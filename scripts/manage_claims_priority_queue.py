#!/usr/bin/env python3
"""Manage the Rank 1-142 GitHub issue priority queue and review-handoff state."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import xml.etree.ElementTree as ET
import zipfile


ROOT = Path(__file__).resolve().parent.parent
XLSX_PATH = ROOT / "docs" / "technical_claims_foundations.xlsx"
TEX_PATH = ROOT / "docs" / "categorical_reverse_mathematics.tex"
REPO = "tryggth/categorical-reverse-mathematics"
SPREADSHEET_NS = {"m": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
MARKER_RE = re.compile(r"<!--\s*crm-claim-id:\s*([^\s>]+)\s*-->")

READY_LABEL = "status: ready-for-review"

PRIORITY_LABELS: dict[str, tuple[str, str]] = {
    "priority: P0": (
        "b60205",
        "Ranks 1-3: Critical unfounded prose/table assertions stated as fact",
    ),
    "priority: P1": (
        "d93f0b",
        "Ranks 4-13: Stated conjectures & obstruction classes needing audit + action plan",
    ),
    "priority: P2": (
        "fbca04",
        "Ranks 14-94: External theorem first-mention citation verification",
    ),
    "priority: P3": (
        "0052cc",
        "Ranks 95-128: English-language proofs needing Lean 4 mechanization",
    ),
    "priority: P4": (
        "6f42c1",
        "Ranks 129-142: Standing Ch. 7 open problems (manual selection only)",
    ),
}

STATUS_LABELS: dict[str, tuple[str, str]] = {
    READY_LABEL: (
        "2da44e",
        "Resolved and verified; awaiting author review and manual close",
    ),
}

# Explicit deterministic issue-number ordering within non-line-sorted tiers.
P0_ISSUES = [90, 87, 92]
P1_ISSUES = [8, 56, 57, 58, 6, 7, 10, 17, 141, 140]
P2A_ISSUES = [2, 4, 12, 20]
P3A_ISSUES = [78, 136, 37, 49, 50, 48, 47, 5, 3, 79, 13, 1]
P3B_ISSUES = [14, 60, 15, 9, 16, 18, 19, 106, 11, 53, 80]
P3C_ISSUES = [21, 22, 43, 40, 41, 138, 42, 139, 137, 98, 142]
P4_ISSUES = [29, 33, 28, 34, 24, 35, 23, 25, 26, 27, 30, 31, 32, 36]

# Locked baseline snapshot of the 26 P2b issues (missing nearby \cite at creation commit d3a6e61)
# and 51 P2c issues so ranks 1..142 remain invariant even as .tex lines are edited over time.
P2B_ISSUES = [
    38, 44, 45, 46, 51, 54, 72, 77, 91, 94, 95, 102, 111, 117,
    120, 121, 122, 123, 124, 125, 128, 129, 130, 131, 132, 133,
]
P2C_ISSUES = [
    39, 52, 55, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 74,
    75, 76, 81, 82, 83, 84, 85, 86, 88, 89, 93, 96, 97, 99, 100, 101, 103,
    104, 105, 107, 108, 109, 110, 112, 113, 114, 115, 116, 118, 119, 126,
    127, 134, 135,
]

TIER_DEFINITIONS: list[tuple[str, str, list[int]]] = [
    ("P0", "priority: P0", P0_ISSUES),
    ("P1", "priority: P1", P1_ISSUES),
    ("P2a", "priority: P2", P2A_ISSUES),
    ("P2b", "priority: P2", P2B_ISSUES),
    ("P2c", "priority: P2", P2C_ISSUES),
    ("P3a", "priority: P3", P3A_ISSUES),
    ("P3b", "priority: P3", P3B_ISSUES),
    ("P3c", "priority: P3", P3C_ISSUES),
    ("P4", "priority: P4", P4_ISSUES),
]


def build_rank_map() -> list[dict]:
    """Return the invariant Rank 1..142 table mapping issue numbers to tiers and labels."""
    entries: list[dict] = []
    for subtier, prio_label, nums in TIER_DEFINITIONS:
        for num in nums:
            entries.append(
                {
                    "rank": len(entries) + 1,
                    "number": num,
                    "subtier": subtier,
                    "priority_label": prio_label,
                    "auto_eligible": subtier != "P4",
                }
            )
    got = [e["number"] for e in entries]
    if len(got) != 142 or set(got) != set(range(1, 143)):
        raise AssertionError("TIER_DEFINITIONS must form a bijection onto issues #1..#142.")
    return entries


def run_gh_with_retry(
    args: list[str],
    stdin_text: str | None = None,
    max_attempts: int = 5,
) -> subprocess.CompletedProcess[str]:
    """Execute a `gh` command with retry/backoff for secondary rate limits and 5xx errors."""
    last_proc: subprocess.CompletedProcess[str] | None = None
    for attempt in range(1, max_attempts + 1):
        proc = subprocess.run(
            ["gh", *args],
            input=stdin_text,
            capture_output=True,
            text=True,
        )
        if proc.returncode == 0:
            return proc
        last_proc = proc
        combined = f"{proc.stdout}\n{proc.stderr}".lower()
        is_rate_limit = any(
            tok in combined
            for tok in ("secondary rate limit", "submitted too quickly", "429", "rate limit")
        )
        is_transient = any(
            tok in combined
            for tok in ("http 500", "http 502", "http 503", "http 504", "timeout", "eof")
        )
        if attempt < max_attempts and (is_rate_limit or is_transient):
            wait_s = 65 if is_rate_limit else 5 * attempt
            print(
                f"  [retry {attempt}/{max_attempts}] sleeping {wait_s}s: {proc.stderr.strip()[:140]}",
                file=sys.stderr,
                flush=True,
            )
            time.sleep(wait_s)
            continue
        break

    assert last_proc is not None
    raise RuntimeError(
        f"gh {' '.join(args)} failed (exit {last_proc.returncode}): "
        f"{last_proc.stderr.strip() or last_proc.stdout.strip()}"
    )


def fetch_all_issues(state: str = "all") -> dict[int, dict]:
    """Fetch paginated repository issues keyed by issue number (excluding PRs)."""
    by_num: dict[int, dict] = {}
    page = 1
    while True:
        proc = run_gh_with_retry(
            ["api", f"repos/{REPO}/issues?state={state}&per_page=100&page={page}"]
        )
        batch = json.loads(proc.stdout)
        if not batch:
            break
        for item in batch:
            if "pull_request" not in item:
                by_num[item["number"]] = item
        if len(batch) < 100:
            break
        page += 1
    return by_num


def ensure_priority_and_status_labels() -> None:
    """Idempotently create/update `priority: P0..P4` and `status: ready-for-review`."""
    combined = {**PRIORITY_LABELS, **STATUS_LABELS}
    for name, (color, desc) in combined.items():
        run_gh_with_retry(
            [
                "label",
                "create",
                name,
                "--repo",
                REPO,
                "--color",
                color,
                "--description",
                desc,
                "--force",
            ]
        )


def cmd_sync_labels(delay_seconds: float) -> int:
    """Apply `priority: P0..P4` labels across all 142 issues idempotently."""
    rank_entries = build_rank_map()
    print(f"Ensuring priority & status labels on {REPO}...", flush=True)
    ensure_priority_and_status_labels()

    issues_by_num = fetch_all_issues(state="all")
    updated = 0
    already_labeled = 0

    for idx, entry in enumerate(rank_entries, start=1):
        num = entry["number"]
        prio_label = entry["priority_label"]
        issue = issues_by_num[num]
        current_labels = {lbl["name"] for lbl in issue.get("labels", [])}
        if prio_label in current_labels:
            already_labeled += 1
            continue

        payload = json.dumps({"labels": [prio_label]})
        run_gh_with_retry(
            ["api", f"repos/{REPO}/issues/{num}/labels", "--method", "POST", "--input", "-"],
            stdin_text=payload,
        )
        updated += 1
        if updated % 20 == 0 or idx == len(rank_entries):
            print(
                f"Progress: {idx}/{len(rank_entries)} checked "
                f"(labeled={updated}, skipped={already_labeled}, last=#{num} -> {prio_label})",
                flush=True,
            )
        if idx < len(rank_entries):
            time.sleep(delay_seconds)

    print(
        f"Sync complete: newly_labeled={updated}, already_labeled={already_labeled}.",
        flush=True,
    )
    return 0


def cmd_status() -> int:
    """Print live queue status across P0..P4 (open actionable, ready-for-review, closed)."""
    rank_entries = build_rank_map()
    issues_by_num = fetch_all_issues(state="all")

    tier_stats: dict[str, Counter[str]] = {}
    label_counts: Counter[str] = Counter()

    for entry in rank_entries:
        num = entry["number"]
        prio = entry["priority_label"]
        issue = issues_by_num[num]
        labels = {lbl["name"] for lbl in issue.get("labels", [])}
        for lbl in labels:
            if lbl.startswith("priority:") or lbl == READY_LABEL:
                label_counts[lbl] += 1

        stats = tier_stats.setdefault(prio, Counter())
        stats["total"] += 1
        if issue["state"] == "closed":
            stats["closed"] += 1
        elif READY_LABEL in labels:
            stats["ready_for_review"] += 1
        else:
            stats["actionable_open"] += 1
        if prio not in labels:
            stats["missing_prio_label"] += 1

    print(f"=== Priority Queue Live Status ({REPO}) ===")
    for prio in PRIORITY_LABELS:
        st = tier_stats[prio]
        note = " [skipped in auto-queue]" if prio == "priority: P4" else ""
        print(
            f"  {prio:12s}: total={st['total']:3d} | actionable={st['actionable_open']:3d} | "
            f"ready_for_review={st['ready_for_review']:3d} | closed={st['closed']:3d} | "
            f"missing_label={st['missing_prio_label']}{note}"
        )
        assert st["missing_prio_label"] == 0, f"Missing {prio} on {st['missing_prio_label']} issues!"
    return 0


def cmd_next(include_p4: bool = False) -> int:
    """Print the single highest-priority open issue not yet marked ready-for-review."""
    rank_entries = build_rank_map()
    open_issues = fetch_all_issues(state="open")

    for entry in rank_entries:
        if not include_p4 and not entry["auto_eligible"]:
            continue
        num = entry["number"]
        issue = open_issues.get(num)
        if issue is None:
            continue
        labels = {lbl["name"] for lbl in issue.get("labels", [])}
        if READY_LABEL in labels:
            continue

        body = issue.get("body") or ""
        m = MARKER_RE.search(body)
        claim_id = m.group(1) if m else ""
        out = {
            "rank": entry["rank"],
            "subtier": entry["subtier"],
            "priority_label": entry["priority_label"],
            "number": num,
            "claim_id": claim_id,
            "title": issue["title"],
            "url": issue["html_url"],
            "labels": sorted(labels),
        }
        print(json.dumps(out, indent=2))
        return 0

    print("No actionable open tickets remaining in queue.")
    return 0


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--sync-labels", action="store_true", help="Create & apply priority/status labels")
    mode.add_argument("--status", action="store_true", help="Verify and print live queue summary")
    mode.add_argument("--next", action="store_true", help="Show next actionable ticket for 'Close a ticket'")
    parser.add_argument("--include-p4", action="store_true", help="Include P4 Open Problems in --next")
    parser.add_argument("--delay", type=float, default=0.6, help="Seconds between label POST requests")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint."""
    args = parse_args(argv)
    if args.sync_labels:
        return cmd_sync_labels(delay_seconds=args.delay)
    if args.status:
        return cmd_status()
    return cmd_next(include_p4=args.include_p4)


if __name__ == "__main__":
    sys.exit(main())
