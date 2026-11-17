#!/usr/bin/env python3
"""Manage the GitHub issue priority queue, 'Reviewed' handoffs, and follow-up Lean tickets."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.parse
import xml.etree.ElementTree as ET
import zipfile


ROOT = Path(__file__).resolve().parent.parent
XLSX_PATH = ROOT / "docs" / "technical_claims_foundations.xlsx"
REPO = "tryggth/categorical-reverse-mathematics"
SPREADSHEET_NS = {"m": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
MARKER_RE = re.compile(r"<!--\s*crm-claim-id:\s*([^\s>]+)\s*-->")
COMMIT_LINK_RE = re.compile(
    r"https://github\.com/tryggth/categorical-reverse-mathematics/commit/([0-9a-f]{7,40})"
)
REVIEWED_COMMENT_RE = re.compile(r"^\s*reviewed\b", re.IGNORECASE)

READY_LABEL = "status: ready-for-review"

PRIORITY_LABELS: dict[str, tuple[str, str]] = {
    "priority: P0": (
        "b60205",
        "Critical unfounded prose/table assertions stated as fact",
    ),
    "priority: P1": (
        "d93f0b",
        "Stated conjectures & obstruction classes needing audit + action plan",
    ),
    "priority: P2": (
        "fbca04",
        "External theorem first-mention citation verification",
    ),
    "priority: P3": (
        "0052cc",
        "English-language proofs needing Lean 4 mechanization",
    ),
    "priority: P4": (
        "6f42c1",
        "Standing Ch. 7 open problems (manual selection only)",
    ),
}

STATUS_LABELS: dict[str, tuple[str, str]] = {
    READY_LABEL: (
        "2da44e",
        "Resolved and verified; awaiting author review ('Reviewed' comment)",
    ),
}

PART_LABELS: dict[str, str] = {
    "Part I": "part: I-formal-result",
    "Part II": "part: II-def-rem-prob",
    "Part III": "part: III-inline-claim",
}

AXIS_LABELS: dict[str, str] = {
    "Axis I": "axis: I-choice",
    "Axis II": "axis: II-logic",
    "Axis III": "axis: III-infinity",
    "Axis IV": "axis: IV-torsion-geometry",
    "Axis V": "axis: V-directed-higher-cat",
    "Cross-Axis": "axis: cross-axis",
}

P0_ISSUES = [90, 87, 92]
P1_ISSUES = [8, 56, 57, 58, 6, 7, 10, 17, 141, 140]
P2A_ISSUES = [2, 4, 12, 20]
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
P3A_ISSUES = [78, 136, 37, 49, 50, 48, 47, 5, 3, 79, 13, 1]
P3B_ISSUES = [14, 60, 15, 9, 16, 18, 19, 106, 11, 53, 80]
P3C_ISSUES = [21, 22, 43, 40, 41, 138, 42, 139, 137, 98, 142]
P4_ISSUES = [29, 33, 28, 34, 24, 35, 23, 25, 26, 27, 30, 31, 32, 36]

BASE_TIER_DEFINITIONS: list[tuple[str, str, list[int]]] = [
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


def md_table_escape(value: str) -> str:
    """Escape pipe characters inside Markdown table cells."""
    return value.replace("|", "\\|")


def read_master_rows_by_id(xlsx_path: Path) -> dict[str, tuple[int, dict[str, str]]]:
    """Read Sheet 1 (`Master All Claims (208)`) keyed by `ID / Label`."""
    with zipfile.ZipFile(xlsx_path, "r") as zf:
        ws = ET.fromstring(zf.read("xl/worksheets/sheet1.xml"))

    parsed_rows: list[tuple[int, list[str]]] = []
    for row_el in ws.findall(".//m:sheetData/m:row", SPREADSHEET_NS):
        excel_row = int(row_el.attrib["r"])
        values: list[str] = []
        for cell_el in row_el.findall("m:c", SPREADSHEET_NS):
            if cell_el.attrib.get("t") == "inlineStr":
                t_el = cell_el.find("m:is/m:t", SPREADSHEET_NS)
                val = t_el.text if t_el is not None and t_el.text is not None else ""
            else:
                v_el = cell_el.find("m:v", SPREADSHEET_NS)
                val = v_el.text if v_el.text is not None else ""
            values.append(val)
        parsed_rows.append((excel_row, values))

    headers = parsed_rows[0][1]
    out: dict[str, tuple[int, dict[str, str]]] = {}
    for excel_row, vals in parsed_rows[1:]:
        row_dict = dict(zip(headers, vals))
        out[row_dict["ID / Label"]] = (excel_row, row_dict)
    return out


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


def extract_claim_id(issue: dict) -> str | None:
    """Extract `<!-- crm-claim-id: ... -->` from an issue body."""
    body = issue.get("body") or ""
    m = MARKER_RE.search(body)
    return m.group(1) if m else None


def build_rank_map(issues_by_num: dict[int, dict] | None = None) -> list[dict]:
    """Build deterministic rank table for #1..#142 plus any follow-up tickets (#143+)."""
    base_got = [num for _, _, nums in BASE_TIER_DEFINITIONS for num in nums]
    if len(base_got) != 142 or set(base_got) != set(range(1, 143)):
        raise AssertionError("BASE_TIER_DEFINITIONS must form a bijection onto #1..#142.")

    extra_by_prio: dict[str, list[int]] = {p: [] for p in PRIORITY_LABELS}
    p3a_after_5: list[int] = []
    p3b_after_60: list[int] = []
    p3b_after_18: list[int] = []
    p3b_after_53: list[int] = []

    if issues_by_num:
        for num in sorted(issues_by_num):
            if num <= 142:
                continue
            issue = issues_by_num[num]
            cid = extract_claim_id(issue) or ""
            labels = {lbl["name"] for lbl in issue.get("labels", [])}
            prio = next((p for p in PRIORITY_LABELS if p in labels), "priority: P3")
            if cid in ("prose:ch4-coshep-to-iac-absoluteness", "prose:ch2-ga-svc-subquotient-groups") and prio == "priority: P3":
                p3a_after_5.append(num)
            elif cid == "prose:ch5-acn-strict-model-separation" and prio == "priority: P3":
                p3b_after_60.append(num)
            elif cid == "prose:ch2-ga-dc-uncountable-groups" and prio == "priority: P3":
                p3b_after_18.append(num)
            elif cid == "prose:ch2-ga-bpi-noncompact-groups" and prio == "priority: P3":
                p3b_after_53.append(num)
            else:
                extra_by_prio[prio].append(num)

    entries: list[dict] = []
    for subtier, prio_label, nums in BASE_TIER_DEFINITIONS:
        expanded_nums: list[int] = []
        for num in nums:
            expanded_nums.append(num)
            if subtier == "P3a" and num == 5:
                expanded_nums.extend(p3a_after_5)
            elif subtier == "P3b" and num == 60:
                expanded_nums.extend(p3b_after_60)
            elif subtier == "P3b" and num == 18:
                expanded_nums.extend(p3b_after_18)
            elif subtier == "P3b" and num == 53:
                expanded_nums.extend(p3b_after_53)
        if subtier in ("P0", "P1", "P2c", "P3c", "P4"):
            expanded_nums.extend(extra_by_prio[prio_label])
            extra_by_prio[prio_label] = []

        for num in expanded_nums:
            entries.append(
                {
                    "rank": len(entries) + 1,
                    "number": num,
                    "subtier": subtier,
                    "priority_label": prio_label,
                    "auto_eligible": subtier != "P4",
                }
            )
    return entries


def build_lean_followup_payload(
    claim_id: str,
    excel_row: int,
    row: dict[str, str],
    parent_issue: dict,
    commit_sha: str | None,
    reviewed_comment_url: str,
) -> dict:
    """Build a `[Lean Proof]` GitHub issue payload with an explicit back-pointer to `parent_issue`."""
    line = row["Line"]
    part = row["Part"]
    axis = row["Axis"]
    claim_title = row["Claim Title"]
    parent_num = parent_issue["number"]
    parent_url = parent_issue["html_url"]

    raw_title = f"[Lean Proof] [{claim_id}] {claim_title}"
    title = raw_title if len(raw_title) <= 250 else raw_title[:247] + "..."

    commit_ref = (
        f"[`{commit_sha[:7]}`](https://github.com/{REPO}/commit/{commit_sha})"
        if commit_sha
        else "`main`"
    )
    blob_ref = commit_sha if commit_sha else "main"
    tex_blob = (
        f"https://github.com/{REPO}/blob/{blob_ref}"
        f"/docs/categorical_reverse_mathematics.tex#L{line}"
    )
    tex_main = (
        f"https://github.com/{REPO}/blob/main"
        f"/docs/categorical_reverse_mathematics.tex#L{line}"
    )

    body = "\n".join(
        [
            f"<!-- crm-claim-id: {claim_id} -->",
            "This claim is established by an **English-language proof in the monograph** "
            "and requires a formal **Lean 4 proof** (`leanprover/lean4:v4.28.0`) satisfying all "
            "4 layers of the project's Lean Definition Check Gate.",
            "",
            "### Origin & Back-Pointer",
            f"- **Preceding Audit & Rectification Ticket:** #{parent_num} ([link]({parent_url}))",
            f"- **English Proof Commit:** {commit_ref} · **Author Sign-Off:** [`Reviewed`]({reviewed_comment_url})",
            "",
            "### Catalog Metadata",
            "| Field | Value |",
            "| :--- | :--- |",
            f"| **Claim ID / Label** | `{claim_id}` |",
            f"| **Spreadsheet Location** | `docs/technical_claims_foundations.xlsx` → `Master All Claims (208)`, Excel Row {excel_row} |",
            f"| **Part & Environment Type** | {md_table_escape(part)} · {md_table_escape(row['Type'])} (`Evaluated Claim?`: {md_table_escape(row['Evaluated Claim?'])}) |",
            f"| **Coordinate Axis** | {md_table_escape(axis)} |",
            f"| **Foundational Grounding** | `{row['Foundational Grounding']}` |",
            f"| **Characterization Types** | {md_table_escape(row['Characterization Types'])} |",
            f"| **Manuscript Location** | [`docs/categorical_reverse_mathematics.tex#L{line}`]({tex_blob}) ([`main`]({tex_main})) |",
            "",
            "### Cataloged Grounding Evidence / Context",
            f"> {row['Grounding Evidence / Location']}",
            "",
            "### Action Checklist — Lean 4 Mechanization Needed",
            f"- [ ] Design faithful Lean 4 definitions/statement in `HomotopyCRM/<Module>.lean` (`leanprover/lean4:v4.28.0`) matching the monograph claim at `L{line}`.",
            "- [ ] Complete kernel-verified proof (`0 sorry`, `0` custom `axiom`, `0 opaque`).",
            "- [ ] Add `namespace Checks` satisfying the 4-Layer Lean 4 Definition Check Gate (Carrier Inhabitation, Bidirectional Separation, `mathlib4` Projections & Derived Sanity, `#guard_msgs in #print axioms`).",
            "- [ ] Link via `\\lean{...}` in `docs/categorical_reverse_mathematics.tex` and update `Foundational Grounding` to `Proved by Lean code` in `docs/technical_claims_foundations.{md,xlsx}`.",
        ]
    )

    labels = [
        "grounding: lean-proof-needed",
        PART_LABELS[part],
        AXIS_LABELS[axis],
        "priority: P3",
    ]
    return {"title": title, "body": body, "labels": labels}


def find_author_reviewed_comment(comments: list[dict]) -> tuple[dict | None, str | None]:
    """Return `(reviewed_comment, dossier_commit_sha)` if an author `Reviewed` comment follows the latest Dossier."""
    latest_dossier_idx = -1
    commit_sha: str | None = None
    for idx, c in enumerate(comments):
        body = c.get("body") or ""
        if body.lstrip().startswith("## Review Dossier"):
            latest_dossier_idx = idx
            m = COMMIT_LINK_RE.search(body)
            if m:
                commit_sha = m.group(1)

    search_start = latest_dossier_idx + 1 if latest_dossier_idx >= 0 else 0
    for c in comments[search_start:]:
        body = c.get("body") or ""
        if not body.lstrip().startswith("## Review Dossier") and REVIEWED_COMMENT_RE.match(body):
            return c, commit_sha
    return None, commit_sha


def remove_ready_label(issue_num: int) -> None:
    """Remove `status: ready-for-review` from an issue before closing it."""
    encoded = urllib.parse.quote(READY_LABEL, safe="")
    subprocess.run(
        ["gh", "api", f"repos/{REPO}/issues/{issue_num}/labels/{encoded}", "--method", "DELETE"],
        capture_output=True,
        text=True,
    )


def cmd_process_reviewed() -> int:
    """Scan open `status: ready-for-review` issues for `Reviewed` comments, spawn Lean follow-ups if needed, and close."""
    all_issues = fetch_all_issues(state="all")
    rows_by_id = read_master_rows_by_id(XLSX_PATH)

    open_lean_ids: dict[str, int] = {}
    for num, iss in all_issues.items():
        if iss["state"] != "open":
            continue
        labels = {lbl["name"] for lbl in iss.get("labels", [])}
        cid = extract_claim_id(iss)
        if cid and "grounding: lean-proof-needed" in labels:
            open_lean_ids[cid] = num

    ready_open = [
        iss
        for iss in sorted(all_issues.values(), key=lambda x: x["number"])
        if iss["state"] == "open"
        and READY_LABEL in {lbl["name"] for lbl in iss.get("labels", [])}
    ]

    if not ready_open:
        print("No open issues currently carry 'status: ready-for-review'.")
        return 0

    closed_count = 0
    spawned_count = 0
    for iss in ready_open:
        num = iss["number"]
        comments_proc = run_gh_with_retry(["api", f"repos/{REPO}/issues/{num}/comments?per_page=100"])
        comments = json.loads(comments_proc.stdout)
        reviewed_comment, commit_sha = find_author_reviewed_comment(comments)
        if reviewed_comment is None:
            print(f"  Issue #{num}: awaiting 'Reviewed' comment.")
            continue

        cid = extract_claim_id(iss)
        labels = {lbl["name"] for lbl in iss.get("labels", [])}
        rev_url = reviewed_comment["html_url"]
        followup_num: int | None = None
        followup_url: str | None = None

        if (
            cid
            and "grounding: unfounded-needs-analysis" in labels
            and cid in rows_by_id
            and rows_by_id[cid][1]["Foundational Grounding"] == "English language proof in monograph"
        ):
            if cid in open_lean_ids:
                followup_num = open_lean_ids[cid]
                followup_url = f"https://github.com/{REPO}/issues/{followup_num}"
            else:
                excel_row, row_dict = rows_by_id[cid]
                payload = build_lean_followup_payload(
                    claim_id=cid,
                    excel_row=excel_row,
                    row=row_dict,
                    parent_issue=iss,
                    commit_sha=commit_sha,
                    reviewed_comment_url=rev_url,
                )
                create_proc = run_gh_with_retry(
                    ["api", f"repos/{REPO}/issues", "--method", "POST", "--input", "-"],
                    stdin_text=json.dumps(payload),
                )
                created_issue = json.loads(create_proc.stdout)
                followup_num = created_issue["number"]
                followup_url = created_issue["html_url"]
                open_lean_ids[cid] = followup_num
                spawned_count += 1

        if followup_num and followup_url:
            close_msg = (
                f"Author review confirmed ([`Reviewed`]({rev_url})). "
                f"Closing this analysis/rectification ticket as completed; follow-up Lean 4 "
                f"mechanization of the English-language proof is tracked in **#{followup_num}** "
                f"([link]({followup_url}))."
            )
        else:
            close_msg = f"Author review confirmed ([`Reviewed`]({rev_url})). Closing ticket as completed."

        run_gh_with_retry(
            ["api", f"repos/{REPO}/issues/{num}/comments", "--method", "POST", "--input", "-"],
            stdin_text=json.dumps({"body": close_msg}),
        )
        remove_ready_label(num)
        run_gh_with_retry(
            ["api", f"repos/{REPO}/issues/{num}", "--method", "PATCH", "--input", "-"],
            stdin_text=json.dumps({"state": "closed", "state_reason": "completed"}),
        )
        closed_count += 1
        if followup_num:
            print(f"  Finalized #{num} (closed) -> spawned Lean follow-up #{followup_num} ({followup_url})")
        else:
            print(f"  Finalized #{num} (closed).")

    print(f"Processed reviewed issues: closed={closed_count}, spawned_lean_followups={spawned_count}.")
    return 0


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
    """Apply `priority: P0..P4` labels across all ranked issues idempotently."""
    ensure_priority_and_status_labels()
    issues_by_num = fetch_all_issues(state="all")
    rank_entries = build_rank_map(issues_by_num)
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

        run_gh_with_retry(
            ["api", f"repos/{REPO}/issues/{num}/labels", "--method", "POST", "--input", "-"],
            stdin_text=json.dumps({"labels": [prio_label]}),
        )
        updated += 1
        if idx < len(rank_entries):
            time.sleep(delay_seconds)

    print(f"Sync complete: newly_labeled={updated}, already_labeled={already_labeled}.")
    return 0


def cmd_status() -> int:
    """Print live queue status across P0..P4 (actionable open, ready-for-review, closed)."""
    issues_by_num = fetch_all_issues(state="all")
    rank_entries = build_rank_map(issues_by_num)

    tier_stats: dict[str, Counter[str]] = {}
    for entry in rank_entries:
        num = entry["number"]
        prio = entry["priority_label"]
        issue = issues_by_num[num]
        labels = {lbl["name"] for lbl in issue.get("labels", [])}

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

    print(f"=== Priority Queue Live Status ({REPO}, {len(rank_entries)} tracked issues) ===")
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
    """Process any newly `Reviewed` issues first, then print the next actionable open ticket."""
    cmd_process_reviewed()
    all_issues = fetch_all_issues(state="all")
    rank_entries = build_rank_map(all_issues)

    for entry in rank_entries:
        if not include_p4 and not entry["auto_eligible"]:
            continue
        num = entry["number"]
        issue = all_issues.get(num)
        if issue is None or issue["state"] != "open":
            continue
        labels = {lbl["name"] for lbl in issue.get("labels", [])}
        if READY_LABEL in labels:
            continue

        claim_id = extract_claim_id(issue) or ""
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
    mode.add_argument("--process-reviewed", action="store_true", help="Finalize 'Reviewed' tickets & spawn Lean follow-ups")
    mode.add_argument("--sync-labels", action="store_true", help="Create & apply priority/status labels")
    mode.add_argument("--status", action="store_true", help="Verify and print live queue summary")
    mode.add_argument("--next", action="store_true", help="Process reviewed tickets and show next actionable ticket")
    parser.add_argument("--include-p4", action="store_true", help="Include P4 Open Problems in --next")
    parser.add_argument("--delay", type=float, default=0.6, help="Seconds between label POST requests")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint."""
    args = parse_args(argv)
    if args.process_reviewed:
        return cmd_process_reviewed()
    if args.sync_labels:
        return cmd_sync_labels(delay_seconds=args.delay)
    if args.status:
        return cmd_status()
    return cmd_next(include_p4=args.include_p4)


if __name__ == "__main__":
    sys.exit(main())
