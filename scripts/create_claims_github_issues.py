#!/usr/bin/env python3
"""Create and verify GitHub work-item issues from docs/technical_claims_foundations.xlsx."""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
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
LEDGER_PATH = Path(
    "/home/tryggth2009/.gemini/antigravity-cli/brain/"
    "9e153dcc-5e91-41c1-8d51-49c3028223d5/scratch/created_github_issues.json"
)
REPO = "tryggth/categorical-reverse-mathematics"
SPREADSHEET_NS = {"m": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
MARKER_RE = re.compile(r"<!--\s*crm-claim-id:\s*([^\s>]+)\s*-->")


def resolve_head_sha() -> str:
    """Resolve current git HEAD SHA for pinning newly minted issues."""
    proc = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    sha = proc.stdout.strip()
    return sha if len(sha) == 40 else "d3a6e61a94df1454304cc1d5ffd26dabd43985e6"


def resolve_manuscript_links(line_spec: str, commit_sha: str) -> tuple[str, str, str]:
    """Resolve `<line>` or `ch07:<line>` into `(display_ref, blob_url, main_url)`."""
    s = line_spec.strip()
    if s.startswith("ch07:"):
        rel_path = "docs/ch07_sets_residuum.tex"
        line_num = s.split(":", 1)[1].strip()
    else:
        rel_path = "docs/categorical_reverse_mathematics.tex"
        line_num = s
    disp = f"{rel_path}#L{line_num}"
    blob_url = f"https://github.com/{REPO}/blob/{commit_sha}/{disp}"
    main_url = f"https://github.com/{REPO}/blob/main/{disp}"
    return disp, blob_url, main_url


@dataclass(frozen=True)
class GroundingSpec:
    """Configuration mapping a Foundational Grounding category to GitHub metadata."""

    label: str
    color: str
    label_description: str
    title_prefix: str
    summary_banner: str
    checklist: str


GROUNDING_SPECS: dict[str, GroundingSpec] = {
    "English language proof in monograph": GroundingSpec(
        label="grounding: lean-proof-needed",
        color="1d76db",
        label_description="English language proof in monograph — needs Lean 4 mechanization",
        title_prefix="[Lean Proof]",
        summary_banner=(
            "This claim is currently established by an **English-language proof in the monograph** "
            "and requires a formal **Lean 4 proof** (`leanprover/lean4:v4.28.0`) satisfying all "
            "4 layers of the project's Lean Definition Check Gate."
        ),
        checklist=(
            "### Action Checklist — Lean 4 Mechanization Needed\n"
            "- [ ] Design faithful Lean 4 definitions/statement in `HomotopyCRM/<Module>.lean` "
            "(`leanprover/lean4:v4.28.0`) matching the monograph claim at `{disp_ref}`.\n"
            "- [ ] Complete kernel-verified proof (`0 sorry`, `0` custom `axiom`, `0 opaque`).\n"
            "- [ ] Add `namespace Checks` satisfying the 4-Layer Lean 4 Definition Check Gate "
            "(Carrier Inhabitation, Bidirectional Separation, `mathlib4` Projections & Derived Sanity, "
            "`#guard_msgs in #print axioms`).\n"
            "- [ ] Link via `\\lean{{...}}` in `{tex_file}` and update "
            "`Foundational Grounding` to `Proved by Lean code` in `docs/technical_claims_foundations.{{md,xlsx}}`."
        ),
    ),
    "External theorem": GroundingSpec(
        label="grounding: verify-first-citation",
        color="0e8a16",
        label_description="External theorem — confirm citation on first mention in monograph text",
        title_prefix="[Verify Citation]",
        summary_banner=(
            "This claim relies on an **external theorem** in the literature. We must confirm that "
            "the monograph text includes an explicit, accurate citation at the **first instance** "
            "where the theorem or result is referenced."
        ),
        checklist=(
            "### Action Checklist — First-Mention Citation Verification\n"
            "- [ ] Search `docs/categorical_reverse_mathematics.tex` and `docs/ch07_sets_residuum.tex` "
            "(including Preface, Glossary, chapter openings, summary tables, and `{disp_ref}`) to identify "
            "the **very first instance** where this theorem/result is referenced in the monograph text.\n"
            "- [ ] Confirm that the **first instance** carries an explicit, on-the-nose `\\cite{{...}}` "
            "citation (with theorem/section/page pinpoint where appropriate), rather than deferring the "
            "citation only to a later occurrence.\n"
            "- [ ] If missing or imprecise at first mention, add/refine `\\cite{{...}}` in `{tex_file}` "
            "and verify clean build via `python3 scripts/verify_monograph.py --tex-only`."
        ),
    ),
    "Open problem": GroundingSpec(
        label="grounding: future-research",
        color="5319e7",
        label_description="Open problem — future research direction",
        title_prefix="[Research Direction]",
        summary_banner=(
            "This entry tracks an explicit **open problem** representing a **future research "
            "direction** extending *Categorical Reverse Mathematics*."
        ),
        checklist=(
            "### Action Checklist — Future Research Direction\n"
            "- [ ] Formulate precise target theorems, candidate Doctrinal Comparison Triples "
            "$\\mathfrak{{T}} = (\\mathcal{{D}}_0 \\supseteq \\mathcal{{D}}_1, \\kappa)$, and test "
            "countermodels building on the Chapter 8 Horizon statement at `{disp_ref}`.\n"
            "- [ ] Map dependencies against existing CRM results and external literature noted in "
            "Grounding Evidence above.\n"
            "- [ ] Prototype tractable special cases / toy witnesses (in prose or Lean 4) and document "
            "progress or spinout milestones (cf. `docs/11_FUTURE_VISTAS_AND_SPINOUTS.md`)."
        ),
    ),
    "Unfounded": GroundingSpec(
        label="grounding: unfounded-needs-analysis",
        color="d93f0b",
        label_description="Unfounded claim — needs deeper analysis and plan of action",
        title_prefix="[Analysis & Action Plan]",
        summary_banner=(
            "This claim is currently marked **Unfounded** (either an open conjecture or an "
            "ungrounded/under-justified assertion) and requires **deeper mathematical analysis** "
            "together with a concrete **plan of action** before acceptance."
        ),
        checklist=(
            "### Action Checklist — Deeper Mathematical Analysis & Plan of Action Needed\n"
            "- [ ] Conduct a deep mathematical audit of the claim/conjecture at `{disp_ref}` and every "
            "prose/table cross-reference identified in Grounding Evidence above.\n"
            "- [ ] Establish and record a concrete **Plan of Action** selecting the appropriate "
            "resolution path:\n"
            "  - *(a)* Prove rigorously in monograph prose and/or Lean 4; **or**\n"
            "  - *(b)* Locate and cite a precise external theorem if already proved in the literature; **or**\n"
            "  - *(c)* Narrow/rectify hypotheses if an obstruction or countermodel applies; **or**\n"
            "  - *(d)* Explicitly frame and label as an open conjecture / heuristic specification "
            "everywhere it appears (including summary tables) so no unproved assertion reads as established fact.\n"
            "- [ ] Execute the chosen resolution in `{tex_file}`, verify via "
            "`python3 scripts/verify_monograph.py --tex-only`, and update "
            "`docs/technical_claims_foundations.{{md,xlsx}}`."
        ),
    ),
}

PART_LABELS: dict[str, tuple[str, str, str]] = {
    "Part I": (
        "part: I-formal-result",
        "bfd4f2",
        "Part I: Formal theorem, proposition, conjecture, or principle",
    ),
    "Part II": (
        "part: II-def-rem-prob",
        "d4c5f9",
        "Part II: Formal definition, remark, or open problem",
    ),
    "Part III": (
        "part: III-inline-claim",
        "c2e0c6",
        "Part III: Atomic inline prose or summary-table claim",
    ),
}

AXIS_LABELS: dict[str, tuple[str, str, str]] = {
    "Axis I": ("axis: I-choice", "f9d0c4", "Axis I: Choice / Splitting"),
    "Axis II": (
        "axis: II-logic",
        "fef2c0",
        "Axis II: Constructive Logic / Booleanness",
    ),
    "Axis III": ("axis: III-infinity", "bfdadc", "Axis III: Arithmetic Infinity / NNO"),
    "Axis IV": (
        "axis: IV-torsion-geometry",
        "e99695",
        "Axis IV: Characteristic / p-Torsion / Geometry",
    ),
    "Axis V": (
        "axis: V-directed-higher-cat",
        "c5def5",
        "Axis V: Directional Invertibility / Higher Category Theory",
    ),
    "Axis VI": (
        "axis: VI-replacement-descent",
        "bde0fe",
        "Axis VI: Quotient-Image Descent / Replacement",
    ),
    "Axis VII": (
        "axis: VII-foundation-truncation",
        "e2c6ff",
        "Axis VII: Foundation vs. Anti-Foundation / Structural Truncation",
    ),
    "Cross-Axis": ("axis: cross-axis", "ededed", "Cross-Axis / Metamathematical"),
}


@dataclass(frozen=True)
class ClaimWorkItem:
    """Normalized work item extracted from Sheet 1 of the claims workbook."""

    excel_row: int
    part: str
    evaluated_claim: str
    claim_id: str
    claim_type: str
    line: str
    claim_title: str
    axis: str
    foundational_grounding: str
    evidence: str
    characterization: str
    title: str
    body: str
    labels: list[str]


def md_table_escape(value: str) -> str:
    """Escape pipe characters so text renders cleanly inside a Markdown table cell."""
    return value.replace("|", "\\|")


def read_master_rows(xlsx_path: Path) -> list[tuple[int, dict[str, str]]]:
    """Read all data rows from Sheet 1 (`Master All Claims (208)`) with Excel row indices."""
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
                val = v_el.text if v_el is not None and v_el.text is not None else ""
            values.append(val)
        parsed_rows.append((excel_row, values))

    headers = parsed_rows[0][1]
    return [
        (excel_row, dict(zip(headers, row_vals)))
        for excel_row, row_vals in parsed_rows[1:]
    ]


def build_work_item(
    excel_row: int,
    row: dict[str, str],
    total_master_rows: int,
    commit_sha: str,
) -> ClaimWorkItem:
    """Build GitHub issue title, Markdown body, and labels for one catalog row."""
    grounding = row["Foundational Grounding"]
    spec = GROUNDING_SPECS[grounding]
    part = row["Part"]
    axis = row["Axis"]
    claim_id = row["ID / Label"]
    claim_title = row["Claim Title"]
    line = row["Line"]

    raw_title = f"{spec.title_prefix} [{claim_id}] {claim_title}"
    title = raw_title if len(raw_title) <= 250 else raw_title[:247] + "..."

    part_label = PART_LABELS[part][0]
    axis_label = AXIS_LABELS[axis][0]
    labels = [spec.label, part_label, axis_label]

    disp_ref, tex_blob, tex_main = resolve_manuscript_links(line, commit_sha)
    tex_file = disp_ref.split("#", 1)[0]

    body = "\n".join(
        [
            f"<!-- crm-claim-id: {claim_id} -->",
            spec.summary_banner,
            "",
            "### Catalog Metadata",
            "| Field | Value |",
            "| :--- | :--- |",
            f"| **Claim ID / Label** | `{claim_id}` |",
            f"| **Spreadsheet Location** | `docs/technical_claims_foundations.xlsx` → `Master All Claims ({total_master_rows})`, Excel Row {excel_row} |",
            f"| **Part & Environment Type** | {md_table_escape(part)} · {md_table_escape(row['Type'])} (`Evaluated Claim?`: {md_table_escape(row['Evaluated Claim?'])}) |",
            f"| **Coordinate Axis** | {md_table_escape(axis)} |",
            f"| **Foundational Grounding** | `{grounding}` |",
            f"| **Characterization Types** | {md_table_escape(row['Characterization Types'])} |",
            f"| **Manuscript Location** | [`{disp_ref}`]({tex_blob}) ([`main`]({tex_main})) |",
            "",
            "### Cataloged Grounding Evidence / Context",
            f"> {row['Grounding Evidence / Location']}",
            "",
            spec.checklist.format(disp_ref=disp_ref, tex_file=tex_file),
        ]
    )

    return ClaimWorkItem(
        excel_row=excel_row,
        part=part,
        evaluated_claim=row["Evaluated Claim?"],
        claim_id=claim_id,
        claim_type=row["Type"],
        line=line,
        claim_title=claim_title,
        axis=axis,
        foundational_grounding=grounding,
        evidence=row["Grounding Evidence / Location"],
        characterization=row["Characterization Types"],
        title=title,
        body=body,
        labels=labels,
    )


def load_target_items(xlsx_path: Path, commit_sha: str | None = None) -> list[ClaimWorkItem]:
    """Load, validate, and build all target issue work items from Sheet 1."""
    sha = commit_sha or resolve_head_sha()
    all_rows = read_master_rows(xlsx_path)
    total_master_rows = len(all_rows)
    items = [
        build_work_item(excel_row, row, total_master_rows=total_master_rows, commit_sha=sha)
        for excel_row, row in all_rows
        if row["Foundational Grounding"] in GROUNDING_SPECS
    ]

    ids = [item.claim_id for item in items]
    if len(ids) != len(set(ids)):
        raise AssertionError("Duplicate Claim ID / Label found in target rows.")

    for item in items:
        if len(item.title) > 256:
            raise AssertionError(f"Issue title exceeds 256 chars for {item.claim_id}")

    return items


def run_gh_with_retry(
    args: list[str],
    stdin_text: str | None = None,
    max_attempts: int = 5,
) -> subprocess.CompletedProcess[str]:
    """Run a `gh` command with retry/backoff for GitHub secondary rate limits and 5xx errors."""
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
            tok in combined for tok in ("http 500", "http 502", "http 503", "http 504", "timeout", "eof")
        )
        if attempt < max_attempts and (is_rate_limit or is_transient):
            wait_s = 65 if is_rate_limit else 5 * attempt
            print(
                f"  [retry {attempt}/{max_attempts}] sleeping {wait_s}s after error: "
                f"{proc.stderr.strip()[:160]}",
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


def ensure_labels(dry_run: bool = False) -> None:
    """Create or update all 13 workflow/part/axis labels in the repository."""
    all_labels: list[tuple[str, str, str]] = [
        (spec.label, spec.color, spec.label_description)
        for spec in GROUNDING_SPECS.values()
    ]
    all_labels.extend(PART_LABELS.values())
    all_labels.extend(AXIS_LABELS.values())

    for name, color, desc in all_labels:
        if dry_run:
            continue
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


def fetch_all_issues(state: str = "all") -> list[dict]:
    """Fetch paginated GitHub issues (excluding pull requests) for the repository."""
    issues: list[dict] = []
    page = 1
    while True:
        proc = run_gh_with_retry(
            ["api", f"repos/{REPO}/issues?state={state}&per_page=100&page={page}"]
        )
        batch = json.loads(proc.stdout)
        if not batch:
            break
        issues.extend(item for item in batch if "pull_request" not in item)
        if len(batch) < 100:
            break
        page += 1
    return issues


def extract_claim_id(issue: dict) -> str | None:
    """Extract embedded `<!-- crm-claim-id: ... -->` marker from an issue body."""
    body = issue.get("body") or ""
    match = MARKER_RE.search(body)
    return match.group(1) if match else None


def cmd_dry_run(items: list[ClaimWorkItem]) -> int:
    """Validate counts and print category breakdown + sample rendered issues."""
    counts = Counter(item.foundational_grounding for item in items)
    print(f"Dry-run OK: {len(items)} target work items loaded from {XLSX_PATH.name}")
    for grounding, spec in GROUNDING_SPECS.items():
        print(f"  {grounding} ({spec.label}): {counts[grounding]}")

    seen: set[str] = set()
    for item in items:
        if item.foundational_grounding in seen:
            continue
        seen.add(item.foundational_grounding)
        print("\n--- Sample:", item.foundational_grounding, "---")
        print("Title :", item.title)
        print("Labels:", item.labels)
        print("Body preview (first 8 lines):")
        for line in item.body.splitlines()[:8]:
            print(" ", line)
    return 0


def cmd_apply(items: list[ClaimWorkItem], delay_seconds: float) -> int:
    """Idempotently ensure labels and create missing GitHub issues for all 142 items."""
    print(f"Ensuring 15 labels on {REPO}...", flush=True)
    ensure_labels(dry_run=False)

    existing_issues = fetch_all_issues(state="all")
    existing_by_id: dict[str, dict] = {}
    for issue in existing_issues:
        cid = extract_claim_id(issue)
        if cid:
            existing_by_id[cid] = issue
    print(
        f"Found {len(existing_issues)} existing issues ({len(existing_by_id)} tagged with crm-claim-id).",
        flush=True,
    )

    ledger: list[dict] = []
    created_now = 0
    skipped = 0

    for idx, item in enumerate(items, start=1):
        if item.claim_id in existing_by_id:
            prev = existing_by_id[item.claim_id]
            skipped += 1
            ledger.append(
                {
                    "claim_id": item.claim_id,
                    "grounding": item.foundational_grounding,
                    "number": prev["number"],
                    "url": prev["html_url"],
                    "title": prev["title"],
                    "status": "existing",
                }
            )
            continue

        payload = json.dumps(
            {
                "title": item.title,
                "body": item.body,
                "labels": item.labels,
            }
        )
        proc = run_gh_with_retry(
            ["api", f"repos/{REPO}/issues", "--method", "POST", "--input", "-"],
            stdin_text=payload,
        )
        resp = json.loads(proc.stdout)
        created_now += 1
        ledger.append(
            {
                "claim_id": item.claim_id,
                "grounding": item.foundational_grounding,
                "number": resp["number"],
                "url": resp["html_url"],
                "title": resp["title"],
                "status": "created",
            }
        )
        if created_now % 10 == 0 or idx == len(items):
            print(
                f"Progress: {idx}/{len(items)} processed "
                f"(created={created_now}, skipped={skipped}, last=#{resp['number']} {item.claim_id})",
                flush=True,
            )
        if idx < len(items):
            time.sleep(delay_seconds)

    LEDGER_PATH.parent.mkdir(parents=True, exist_ok=True)
    LEDGER_PATH.write_text(json.dumps(ledger, indent=2), encoding="utf-8")
    print(f"Done: created={created_now}, skipped={skipped}. Ledger written to {LEDGER_PATH}", flush=True)
    return 0


def cmd_verify(items: list[ClaimWorkItem]) -> int:
    """Verify every active target spreadsheet item has a matching GitHub issue (across open/closed + follow-ups)."""
    all_issues = fetch_all_issues(state="all")
    expected_ids = {item.claim_id for item in items}

    id_to_issues: dict[str, list[dict]] = {}
    untagged: list[int] = []

    for issue in all_issues:
        cid = extract_claim_id(issue)
        if cid is None:
            untagged.append(issue["number"])
        else:
            id_to_issues.setdefault(cid, []).append(issue)

    missing = sorted(expected_ids - set(id_to_issues))
    duplicate_open = {
        cid: [i["number"] for i in iss_list if i["state"] == "open"]
        for cid, iss_list in id_to_issues.items()
        if sum(1 for i in iss_list if i["state"] == "open") > 1
    }

    print(f"Total GitHub issues on {REPO}: {len(all_issues)} (untagged={len(untagged)})")
    print(f"Matched target claim IDs: {len(expected_ids - set(missing))}/{len(expected_ids)}")
    print(f"Missing target IDs: {len(missing)}, Duplicate open IDs: {len(duplicate_open)}")

    for grounding, spec in GROUNDING_SPECS.items():
        matched_nums = sorted(
            id_to_issues[it.claim_id][-1]["number"]
            for it in items
            if it.foundational_grounding == grounding and it.claim_id in id_to_issues
        )
        lo_hi = f"#{matched_nums[0]}..#{matched_nums[-1]}" if matched_nums else "none"
        print(f"  {grounding} ({spec.label}): matched={len(matched_nums)}, range={lo_hi}")

    assert not untagged, f"Found untagged issues: {untagged}"
    assert not duplicate_open, f"Found duplicate open claim IDs: {duplicate_open}"
    assert not missing, f"Missing claim IDs: {missing}"
    print(f"VERIFICATION PASSED: all {len(expected_ids)} target claims tracked on GitHub.")
    return 0


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--dry-run", action="store_true", help="Validate counts and preview payloads")
    mode.add_argument("--apply", action="store_true", help="Ensure labels and create GitHub issues")
    mode.add_argument("--verify", action="store_true", help="Verify live GitHub open issues match 1-to-1")
    parser.add_argument("--delay", type=float, default=1.1, help="Seconds to wait between POST requests")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint."""
    args = parse_args(argv)
    items = load_target_items(XLSX_PATH)
    if args.dry_run:
        return cmd_dry_run(items)
    if args.apply:
        return cmd_apply(items, delay_seconds=args.delay)
    return cmd_verify(items)


if __name__ == "__main__":
    sys.exit(main())
