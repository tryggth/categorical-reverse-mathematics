#!/usr/bin/env python3
"""
scripts/verify_technical_claims.py

Deterministic Second-Pass verifier for monograph technical claims and foundational grounding.
Audits docs/categorical_reverse_mathematics.tex, references.bib, blueprint/lean_decls,
and HomotopyCRM/*.lean against docs/technical_claims_foundations.md, enforcing:
1. 100% 1-to-1 bijection across all 88 formal post-document environments (51 results + 37 structural/open).
2. All 174+ distinct inline prose & table technical claims across Preface, Glossary, and Chapters 1-9.
3. All 12 manuscript xltabular/tabularx tables mapped to valid catalog claim IDs in Part IV.
4. Canonical grounding categories, valid coordinate axes, non-empty fields, zero placeholders,
   and Summary Ledger (§7) arithmetic consistency.
5. 100% coverage of blueprint/lean_decls (132 declarations), namespace-aware Lean declaration verification across HomotopyCRM/*.lean,
   and 100% valid literature citation keys against references.bib with anti-hallucination guards.
"""

import argparse
import json
import pathlib
import re
import sys
from collections import Counter
from typing import Any, Dict, List, Set, Tuple

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"
TEX_PATH = DOCS / "categorical_reverse_mathematics.tex"
MD_PATH = DOCS / "technical_claims_foundations.md"
BIB_PATH = ROOT / "references.bib"
BLUEPRINT_DECLS_PATH = ROOT / "blueprint" / "lean_decls"
LEAN_DIR = ROOT / "HomotopyCRM"

RESULT_ENVS = {"theorem", "proposition", "conjecture", "principle", "lemma", "corollary"}
STRUCTURAL_ENVS = {"definition", "remark", "problem"}
ALL_ENVS = RESULT_ENVS | STRUCTURAL_ENVS

CANONICAL_RESULT_CATEGORIES = {
    "External theorem",
    "Proved by Lean code",
    "Folklore",
    "English language proof in monograph",
    "Unfounded",
}
DEFINITION_CATEGORIES = {
    "Authorial framework definition",
    "Standard definition (external)",
}
PROBLEM_CATEGORIES = {"Open problem"}

CANONICAL_AXES = {
    "Axis I",
    "Axis II",
    "Axis III",
    "Axis IV",
    "Axis V",
    "Axis VI",
    "Axis VII",
    "Cross-Axis",
}

PLACEHOLDER_STRINGS = [
    "TBD",
    "TODO",
    "???",
    "placeholder",
    "unverified",
    "Check:",
    "check exact",
]

BANNED_CITATIONS = [
    "pp. 1–98",
    "pp. 1-98",
    "pp. 544–554",
    "pp. 544-554",
    "pp. 165–179",
    "pp. 165-179",
    "pp. 100–120",
    "pp. 100-120",
    "pp. 45–90",
    "pp. 45-90",
    "LietzStreicher02",
    "§C3.4",
    "v5, Theorem~3.2.6",
    "v5 Theorem 3.2.6",
    "Lemma~5.57",
    "Lemma 5.57",
    "Theorems~2.20",
    "Theorems 2.20",
    "A2.2.12",
    "A4.6.9",
    "§C2.5",
    "§C3.3",
    "Theorem D3.3.12",
]


def _extract_opt_arg(line: str, pos: int) -> str:
    """Extract brace/bracket-balanced optional [...] argument immediately following \\begin{env}."""
    if pos >= len(line) or line[pos] != "[":
        return ""
    depth_sq = 0
    depth_br = 0
    out: List[str] = []
    for ch in line[pos:]:
        if ch == "{":
            depth_br += 1
        elif ch == "}":
            depth_br = max(0, depth_br - 1)
        elif ch == "[" and depth_br == 0:
            depth_sq += 1
            if depth_sq == 1:
                continue
        elif ch == "]" and depth_br == 0:
            depth_sq -= 1
            if depth_sq == 0:
                return "".join(out).strip()
        out.append(ch)
    return "".join(out).strip()


def normalize_title(t: str) -> str:
    t_clean = t.strip()
    if t_clean.startswith("{") and t_clean.endswith("}"):
        t_clean = t_clean[1:-1].strip()
    t_clean = t_clean.replace("\\_", "_").replace("\\ ", " ").replace("~", " ")
    return re.sub(r"\s+", " ", t_clean).strip()


INPUT_PREFIX_MAP = {
    "ch07_sets_residuum": ("ch07", DOCS / "ch07_sets_residuum.tex"),
    "ch07_sets_residuum.tex": ("ch07", DOCS / "ch07_sets_residuum.tex"),
    "docs/ch07_sets_residuum": ("ch07", DOCS / "ch07_sets_residuum.tex"),
    "docs/ch07_sets_residuum.tex": ("ch07", DOCS / "ch07_sets_residuum.tex"),
}


def parse_locator(loc_str: str) -> Tuple[str, int]:
    """Parse `<line>` -> `('', int)` or `<prefix>:<line>` -> `(prefix, int)`."""
    s = loc_str.strip()
    if ":" in s:
        pfx, num_s = s.split(":", 1)
        return pfx.strip(), int(num_s.strip())
    return "", int(s)


def format_locator(prefix: str, line: int) -> str:
    return f"{prefix}:{line}" if prefix else str(line)


def _parse_single_tex_file(
    tex_file: pathlib.Path,
    prefix: str,
    start_at_begin_doc: bool,
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], Dict[str, int]]:
    """Parse formal environments and tables recursively across \\input modules in document order."""
    lines = tex_file.read_text(encoding="utf-8").splitlines()
    doc_start = (
        next((idx for idx, l in enumerate(lines) if l.strip() == "\\begin{document}"), 0)
        if start_at_begin_doc
        else 0
    )

    env_names = "|".join(sorted(ALL_ENVS))
    env_pat = re.compile(r"\\begin\{(" + env_names + r")\}")
    table_pat = re.compile(r"\\begin\{(xltabular|tabularx)\}")
    cond_input_pat = re.compile(r"\\IfFileExists\{[^}]+\}\{\\input\{([^}]+)\}\}\{\\input\{[^}]+\}\}")
    plain_input_pat = re.compile(r"(?<!%)\\input\{([^}]+)\}")

    envs: List[Dict[str, Any]] = []
    tables: List[Dict[str, Any]] = []
    line_counts: Dict[str, int] = {prefix: len(lines)}

    i = doc_start
    while i < len(lines):
        line_str = lines[i]

        # Follow modular chapter inputs in exact document order
        cm = cond_input_pat.search(line_str)
        im = plain_input_pat.search(line_str) if not cm else None
        target_key = cm.group(1).strip() if cm else (im.group(1).strip() if im else "")
        if target_key and target_key != "glyphtounicode":
            if target_key in INPUT_PREFIX_MAP:
                sub_pfx, sub_path = INPUT_PREFIX_MAP[target_key]
            else:
                rel = target_key if target_key.endswith(".tex") else target_key + ".tex"
                sub_path = (DOCS / rel) if (DOCS / rel).exists() else (ROOT / rel)
                sub_pfx = sub_path.stem.split("_")[0]
            sub_envs, sub_tables, sub_counts = _parse_single_tex_file(
                sub_path, prefix=sub_pfx, start_at_begin_doc=False
            )
            envs.extend(sub_envs)
            tables.extend(sub_tables)
            line_counts.update(sub_counts)
            i += 1
            continue

        m = env_pat.search(line_str)
        if m:
            etype = m.group(1)
            title = _extract_opt_arg(line_str, m.end())
            start_line = i + 1
            end_line = start_line
            end_tag = "\\end{" + etype + "}"
            while end_line - 1 < len(lines) and end_tag not in lines[end_line - 1]:
                end_line += 1
            blob = "\n".join(lines[i:end_line])
            lbl_m = re.search(r"\\label\{([^}]+)\}", blob)
            label = lbl_m.group(1) if lbl_m else ""
            lean_m = re.search(r"\\lean\{([^}]+)\}", blob)
            lean_decls = [d.strip() for d in lean_m.group(1).split(",") if d.strip()] if lean_m else []
            # Record any tables nested inside or skipped? Formal envs never contain xltabular/tabularx,
            # but check lines inside just in case.
            for k in range(i, end_line):
                tm_in = table_pat.search(lines[k])
                if tm_in:
                    tables.append({"prefix": prefix, "line": k + 1, "env": tm_in.group(1)})
            envs.append(
                {
                    "type": etype,
                    "title": title,
                    "prefix": prefix,
                    "line": start_line,
                    "end_line": end_line,
                    "label": label,
                    "lean_decls": lean_decls,
                }
            )
            i = end_line
        else:
            tm = table_pat.search(line_str)
            if tm:
                tables.append({"prefix": prefix, "line": i + 1, "env": tm.group(1)})
            i += 1

    return envs, tables, line_counts


def parse_tex_structure(tex_file: pathlib.Path) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], Dict[str, int]]:
    """Parse post-\\begin{document} formal environments and all xltabular/tabularx tables across modular TeX."""
    return _parse_single_tex_file(tex_file, prefix="", start_at_begin_doc=True)


def get_bib_keys(bib_file: pathlib.Path, tex_file: pathlib.Path) -> Tuple[Set[str], Set[str]]:
    bib_keys: Set[str] = set()
    if bib_file.exists():
        content = bib_file.read_text(encoding="utf-8")
        bib_keys.update(re.findall(r"@\w+\{([^,]+),", content))
    tex_keys: Set[str] = set()
    if tex_file.exists():
        tex_content = tex_file.read_text(encoding="utf-8")
        tex_keys.update(re.findall(r"\\bibitem\{([^}]+)\}", tex_content))
    return bib_keys, tex_keys


def get_available_lean_decls() -> Tuple[Set[str], Set[str]]:
    """Collect blueprint/lean_decls and namespace-qualified declarations from HomotopyCRM/*.lean."""
    bp_decls: Set[str] = set()
    if BLUEPRINT_DECLS_PATH.exists():
        for line in BLUEPRINT_DECLS_PATH.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line:
                bp_decls.add(line)

    lean_decls = set(bp_decls)
    decl_pat = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)?(?:noncomputable\s+)?(?:def|theorem|lemma|instance|class|structure|inductive|abbrev)\s+([A-Za-z0-9_.']+)")
    ns_pat = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)")
    sec_pat = re.compile(r"^section(?:\s+([A-Za-z0-9_.]+))?\s*$")
    end_pat = re.compile(r"^end(?:\s+([A-Za-z0-9_.]+))?\s*$")

    if LEAN_DIR.exists():
        for lean_file in sorted(LEAN_DIR.glob("*.lean")):
            scope_stack: List[Tuple[str, str]] = []
            for raw_line in lean_file.read_text(encoding="utf-8").splitlines():
                stripped = raw_line.strip()
                if not stripped or stripped.startswith("--") or stripped.startswith("/-"):
                    continue
                nm = ns_pat.match(stripped)
                if nm:
                    for part in nm.group(1).split("."):
                        scope_stack.append(("namespace", part))
                    continue
                sm = sec_pat.match(stripped)
                if sm:
                    scope_stack.append(("section", sm.group(1) or ""))
                    continue
                em = end_pat.match(stripped)
                if em:
                    if em.group(1):
                        for _ in em.group(1).split("."):
                            if scope_stack:
                                scope_stack.pop()
                    elif scope_stack:
                        scope_stack.pop()
                    continue
                dm = decl_pat.match(stripped)
                if dm:
                    dname = dm.group(1)
                    ns_parts = [name for kind, name in scope_stack if kind == "namespace"]
                    if dname.startswith("HomotopyCRM."):
                        lean_decls.add(dname)
                    elif ns_parts:
                        lean_decls.add(".".join(ns_parts + [dname]))
                    else:
                        lean_decls.add(dname)
                        lean_decls.add("HomotopyCRM." + dname)

    return lean_decls, bp_decls


def parse_markdown_catalog(md_file: pathlib.Path) -> Dict[str, Any]:
    """Parse Part I, Part II, Part III (8-col rows), Part IV (5-col rows), and §7 summary rows."""
    lines = md_file.read_text(encoding="utf-8").splitlines()
    part1: List[Dict[str, Any]] = []
    part2: List[Dict[str, Any]] = []
    part3: List[Dict[str, Any]] = []
    part4: List[Dict[str, Any]] = []
    ledger72: Dict[str, Tuple[int, int, int, int]] = {}
    ledger73: Dict[str, Tuple[int, int, int, int]] = {}
    malformed_rows: List[str] = []

    sec = None
    subsec = None
    for idx, raw_line in enumerate(lines, 1):
        line = raw_line.strip()
        if line.startswith("## 3."):
            sec = "P1"
            subsec = None
            continue
        if line.startswith("## 4."):
            sec = "P2"
            subsec = None
            continue
        if line.startswith("## 5."):
            sec = "P3"
            subsec = None
            continue
        if line.startswith("## 6."):
            sec = "P4"
            subsec = None
            continue
        if line.startswith("## 7."):
            sec = "P5"
            subsec = None
            continue
        if line.startswith("### 7.2"):
            subsec = "7.2"
            continue
        if line.startswith("### 7.3"):
            subsec = "7.3"
            continue
        if line.startswith("### "):
            subsec = None
            continue

        if not line.startswith("|") or not line.endswith("|"):
            continue

        cells = [c.strip() for c in line.strip("|").split("|")]
        if not cells:
            continue
        first = cells[0]
        if first in ("ID / Label", "ID", "Table #", "Monograph Cohort", "Canonical Foundational Grounding Category", "Foundational Coordinate Axis"):
            continue
        if all(set(c) <= {"-", ":"} for c in cells):
            continue

        if sec in ("P1", "P2", "P3") and len(cells) == 8:
            row = {
                "id": cells[0].strip("`"),
                "type": cells[1].strip("`"),
                "line": cells[2],
                "title": cells[3],
                "axis": cells[4],
                "grounding": cells[5],
                "evidence": cells[6],
                "characterization": cells[7],
                "source_line": idx,
            }
            if sec == "P1":
                part1.append(row)
            elif sec == "P2":
                part2.append(row)
            else:
                part3.append(row)
        elif sec in ("P1", "P2", "P3"):
            malformed_rows.append(f"Line {idx} ({sec}): expected 8 table columns, found {len(cells)} (unescaped '|'?).")
        elif sec == "P4" and len(cells) == 5:
            part4.append(
                {
                    "table_num": cells[0],
                    "line": cells[1],
                    "env_label": cells[2],
                    "scope": cells[3],
                    "claim_ids": [c.strip().strip("`") for c in cells[4].split(",") if c.strip()],
                    "source_line": idx,
                }
            )
        elif sec == "P4":
            malformed_rows.append(f"Line {idx} (P4): expected 5 table columns, found {len(cells)} (unescaped '|'?).")
        elif sec == "P5" and subsec == "7.2" and len(cells) == 5:
            cat = cells[0].strip("*").strip("`")
            try:
                nums = tuple(int(c.strip("*")) for c in cells[1:5])
                ledger72[cat] = nums  # type: ignore[assignment]
            except ValueError:
                pass
        elif sec == "P5" and subsec == "7.3" and len(cells) == 5:
            ax = cells[0].strip("*").split("(")[0].split("/")[0].strip()
            try:
                nums = tuple(int(c.strip("*")) for c in cells[1:5])
                ledger73[ax] = nums  # type: ignore[assignment]
            except ValueError:
                pass

    return {
        "part1": part1,
        "part2": part2,
        "part3": part3,
        "part4": part4,
        "ledger72": ledger72,
        "ledger73": ledger73,
        "malformed_rows": malformed_rows,
    }


def _check_citations_and_lean(
    row: Dict[str, Any],
    all_bib_keys: Set[str],
    available_decls: Set[str],
    errors: List[str],
) -> Tuple[List[str], List[str]]:
    cid = row["id"]
    evidence = row["evidence"]
    cit_keys = re.findall(r"\[([A-Za-z][A-Za-z0-9_-]*\d{2}[a-z]?)\]", evidence)
    for key in cit_keys:
        if key not in all_bib_keys:
            errors.append(f"{cid}: unknown citation key [{key}] (not in references.bib / tex).")

    lean_refs = re.findall(r"(?:HomotopyCRM|Checks)\.[A-Za-z0-9_.']+", evidence)
    for decl in lean_refs:
        if decl not in available_decls:
            errors.append(f"{cid}: unknown Lean declaration '{decl}'.")

    return cit_keys, lean_refs


def verify_technical_claims() -> Tuple[bool, List[str], Dict[str, Any]]:
    errors: List[str] = []

    for p in (TEX_PATH, MD_PATH, BLUEPRINT_DECLS_PATH):
        if not p.exists():
            return False, [f"Missing required file: {p}"], {}

    tex_envs, tex_tables, tex_line_counts = parse_tex_structure(TEX_PATH)
    bib_keys, tex_bib_keys = get_bib_keys(BIB_PATH, TEX_PATH)
    all_bib_keys = bib_keys | tex_bib_keys
    available_decls, blueprint_decls = get_available_lean_decls()
    catalog = parse_markdown_catalog(MD_PATH)
    errors.extend(catalog.get("malformed_rows", []))

    md_text = MD_PATH.read_text(encoding="utf-8")
    tex_texts = {TEX_PATH.name: TEX_PATH.read_text(encoding="utf-8")}
    for _, (_, sub_p) in INPUT_PREFIX_MAP.items():
        if sub_p.exists():
            tex_texts[sub_p.name] = sub_p.read_text(encoding="utf-8")

    # 1. Anti-hallucination and placeholder scan across .md and all .tex modules
    for ph in PLACEHOLDER_STRINGS:
        if ph in md_text:
            errors.append(f"Placeholder or draft string '{ph}' found in {MD_PATH.name}.")
    for banned in BANNED_CITATIONS:
        if banned in md_text:
            errors.append(f"Banned/rectified citation artifact '{banned}' found in {MD_PATH.name}.")
        for tname, tcontent in tex_texts.items():
            if banned in tcontent:
                errors.append(f"Banned/rectified citation artifact '{banned}' found in {tname}.")

    part1 = catalog["part1"]
    part2 = catalog["part2"]
    part3 = catalog["part3"]
    part4 = catalog["part4"]

    # 2. Validate Part I & Part II 1-to-1 bijection with all 88 formal LaTeX environments
    tex_result_envs = [e for e in tex_envs if e["type"] in RESULT_ENVS]
    tex_struct_envs = [e for e in tex_envs if e["type"] in STRUCTURAL_ENVS]
    if len(tex_result_envs) != 51:
        errors.append(f"Expected 51 formal result environments in LaTeX, found {len(tex_result_envs)}.")
    if len(tex_struct_envs) != 37:
        errors.append(f"Expected 37 structural/open environments in LaTeX, found {len(tex_struct_envs)}.")
    if len(part1) != len(tex_result_envs):
        errors.append(f"Part I row count ({len(part1)}) != LaTeX formal results ({len(tex_result_envs)}).")
    if len(part2) != len(tex_struct_envs):
        errors.append(f"Part II row count ({len(part2)}) != LaTeX structural/open environments ({len(tex_struct_envs)}).")

    all_rows = part1 + part2 + part3
    seen_ids: Set[str] = set()
    for row in all_rows:
        cid = row["id"]
        if cid in seen_ids:
            errors.append(f"Duplicate catalog ID '{cid}' at line {row['source_line']}.")
        seen_ids.add(cid)

    part1_by_id = {r["id"]: r for r in part1}
    part2_by_id = {r["id"]: r for r in part2}
    formal_md_by_id = {**part1_by_id, **part2_by_id}

    for env in tex_envs:
        lbl = env["label"]
        tex_loc = format_locator(env["prefix"], env["line"])
        if not lbl:
            errors.append(f"Formal {env['type']} at LaTeX {tex_loc} lacks \\label{{...}}.")
            continue
        if lbl not in formal_md_by_id:
            errors.append(f"Formal {env['type']} '{lbl}' ({tex_loc}) missing from Parts I/II.")
            continue
        row = formal_md_by_id[lbl]
        if row["type"].lower() != env["type"].lower():
            errors.append(f"{lbl}: type mismatch tex='{env['type']}' vs md='{row['type']}'.")
        try:
            md_pfx, md_line = parse_locator(row["line"])
            if md_pfx != env["prefix"] or abs(md_line - env["line"]) > 2:
                errors.append(f"{lbl}: locator drift tex={tex_loc} vs md={row['line']}.")
        except ValueError:
            errors.append(f"{lbl}: invalid locator '{row['line']}'.")
        nt_tex = normalize_title(env["title"])
        nt_md = normalize_title(row["title"])
        if nt_tex and nt_tex != nt_md:
            errors.append(f"{lbl}: title mismatch tex='{nt_tex}' vs md='{nt_md}'.")
        # Blueprint Lean decls inside formal env must all appear in row evidence
        for d in env["lean_decls"]:
            if d not in row["evidence"]:
                errors.append(f"{lbl}: LaTeX \\lean declaration '{d}' missing from Part I/II evidence.")

    extra_formal = set(formal_md_by_id.keys()) - {e["label"] for e in tex_envs if e["label"]}
    for cid in sorted(extra_formal):
        errors.append(f"Phantom formal catalog row '{cid}' not found in LaTeX post-document environments.")

    # 3. Validate Part III count and required anchor entries
    if len(part3) < 49:
        errors.append(f"Expected at least 49 Part III inline claims, found {len(part3)}.")
    part3_ids = {r["id"] for r in part3}
    for required_id in ("thm:finset-infinity-residua", "prose:ch7-adjoint-closure-conjecture"):
        if required_id not in part3_ids:
            errors.append(f"Missing required Part III entry '{required_id}'.")

    # 4. Row-level checks across Parts I, II, and III
    lean_covered: Set[str] = set()
    grounding_counts = {"P1": Counter(), "P2_remark": Counter(), "P3": Counter()}
    axis_counts = {"P1": Counter(), "P2": Counter(), "P3": Counter()}

    for cohort, rows in (("P1", part1), ("P2", part2), ("P3", part3)):
        for row in rows:
            cid = row["id"]
            for field in ("id", "type", "line", "title", "axis", "grounding", "evidence", "characterization"):
                if not row[field].strip():
                    errors.append(f"{cid}: empty '{field}' cell.")
            try:
                pfx, line_num = parse_locator(row["line"])
                if pfx not in tex_line_counts:
                    errors.append(f"{cid}: unknown file prefix '{pfx}' in locator '{row['line']}'.")
                elif not (1 <= line_num <= tex_line_counts[pfx]):
                    errors.append(f"{cid}: line {row['line']} out of bounds 1..{tex_line_counts[pfx]}.")
            except ValueError:
                errors.append(f"{cid}: invalid line locator '{row['line']}'.")
            if row["axis"] not in CANONICAL_AXES:
                errors.append(f"{cid}: non-canonical axis '{row['axis']}'.")
            axis_counts[cohort][row["axis"]] += 1

            g = row["grounding"]
            rtype_l = row["type"].lower()
            if cohort == "P2" and rtype_l == "definition":
                if g not in DEFINITION_CATEGORIES:
                    errors.append(f"{cid}: invalid definition grounding '{g}'.")
            elif cohort == "P2" and rtype_l == "problem":
                if g not in PROBLEM_CATEGORIES:
                    errors.append(f"{cid}: invalid problem grounding '{g}'.")
            else:
                if g not in CANONICAL_RESULT_CATEGORIES:
                    errors.append(f"{cid}: invalid result grounding '{g}'.")
                if cohort == "P1":
                    grounding_counts["P1"][g] += 1
                elif cohort == "P2" and rtype_l == "remark":
                    grounding_counts["P2_remark"][g] += 1
                elif cohort == "P3":
                    grounding_counts["P3"][g] += 1

            cit_keys, lean_refs = _check_citations_and_lean(row, all_bib_keys, available_decls, errors)
            lean_covered.update(lean_refs)

            if g in ("External theorem", "Folklore") and not cit_keys:
                errors.append(f"{cid}: grounding '{g}' lacks bracketed BibTeX key [AuthorYY] in evidence.")
            if g == "Proved by Lean code" and not lean_refs:
                errors.append(f"{cid}: grounding 'Proved by Lean code' lacks HomotopyCRM.* declaration in evidence.")

    # 5. Validate 89/89 coverage of blueprint/lean_decls in MD_PATH
    missing_bp = sorted(blueprint_decls - set(re.findall(r"(?:HomotopyCRM|Checks)\.[A-Za-z0-9_.']+", md_text)))
    if missing_bp:
        errors.append(f"blueprint/lean_decls declarations missing from catalog ({len(missing_bp)}): {missing_bp[:5]}")

    # 6. Validate Part IV table matrix (all 17 tables)
    if len(part4) != len(tex_tables):
        errors.append(f"Part IV table count ({len(part4)}) != LaTeX tables ({len(tex_tables)}).")
    else:
        for t_idx, (tex_t, md_t) in enumerate(zip(tex_tables, part4), 1):
            tex_t_loc = format_locator(tex_t["prefix"], tex_t["line"])
            try:
                md_t_pfx, md_t_line = parse_locator(md_t["line"])
                if md_t_pfx != tex_t["prefix"] or abs(md_t_line - tex_t["line"]) > 2:
                    errors.append(f"Part IV table #{t_idx}: locator drift tex={tex_t_loc} vs md={md_t['line']}.")
            except ValueError:
                errors.append(f"Part IV table #{t_idx}: invalid locator '{md_t['line']}'.")
            if not md_t["claim_ids"]:
                errors.append(f"Part IV table #{t_idx}: empty Cataloged Claim IDs cell.")
            for cid in md_t["claim_ids"]:
                if cid not in seen_ids:
                    errors.append(f"Part IV table #{t_idx}: references unknown claim ID '{cid}'.")

    # 7. Validate Summary Ledger §7.2 and §7.3 arithmetic
    for cat in CANONICAL_RESULT_CATEGORIES:
        expected = (
            grounding_counts["P1"][cat],
            grounding_counts["P2_remark"][cat],
            grounding_counts["P3"][cat],
            grounding_counts["P1"][cat] + grounding_counts["P2_remark"][cat] + grounding_counts["P3"][cat],
        )
        recorded = catalog["ledger72"].get(cat)
        if recorded != expected:
            errors.append(f"Ledger §7.2 mismatch for '{cat}': recorded={recorded} vs computed={expected}.")

    for ax in CANONICAL_AXES:
        expected_ax = (
            axis_counts["P1"][ax],
            axis_counts["P2"][ax],
            axis_counts["P3"][ax],
            axis_counts["P1"][ax] + axis_counts["P2"][ax] + axis_counts["P3"][ax],
        )
        recorded_ax = catalog["ledger73"].get(ax)
        if recorded_ax != expected_ax:
            errors.append(f"Ledger §7.3 mismatch for '{ax}': recorded={recorded_ax} vs computed={expected_ax}.")

    # 8. Validate Part III and §7.1 heading / table census counts
    m_p3_hdr = re.search(r"^##\s+5\.\s+Part III:[^\n]*\((\d+)\s+Claims\)", md_text, re.MULTILINE)
    if not m_p3_hdr or int(m_p3_hdr.group(1)) != len(part3):
        rec_hdr = m_p3_hdr.group(1) if m_p3_hdr else None
        errors.append(f"Heading §5 Part III count mismatch: recorded={rec_hdr} vs computed={len(part3)}.")

    m_71_hdr = re.search(r"^###\s+7\.1\s+Overall Census Coverage\s*\((\d+)\s+Entries", md_text, re.MULTILINE)
    if not m_71_hdr or int(m_71_hdr.group(1)) != len(all_rows):
        rec_71 = m_71_hdr.group(1) if m_71_hdr else None
        errors.append(f"Heading §7.1 total count mismatch: recorded={rec_71} vs computed={len(all_rows)}.")

    m_71_p3 = re.search(r"^\|\s*\*\*Part III:[^|]*\*\*\s*\|\s*[^|]*\s*\|\s*\*\*(\d+)\*\*\s*\|", md_text, re.MULTILINE)
    if not m_71_p3 or int(m_71_p3.group(1)) != len(part3):
        rec_71_p3 = m_71_p3.group(1) if m_71_p3 else None
        errors.append(f"Ledger §7.1 Part III row mismatch: recorded={rec_71_p3} vs computed={len(part3)}.")

    m_71_tot = re.search(r"^\|\s*\*\*Total Claim / Environment Rows\*\*\s*\|\s*[^|]*\s*\|\s*\*\*(\d+)\*\*\s*\|", md_text, re.MULTILINE)
    if not m_71_tot or int(m_71_tot.group(1)) != len(all_rows):
        rec_71_tot = m_71_tot.group(1) if m_71_tot else None
        errors.append(f"Ledger §7.1 total row mismatch: recorded={rec_71_tot} vs computed={len(all_rows)}.")

    summary = {
        "total_catalog_entries": len(all_rows),
        "part1_formal_results": len(part1),
        "part2_structural_and_open": len(part2),
        "part3_inline_claims": len(part3),
        "part4_tables": len(part4),
        "evaluated_result_assertions": sum(grounding_counts["P1"].values())
        + sum(grounding_counts["P2_remark"].values())
        + sum(grounding_counts["P3"].values()),
        "blueprint_decls_covered": f"{len(blueprint_decls) - len(missing_bp)}/{len(blueprint_decls)}",
        "grounding_breakdown_total": dict(
            grounding_counts["P1"] + grounding_counts["P2_remark"] + grounding_counts["P3"]
        ),
        "axis_breakdown_total": dict(axis_counts["P1"] + axis_counts["P2"] + axis_counts["P3"]),
        "distinct_citations_verified": len(set(re.findall(r"\[([A-Za-z][A-Za-z0-9_-]*\d{2}[a-z]?)\]", md_text)) & all_bib_keys),
    }
    return len(errors) == 0, errors, summary


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify technical claims foundations catalog against LaTeX and Lean.")
    parser.add_argument("--check", action="store_true", help="Run verification check and exit non-zero on failure.")
    parser.add_argument("--json", action="store_true", help="Output verification summary as JSON.")
    args = parser.parse_args()

    passed, errors, summary = verify_technical_claims()

    if args.json:
        print(json.dumps({"passed": passed, "errors": errors, "summary": summary}, indent=2))
    else:
        print("=== Monograph Technical Claims & Foundations Verification ===")
        print(f"Total catalog entries : {summary.get('total_catalog_entries', 0)}")
        print(f"  Part I (results)    : {summary.get('part1_formal_results', 0)}")
        print(f"  Part II (def/rem/p) : {summary.get('part2_structural_and_open', 0)}")
        print(f"  Part III (inline)   : {summary.get('part3_inline_claims', 0)}")
        print(f"  Part IV (tables)    : {summary.get('part4_tables', 0)}")
        print(f"Blueprint Lean decls  : {summary.get('blueprint_decls_covered', '0/0')}")
        eval_cnt = summary.get("evaluated_result_assertions", 0)
        tot_cnt = summary.get("total_catalog_entries", 0)
        print(f"Grounding totals ({eval_cnt}) : {summary.get('grounding_breakdown_total', {})}")
        print(f"Axis totals ({tot_cnt})     : {summary.get('axis_breakdown_total', {})}")
        print(f"Distinct citations    : {summary.get('distinct_citations_verified', 0)}")
        if passed:
            print("STATUS: PASS")
        else:
            print(f"STATUS: FAIL ({len(errors)} errors)")
            for err in errors:
                print(f"  - {err}")

    if args.check and not passed:
        return 1
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
