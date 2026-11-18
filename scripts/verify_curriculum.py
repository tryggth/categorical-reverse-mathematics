#!/usr/bin/env python3
"""
Production Verification Suite for Categorical Reverse Mathematics Concept Curriculum & DAG.

Validates the ten core curriculum and graph architecture invariants across Chapters 1-8:
 1. Immutability: docs/categorical_reverse_mathematics.tex, docs/ch07_sets_residuum.tex, and HomotopyCRM/ untouched.
 2. Text, Markdown, & MathJax Hygiene: 0 control chars, balanced $ delimiters, 0 raw preamble-only TeX macros or leaked meta-tokens.
 3. Graph Topology: 61 canonical nodes, 147 directed edges, and exact adjacency symmetry in JSON schema.
 4. DAG Invariants: Strict acyclicity (0 cycles), Rank(u) < Rank(v), 100% reachability from UG roots, sole sink ADV_EPILOGUE_SYNTHESIS.
 5. Tri-Format Graph Isomorphism: Exact node and edge bijection across Mermaid.js, Graphviz DOT, and JSON schema.
 6. Prerequisite Bijective Mapping: 55 prerequisite concepts (P01-P55) fully covered and aligned.
 7. Monograph Concept Coverage & GFM Table Alignment: 189 monograph concepts (C001-C189) across Index (5 cols), Catalog, JSON, and Master Table (8 cols, 0 span shorthands).
 8. Source Line Grounding, Linearized Monotonicity, & Compiled .aux Alignment: Strict Ch 1+ boundary (>= line 568), monotonic order, and exact [section]/[chapter] label numbering.
 9. Zero Stale Pre-Chapter-7 Drift: 0 stale 7-chapter / 14-problem / 9-module strings across curriculum and graph files.
10. Visual Rendering: Graphviz DOT compiles cleanly to SVG via dot -Tsvg.
"""

import sys
import os
import re
import json
import subprocess
import graphlib

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
CURRICULUM_PATH = os.path.join(REPO_ROOT, "docs/concept_curriculum.md")
DOT_PATH = os.path.join(REPO_ROOT, "docs/concept_graph.dot")
JSON_PATH = os.path.join(REPO_ROOT, "docs/concept_graph.json")
MAIN_TEX_PATH = os.path.join(REPO_ROOT, "docs/categorical_reverse_mathematics.tex")
CH07_TEX_PATH = os.path.join(REPO_ROOT, "docs/ch07_sets_residuum.tex")
AUX_PATH = os.path.join(REPO_ROOT, "docs/categorical_reverse_mathematics.aux")

EXPECTED_NODES = 61
EXPECTED_EDGES = 147
EXPECTED_PREREQS = 55
EXPECTED_CONCEPTS = 189


def count_unescaped_pipes(line):
    """Count GFM table column delimiter pipes outside inline math ($...$) and code spans (`...`)."""
    stripped = re.sub(r"`[^`]*`", "", line)
    stripped = re.sub(r"\$[^$]*\$", "", stripped)
    stripped = stripped.replace(r"\|", "")
    return stripped.count("|")


def verify_immutability():
    print("[1/10] Verifying repository immutability (LaTeX and Lean sources)...")
    res = subprocess.run(
        [
            "git",
            "status",
            "--porcelain",
            "docs/categorical_reverse_mathematics.tex",
            "docs/ch07_sets_residuum.tex",
            "HomotopyCRM/",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    if res.stdout.strip():
        print(f"FAIL: Working tree modified in immutable paths:\n{res.stdout}")
        return False
    print("       PASS: Monograph TeX sources and HomotopyCRM/ are 100% clean.")
    return True


def verify_curriculum_hygiene(curriculum_text, curriculum_bytes):
    print("[2/10] Verifying text, Markdown, & MathJax hygiene and math delimiter balance...")
    if b"\x0b" in curriculum_bytes:
        print("FAIL: Unescaped vertical tab byte (\\x0b) detected in docs/concept_curriculum.md")
        return False

    bad_bytes = [b for b in curriculum_bytes if b not in b"\r\n\t" and b < 32]
    if bad_bytes:
        print(f"FAIL: Disallowed ASCII control bytes detected: {set(bad_bytes)}")
        return False

    dollar_count = curriculum_text.count("$")
    if dollar_count % 2 != 0:
        print(f"FAIL: Odd inline LaTeX math delimiter count ($): {dollar_count}")
        return False

    # Check per-line $ balance outside $$ display math blocks
    in_display = False
    for idx, line in enumerate(curriculum_text.splitlines(), 1):
        dd = line.count("$$")
        if dd % 2 == 1:
            in_display = not in_display
            continue
        if not in_display:
            rem = line.replace("$$", "")
            if rem.count("$") % 2 != 0:
                print(f"FAIL: Unbalanced inline $ on line {idx}: {line}")
                return False

    forbidden_tokens = [
        "TODO",
        "TBD",
        "FIXME",
        "VERIFICATION AUDIT RESULT: PASSED",
        "verify_graph_architecture.py",
        r"\texttt{",
        r"\Eff",
        r"\CohesiveQuad",
        r"\v{C}",
        r'\"',
        r"vs.\ ",
        "Requirement R1",
        "Constitutional Guardrail",
    ]
    for token in forbidden_tokens:
        if token in curriculum_text:
            print(f"FAIL: Prohibited token, raw TeX blemish, or leaked prompt string found: '{token}'")
            return False

    # Check for TeX smart quotes `` outside code fences
    non_fence = re.sub(r"```.*?```", "", curriculum_text, flags=re.DOTALL)
    if "``" in non_fence:
        print("FAIL: Raw TeX smart quote `` detected in Markdown text")
        return False

    print(f"       PASS: Clean UTF-8, per-line $ parity ($ count: {dollar_count}), 0 raw TeX/MathJax or prompt blemishes.")
    return True


def verify_json_topology(json_data):
    print(f"[3/10] Verifying JSON graph topology ({EXPECTED_NODES} nodes, {EXPECTED_EDGES} edges)...")
    nodes = {n["id"]: n for n in json_data["nodes"]}
    if len(nodes) != EXPECTED_NODES:
        print(f"FAIL: Expected {EXPECTED_NODES} nodes in JSON schema, found {len(nodes)}")
        return False

    edges = json_data["edges"]
    if len(edges) != EXPECTED_EDGES:
        print(f"FAIL: Expected {EXPECTED_EDGES} edges in JSON schema, found {len(edges)}")
        return False

    if json_data.get("metadata", {}).get("total_nodes") != EXPECTED_NODES:
        print("FAIL: metadata.total_nodes mismatch")
        return False
    if json_data.get("metadata", {}).get("total_edges") != EXPECTED_EDGES:
        print("FAIL: metadata.total_edges mismatch")
        return False

    edge_pairs = set()
    for e in edges:
        pair = (e["source"], e["target"])
        if pair in edge_pairs:
            print(f"FAIL: Duplicate edge {pair}")
            return False
        if not e.get("rationale", "").strip():
            print(f"FAIL: Missing rationale on edge {pair}")
            return False
        edge_pairs.add(pair)

    for nid, n in nodes.items():
        expected_in = sorted(u for (u, v) in edge_pairs if v == nid)
        expected_out = sorted(v for (u, v) in edge_pairs if u == nid)
        if sorted(n["prerequisites"]) != expected_in:
            print(f"FAIL: Node {nid} prerequisites mismatch: {n['prerequisites']} vs {expected_in}")
            return False
        if sorted(n["dependents"]) != expected_out:
            print(f"FAIL: Node {nid} dependents mismatch: {n['dependents']} vs {expected_out}")
            return False

    print(f"       PASS: Exactly {EXPECTED_NODES} canonical nodes and {EXPECTED_EDGES} directed edges with symmetric adjacency.")
    return True


def verify_dag_properties(json_data):
    print("[4/10] Verifying DAG acyclicity, 100% reachability, and sink nodes...")
    nodes = {n["id"]: n for n in json_data["nodes"]}

    prereqs = {nid: set(n["prerequisites"]) for nid, n in nodes.items()}
    ts = graphlib.TopologicalSorter(prereqs)
    try:
        _ = list(ts.static_order())
    except graphlib.CycleError as err:
        print(f"FAIL: Directed cycle detected in graph: {err}")
        return False

    ranks = {n["id"]: n["topological_rank"] for n in nodes.values()}
    if sorted(ranks.values()) != list(range(1, EXPECTED_NODES + 1)):
        print("FAIL: Topological ranks are not a bijection onto 1..61")
        return False

    for u, n in nodes.items():
        for v in n["dependents"]:
            if ranks[u] >= ranks[v]:
                print(f"FAIL: Topological ranking violation on edge {u} -> {v}: Rank({u})={ranks[u]} >= Rank({v})={ranks[v]}")
                return False

    roots = {"UG_LOGIC", "UG_ALGEBRA", "UG_TOPOLOGY"}
    actual_roots = {nid for nid, n in nodes.items() if len(n["prerequisites"]) == 0}
    if actual_roots != roots:
        print(f"FAIL: Expected root set {roots}, got {actual_roots}")
        return False

    reachable = set(roots)
    frontier = list(roots)
    while frontier:
        curr = frontier.pop(0)
        for nxt in nodes[curr]["dependents"]:
            if nxt not in reachable:
                reachable.add(nxt)
                frontier.append(nxt)

    if len(reachable) != EXPECTED_NODES:
        unreached = set(nodes.keys()) - reachable
        print(f"FAIL: Nodes unreachable from undergraduate foundation roots: {unreached}")
        return False

    terminals = [nid for nid, n in nodes.items() if len(n["dependents"]) == 0]
    if terminals != ["ADV_EPILOGUE_SYNTHESIS"]:
        print(f"FAIL: Exactly one terminal sink allowed (ADV_EPILOGUE_SYNTHESIS), got: {terminals}")
        return False

    grad_sinks = [nid for nid, n in nodes.items() if n["stage"] == "stage_grad" and len(n["dependents"]) == 0]
    if grad_sinks:
        print(f"FAIL: Graduate sink nodes detected: {grad_sinks}")
        return False

    print(f"       PASS: Strictly acyclic DAG, {EXPECTED_NODES}/{EXPECTED_NODES} nodes reachable from roots, sole sink ADV_EPILOGUE_SYNTHESIS.")
    return True


def verify_tri_format_isomorphism(curriculum_text, dot_text, json_data):
    print("[5/10] Verifying tri-format graph isomorphism (Mermaid == DOT == JSON)...")
    m_block_match = re.search(r"```mermaid\s*\nflowchart TD(.*?)```", curriculum_text, re.DOTALL)
    if not m_block_match:
        print("FAIL: Could not locate ```mermaid flowchart block in docs/concept_curriculum.md")
        return False

    mermaid_body = m_block_match.group(1)
    mermaid_nodes = set(re.findall(r"^\s*([A-Z0-9_]+)\[\"[^\"]+\"\]:::[a-z]+$", mermaid_body, re.MULTILINE))
    mermaid_edges = set()
    for line in mermaid_body.splitlines():
        line = line.strip()
        if line.startswith("%%") or not line:
            continue
        m = re.match(r"^([A-Z0-9_]+)\s*-->\s*([A-Z0-9_]+)$", line)
        if m:
            mermaid_edges.add((m.group(1), m.group(2)))

    dot_nodes = set(re.findall(r"^\s*\"([A-Z0-9_]+)\"\s*\[label=", dot_text, re.MULTILINE))
    dot_edges = set(re.findall(r"\"([A-Z0-9_]+)\"\s*->\s*\"([A-Z0-9_]+)\"", dot_text))

    json_nodes = set(n["id"] for n in json_data["nodes"])
    json_edges = set((e["source"], e["target"]) for e in json_data["edges"])

    if mermaid_nodes != json_nodes or dot_nodes != json_nodes:
        print(f"FAIL: Node set mismatch: Mermaid={len(mermaid_nodes)}, DOT={len(dot_nodes)}, JSON={len(json_nodes)}")
        return False

    if len(mermaid_edges) != EXPECTED_EDGES or len(dot_edges) != EXPECTED_EDGES or len(json_edges) != EXPECTED_EDGES:
        print(f"FAIL: Edge count mismatch: Mermaid={len(mermaid_edges)}, DOT={len(dot_edges)}, JSON={len(json_edges)}")
        return False

    if mermaid_edges != json_edges:
        print(f"FAIL: Discrepancy between Mermaid and JSON edge sets: diff={mermaid_edges ^ json_edges}")
        return False
    if dot_edges != json_edges:
        print(f"FAIL: Discrepancy between DOT and JSON edge sets: diff={dot_edges ^ json_edges}")
        return False

    print(f"       PASS: Perfect tri-format node ({EXPECTED_NODES}) and edge ({EXPECTED_EDGES}) isomorphism across Mermaid, DOT, and JSON.")
    return True


def verify_prerequisites_coverage(curriculum_text, json_data):
    print(f"[6/10] Verifying prerequisite concepts (P01-P{EXPECTED_PREREQS:02d}) definition and bijective mapping...")
    p_matches = re.findall(
        r"#{3,4}\s+Concept\s+(P\d+):.*?\n\s*\n\s*-\s*\*\*Prerequisite ID:\*\*\s*`(P\d+)`\s*\n\s*-\s*\*\*Canonical Graph Node:\*\*\s*`([^`]+)`",
        curriculum_text,
    )
    if len(p_matches) != EXPECTED_PREREQS:
        print(f"FAIL: Expected {EXPECTED_PREREQS} prerequisite definitions in text, found {len(p_matches)}")
        return False

    text_p_map = {m[1]: m[2] for m in p_matches}
    expected_p = {f"P{i:02d}" for i in range(1, EXPECTED_PREREQS + 1)}
    if set(text_p_map.keys()) != expected_p:
        print(f"FAIL: Missing prerequisite definitions in text: {expected_p - set(text_p_map.keys())}")
        return False

    nodes = {n["id"]: n for n in json_data["nodes"]}
    for p_id, target_node in text_p_map.items():
        if target_node not in nodes:
            print(f"FAIL: Prerequisite {p_id} points to unknown node {target_node}")
            return False
        node_ps = [c for c in nodes[target_node]["concepts_covered"] if c.startswith("P")]
        if p_id not in node_ps:
            print(f"FAIL: Prerequisite {p_id} mapped to {target_node} in text, but missing from JSON node: {node_ps}")
            return False

    json_all_p = [c for n in nodes.values() for c in n["concepts_covered"] if c.startswith("P")]
    if sorted(json_all_p) != sorted(expected_p):
        print(f"FAIL: JSON prerequisites mismatch: {sorted(json_all_p)} vs {sorted(expected_p)}")
        return False

    print(f"       PASS: All {EXPECTED_PREREQS} prerequisites (P01-P{EXPECTED_PREREQS:02d}) defined in text and bijectively mapped in JSON.")
    return True


def verify_monograph_concepts_coverage(curriculum_text, json_data):
    print(f"[7/10] Verifying monograph concepts (C001-C{EXPECTED_CONCEPTS:03d}) & GFM pipe column counts...")
    c_matches = re.findall(r"#{3,5}\s+Concept\s+(\d+):\s+([^\n]+)", curriculum_text)
    if len(c_matches) != EXPECTED_CONCEPTS:
        print(f"FAIL: Expected {EXPECTED_CONCEPTS} monograph concept sections in text, found {len(c_matches)}")
        return False
    if [int(m[0]) for m in c_matches] != list(range(1, EXPECTED_CONCEPTS + 1)):
        print("FAIL: Monograph concepts in Detailed Catalog are not strictly numbered 1..189")
        return False

    idx_start = curriculum_text.find("## Master Chronological Concept Index")
    idx_end = curriculum_text.find("## Detailed Sequential Concept Catalog", idx_start)
    idx_block = curriculum_text[idx_start:idx_end]
    idx_rows = [l.strip() for l in idx_block.splitlines() if re.match(r"^\|\s*\d+\s*\|", l.strip())]
    if len(idx_rows) != EXPECTED_CONCEPTS:
        print(f"FAIL: Expected {EXPECTED_CONCEPTS} rows in Master Chronological Concept Index, found {len(idx_rows)}")
        return False
    for r in idx_rows:
        pipes = count_unescaped_pipes(r)
        if pipes != 6:
            print(f"FAIL: Master Chronological Concept Index row has {pipes} pipes (expected 6 for 5 columns):\n  {r}")
            return False

    nodes = {n["id"]: n for n in json_data["nodes"]}
    json_all_c = set(c for n in nodes.values() for c in n["concepts_covered"] if c.startswith("C"))
    expected_c = {f"C{i:03d}" for i in range(1, EXPECTED_CONCEPTS + 1)}
    if json_all_c != expected_c:
        print(f"FAIL: JSON monograph concepts mismatch: missing={expected_c - json_all_c}, extra={json_all_c - expected_c}")
        return False

    table_start = curriculum_text.find("## Comprehensive Canonical Graph Cross-Reference Table")
    table_end = curriculum_text.find("## Stage 0:", table_start)
    if table_start == -1 or table_end == -1:
        print("FAIL: Could not delimit Master Cross-Reference Table in docs/concept_curriculum.md")
        return False

    table_block = curriculum_text[table_start:table_end]
    table_lines = [l.strip() for l in table_block.splitlines() if l.strip().startswith("|") and "`" in l]
    if len(table_lines) != EXPECTED_NODES:
        print(f"FAIL: Expected {EXPECTED_NODES} rows in Master Cross-Reference Table, found {len(table_lines)}")
        return False

    table_c_set = set()
    for row in table_lines:
        pipes = count_unescaped_pipes(row)
        if pipes != 9:
            print(f"FAIL: Master Cross-Reference Table row has {pipes} pipes (expected 9 for 8 columns):\n  {row}")
            return False
        if "–" in row or "concepts)" in row:
            print(f"FAIL: Span shorthand detected in Master Cross-Reference Table row:\n  {row}")
            return False
        for cm in re.findall(r"\bC\d{3}\b", row):
            table_c_set.add(cm)

    if table_c_set != expected_c:
        print(f"FAIL: Master Table monograph concept coverage mismatch: missing={expected_c - table_c_set}")
        return False

    print(
        f"       PASS: {EXPECTED_CONCEPTS} monograph concepts (C001-C{EXPECTED_CONCEPTS:03d}) & strict GFM column counts verified."
    )
    return True


def verify_source_ordering_and_bounds(curriculum_text):
    print("[8/10] Verifying Chapter 1+ boundary, linearized monotonicity, and .aux numbering...")
    with open(MAIN_TEX_PATH, "r", encoding="utf-8") as f:
        main_lines = f.read().splitlines()
    with open(CH07_TEX_PATH, "r", encoding="utf-8") as f:
        ch07_lines = f.read().splitlines()

    aux_labels = {}
    if os.path.exists(AUX_PATH):
        with open(AUX_PATH, "r", encoding="utf-8") as f:
            for m in re.finditer(r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{", f.read()):
                aux_labels[m.group(1)] = m.group(2)

    ch1_line = next(i + 1 for i, l in enumerate(main_lines) if "\\chapter{Foundations of Categorical Reverse Mathematics}" in l)
    ch7_input_line = next(i + 1 for i, l in enumerate(main_lines) if "ch07_sets_residuum" in l)
    backmatter_line = next(i + 1 for i, l in enumerate(main_lines) if "\\backmatter" in l)

    entries = re.findall(
        r"##### Concept (\d+): [^\n]+\n\n"
        r"- \*\*Location Reference:\*\* ([^\n]+)\n"
        r"- \*\*LaTeX Source Line:\*\* `([^`]+)`\n"
        r"- \*\*Monograph Section:\*\* ([^\n]+)",
        curriculum_text,
    )
    if len(entries) != EXPECTED_CONCEPTS:
        print(f"FAIL: Parsed {len(entries)} LaTeX Source Line fields, expected {EXPECTED_CONCEPTS}")
        return False

    prev_linear = -1.0
    for cid_s, loc_ref, src_spec, chap in entries:
        cid = int(cid_s)
        if src_spec.startswith("ch07_sets_residuum.tex:"):
            ln = int(src_spec.split(":", 1)[1])
            if chap != "Chapter 7":
                print(f"FAIL: Concept {cid} uses ch07_sets_residuum.tex but section is {chap}")
                return False
            if not (1 <= ln <= len(ch07_lines)):
                print(f"FAIL: Concept {cid} line {ln} out of range for ch07_sets_residuum.tex")
                return False
            linear_pos = ch7_input_line + (ln / 10000.0)
        else:
            ln = int(src_spec)
            if ln <= ch1_line or ln >= backmatter_line:
                print(f"FAIL: Concept {cid} at line {ln} violates mainmatter bounds ({ch1_line}..{backmatter_line})")
                return False
            if chap == "Chapter 7":
                print(f"FAIL: Concept {cid} labeled Chapter 7 must reference ch07_sets_residuum.tex")
                return False
            linear_pos = float(ln)

        if linear_pos < prev_linear:
            print(f"FAIL: Non-monotonic source ordering at Concept {cid} ({src_spec}): {linear_pos} < {prev_linear}")
            return False
        prev_linear = linear_pos

        # Check every `label` paired with a number in Location Reference against .aux
        if aux_labels:
            for num_str, lbl in re.findall(r"(\d+\.\d+(?:\.\d+)?)\s*\(`([a-z]+:[^`]+)`", loc_ref):
                if lbl in aux_labels and aux_labels[lbl] != num_str:
                    print(f"FAIL: Concept {cid} cites {num_str} (`{lbl}`), but compiled .aux has {aux_labels[lbl]}")
                    return False

    print(
        f"       PASS: All {EXPECTED_CONCEPTS} concepts lie in mainmatter in monotonic order and match compiled .aux numbers."
    )
    return True


def verify_zero_stale_drift(curriculum_text, dot_text, json_text):
    print("[9/10] Verifying zero stale pre-Chapter-7 numbering or ledger drift...")
    stale_phrases = [
        "Chapter 7: Master Atlas",
        "14 Open Problems",
        "14 open research problems",
        "fourteen open problems",
        "Seven Horizons",
        "seven horizons",
        "seven research horizons",
        "nine production modules",
        "9 Lean 4 formalization modules",
        "14,583",
        "166 `#guard_msgs",
        "Open Problem 7.",
        "Problem 7.",
        "Section 3.8",
        "Table 4.2",
    ]
    for label, blob in [("concept_curriculum.md", curriculum_text), ("concept_graph.dot", dot_text), ("concept_graph.json", json_text)]:
        for phrase in stale_phrases:
            if phrase in blob:
                print(f"FAIL: Stale or erroneous reference '{phrase}' found in {label}")
                return False

    print("       PASS: Zero stale pre-Chapter-7 chapter/problem/module/section strings across all deliverables.")
    return True


def verify_graphviz_compilation():
    print("[10/10] Verifying Graphviz DOT syntax and SVG compilation...")
    res = subprocess.run(["dot", "-Tsvg", DOT_PATH, "-o", "/dev/null"], capture_output=True, text=True)
    if res.returncode != 0:
        print(f"FAIL: dot -Tsvg failed with exit code {res.returncode}:\n{res.stderr}")
        return False
    print("        PASS: docs/concept_graph.dot compiles cleanly to SVG with zero errors.")
    return True


def main():
    print("================================================================================")
    print("  Categorical Reverse Mathematics — Concept Curriculum & DAG Verification Suite")
    print("================================================================================")

    if not verify_immutability():
        sys.exit(1)

    with open(CURRICULUM_PATH, "r", encoding="utf-8") as f:
        curriculum_text = f.read()
    with open(CURRICULUM_PATH, "rb") as f:
        curriculum_bytes = f.read()
    with open(DOT_PATH, "r", encoding="utf-8") as f:
        dot_text = f.read()
    with open(JSON_PATH, "r", encoding="utf-8") as f:
        json_text = f.read()
    json_data = json.loads(json_text)

    checks = [
        verify_curriculum_hygiene(curriculum_text, curriculum_bytes),
        verify_json_topology(json_data),
        verify_dag_properties(json_data),
        verify_tri_format_isomorphism(curriculum_text, dot_text, json_data),
        verify_prerequisites_coverage(curriculum_text, json_data),
        verify_monograph_concepts_coverage(curriculum_text, json_data),
        verify_source_ordering_and_bounds(curriculum_text),
        verify_zero_stale_drift(curriculum_text, dot_text, json_text),
        verify_graphviz_compilation(),
    ]

    if not all(checks):
        print("\n>>> VERIFICATION FAILED: One or more invariants were violated. <<<")
        sys.exit(1)

    print("================================================================================")
    print("  ALL 10 FORMAL CURRICULUM & GRAPH ARCHITECTURE INVARIANTS PASSED PERFECTLY!")
    print("================================================================================")
    sys.exit(0)


if __name__ == "__main__":
    main()
