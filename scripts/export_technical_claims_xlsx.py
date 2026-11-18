#!/usr/bin/env python3
"""Export all tables from docs/technical_claims_foundations.md to a Google-Sheets-ready .xlsx workbook."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys
import xml.etree.ElementTree as ET
from xml.sax.saxutils import escape
import zipfile


ROOT = Path(__file__).resolve().parent.parent
INPUT_MD = ROOT / "docs" / "technical_claims_foundations.md"
OUTPUT_XLSX = ROOT / "docs" / "technical_claims_foundations.xlsx"

# Temporary sentinels used while parsing math braces so literal \{ and \} survive.
SENTINEL_LBRACE = "\ue001"
SENTINEL_RBRACE = "\ue002"

TABLE_SECTIONS: list[tuple[str, str, bool]] = [
    ("## 3.", "Part I Formal Results ({n})", True),
    ("## 4.", "Part II Def-Rem-Prob ({n})", True),
    ("## 5.", "Part III Inline Claims ({n})", True),
    ("## 6.", "Part IV {n} Tables Matrix", True),
    ("### 7.1", "7.1 Census Coverage", False),
    ("### 7.2", "7.2 Grounding Categories", False),
    ("### 7.3", "7.3 Coordinate Axes", False),
]

NUMERIC_HEADERS = {
    "Line",
    "Table #",
    "Count",
    "Part I",
    "Part II (`remark`)",
    "Part II (remark)",
    "Part III (Inline / §1.6)",
    "Total",
    "Part I Count",
    "Part II Count",
    "Part III Count",
    "Total (208)",
}

CODE_OR_ID_HEADERS = {
    "ID / Label",
    "LaTeX Env / Label",
    "Cataloged Claim IDs Covered",
}

GREEK_MAP: dict[str, str] = {
    "alpha": "α",
    "beta": "β",
    "gamma": "γ",
    "delta": "δ",
    "varepsilon": "ε",
    "epsilon": "ϵ",
    "zeta": "ζ",
    "eta": "η",
    "theta": "θ",
    "iota": "ι",
    "kappa": "κ",
    "lambda": "λ",
    "mu": "μ",
    "nu": "ν",
    "xi": "ξ",
    "pi": "π",
    "rho": "ρ",
    "sigma": "σ",
    "tau": "τ",
    "phi": "φ",
    "varphi": "φ",
    "chi": "χ",
    "psi": "ψ",
    "omega": "ω",
    "Gamma": "Γ",
    "Delta": "Δ",
    "Theta": "Θ",
    "Lambda": "Λ",
    "Xi": "Ξ",
    "Pi": "Π",
    "Sigma": "Σ",
    "Phi": "Φ",
    "Psi": "Ψ",
    "Omega": "Ω",
}

BLACKBOARD_MAP: dict[str, str] = {
    "A": "𝔸",
    "C": "ℂ",
    "E": "𝔼",
    "F": "𝔽",
    "H": "ℍ",
    "N": "ℕ",
    "P": "ℙ",
    "Q": "ℚ",
    "R": "ℝ",
    "S": "𝕊",
    "T": "𝕋",
    "Z": "ℤ",
}

NEGATED_MACROS: list[tuple[str, str]] = [
    (r"\\not\s*\\simeq(?![A-Za-z])", "≄"),
    (r"\\not\s*\\cong(?![A-Za-z])", "≇"),
    (r"\\not\s*\\models(?![A-Za-z])", "⊭"),
    (r"\\not\s*\\in(?![A-Za-z])", "∉"),
    (r"\\not\s*\\le(?![A-Za-z])", "≰"),
    (r"\\not\s*\\ge(?![A-Za-z])", "≱"),
    (r"\\not\s*\\equiv(?![A-Za-z])", "≢"),
    (r"\\not\s*\\sim(?![A-Za-z])", "≁"),
    (r"\\not\s*\\implies(?![A-Za-z])", "⇏"),
    (r"\\not\s*\\Rightarrow(?![A-Za-z])", "⇏"),
    (r"\\not\s*\\subseteq(?![A-Za-z])", "⊈"),
    (r"\\not\s*\\supseteq(?![A-Za-z])", "⊉"),
    (r"\\not\s*\\subset(?![A-Za-z])", "⊄"),
    (r"\\not\s*\\supset(?![A-Za-z])", "⊅"),
    (r"\\not\s*\\exists(?![A-Za-z])", "∄"),
    (r"\\not\s*\\vdash(?![A-Za-z])", "⊬"),
    (r"\\not\s*\\leftrightarrow(?![A-Za-z])", "↮"),
    (r"\\not\s*\\(?:rightarrow|to)(?![A-Za-z])", "↛"),
    (r"\\not\s*=", "≠"),
]

BINARY_SPACED_OPS = (
    "⇔⇒⇒→≃≅∼⊨⊭≄≇∉∈⊆⊇⊊⊋⊈⊉⊄⊅∩∪⊔×⊠⊕⋊∖≠≡≤≥≰≱≢≁⇏↦↪↣↠⇄⊣"
)

SYMBOL_MACROS: dict[str, str] = {
    "Eff": "Eff",
    "S": "§",
    "Uparrow": "⇑",
    "Downarrow": "⇓",
    "Vdash": "⊩",
    "aa": "å",
    "AA": "Å",
    "amalg": "∐",
    "bigcup": "⋃",
    "bigoplus": "⊕",
    "boxtimes": "⊠",
    "bullet": "•",
    "cap": "∩",
    "cdot": "·",
    "cdots": "⋯",
    "circ": "∘",
    "cong": "≅",
    "cup": "∪",
    "dashv": "⊣",
    "dim": "dim",
    "emptyset": "∅",
    "equiv": "≡",
    "exists": "∃",
    "forall": "∀",
    "ge": "≥",
    "hookrightarrow": "↪",
    "iff": "⇔",
    "implies": "⇒",
    "Rightarrow": "⇒",
    "in": "∈",
    "infty": "∞",
    "land": "∧",
    "le": "≤",
    "leftrightarrow": "↔",
    "longrightarrow": "→",
    "lvert": "|",
    "rvert": "|",
    "mapsto": "↦",
    "max": "max",
    "mid": "|",
    "models": "⊨",
    "neg": "¬",
    "neq": "≠",
    "notin": "∉",
    "oplus": "⊕",
    "partial": "∂",
    "prec": "≺",
    "prod": "∏",
    "rightharpoonup": "⇀",
    "rightarrowtail": "↣",
    "rightleftarrows": "⇄",
    "rtimes": "⋊",
    "setminus": "∖",
    "simeq": "≃",
    "sim": "∼",
    "sqcup": "⊔",
    "square": "□",
    "subsetneq": "⊊",
    "subseteq": "⊆",
    "supsetneq": "⊋",
    "supseteq": "⊇",
    "sup": "sup",
    "times": "×",
    "to": "→",
    "top": "⊤",
    "triangle": "△",
    "twoheadrightarrow": "↠",
    "varinjlim": "colim",
    "varprojlim": "lim←",
    "vee": "∨",
    "wedge": "∧",
}

TEXT_ACCENTS: list[tuple[str, str]] = [
    (r"\\v\{C\}", "Č"),
    (r"\\v\{c\}", "č"),
    (r"\\v\{S\}", "Š"),
    (r"\\v\{s\}", "š"),
    (r"\\v\{Z\}", "Ž"),
    (r"\\v\{z\}", "ž"),
    (r"\\ss(?:\{\})?\b", "ß"),
    (r'\\"a', "ä"),
    (r'\\"e', "ë"),
    (r'\\"i', "ï"),
    (r'\\"o', "ö"),
    (r'\\"u', "ü"),
    (r'\\"A', "Ä"),
    (r'\\"E', "Ë"),
    (r'\\"I', "Ï"),
    (r'\\"O', "Ö"),
    (r'\\"U', "Ü"),
    (r'\\"\{a\}', "ä"),
    (r'\\"\{e\}', "ë"),
    (r'\\"\{i\}', "ï"),
    (r'\\"\{o\}', "ö"),
    (r'\\"\{u\}', "ü"),
    (r"\\'e", "é"),
    (r"\\'a", "á"),
    (r"\\'i", "í"),
    (r"\\'o", "ó"),
    (r"\\'u", "ú"),
    (r"\\'\{e\}", "é"),
]


@dataclass
class SheetData:
    """Normalized table data prepared for OpenXML worksheet serialization."""

    name: str
    headers: list[str]
    rows: list[list[str]]
    total_row_indices: set[int]
    autofilter: bool
    col_widths: list[float]


def split_md_row(line: str) -> list[str]:
    """Split one Markdown pipe table line into unescaped cells."""
    stripped = line.strip()
    if stripped.startswith("|"):
        stripped = stripped[1:]
    if stripped.endswith("|") and not stripped.endswith("\\|"):
        stripped = stripped[:-1]
    parts = re.split(r"(?<!\\)\|", stripped)
    return [p.replace("\\|", "|").strip() for p in parts]


def is_separator_row(cells: list[str]) -> bool:
    """Return True if a parsed Markdown row is the `| :--- | --- |` delimiter line."""
    return bool(cells) and all(bool(re.fullmatch(r":?-{3,}:?", c.strip())) for c in cells)


def parse_markdown_tables(md_path: Path) -> dict[str, tuple[list[str], list[list[str]]]]:
    """Extract the 7 Markdown tables keyed by their section prefix."""
    lines = md_path.read_text(encoding="utf-8").splitlines()
    result: dict[str, tuple[list[str], list[list[str]]]] = {}
    current_prefix: str | None = None
    table_lines: list[str] = []
    in_table = False

    def flush() -> None:
        nonlocal table_lines, in_table
        if current_prefix and table_lines:
            parsed = [split_md_row(ln) for ln in table_lines]
            headers = parsed[0]
            rows = [r for r in parsed[1:] if not is_separator_row(r)]
            result[current_prefix] = (headers, rows)
        table_lines = []
        in_table = False

    for line in lines:
        matched_prefix = next(
            (prefix for prefix, _, _ in TABLE_SECTIONS if line.startswith(prefix)),
            None,
        )
        if matched_prefix is not None:
            flush()
            current_prefix = matched_prefix
            continue

        if current_prefix is None:
            continue

        if line.lstrip().startswith("|"):
            in_table = True
            table_lines.append(line)
        elif in_table:
            flush()
            current_prefix = None

    flush()
    missing = [p for p, _, _ in TABLE_SECTIONS if p not in result]
    if missing:
        raise ValueError(f"Missing expected table sections in {md_path}: {missing}")
    return result


def read_braced_arg(text: str, pos: int) -> tuple[str, int] | None:
    """Read `{...}` starting at `pos` with balanced brace tracking."""
    n = len(text)
    while pos < n and text[pos].isspace():
        pos += 1
    if pos >= n or text[pos] != "{":
        return None
    depth = 0
    start = pos + 1
    i = pos
    while i < n:
        ch = text[i]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[start:i], i + 1
        i += 1
    return text[start:], n


def read_bracket_arg(text: str, pos: int) -> tuple[str, int] | None:
    """Read optional `[...]` starting at `pos`."""
    n = len(text)
    while pos < n and text[pos].isspace():
        pos += 1
    if pos >= n or text[pos] != "[":
        return None
    end = text.find("]", pos + 1)
    if end == -1:
        return None
    return text[pos + 1 : end], end + 1


def _strip_group_braces(expr: str) -> str:
    """Format `_` / `^` braced scripts while keeping ASCII `_` and `^` intact."""
    out: list[str] = []
    i = 0
    n = len(expr)
    while i < n:
        if expr[i] in ("_", "^") and i + 1 < n:
            op = expr[i]
            arg = read_braced_arg(expr, i + 1)
            if arg is not None:
                inner, next_pos = arg
                inner_clean = _strip_group_braces(inner.strip())
                if re.fullmatch(r"[A-Za-z0-9α-ωΑ-Ω∞±′]+", inner_clean):
                    out.append(f"{op}{inner_clean}")
                elif inner_clean.startswith("(") and inner_clean.endswith(")"):
                    out.append(f"{op}{inner_clean}")
                else:
                    out.append(f"{op}({inner_clean})")
                i = next_pos
                continue
        if expr[i] in ("{", "}"):
            i += 1
            continue
        out.append(expr[i])
        i += 1
    return "".join(out)


def _expand_parametric_macros(expr: str, font_wrappers: set[str] | None = None) -> str:
    """Expand multi-argument or braced LaTeX commands inside math or prose."""
    if font_wrappers is None:
        font_wrappers = {
            "text",
            "texttt",
            "textbf",
            "emph",
            "mathrm",
            "mathsf",
            "mathbf",
            "mathcal",
            "mathfrak",
            "lean",
        }
    changed = True
    current = expr
    while changed:
        changed = False
        out: list[str] = []
        i = 0
        n = len(current)
        while i < n:
            if current[i] != "\\":
                out.append(current[i])
                i += 1
                continue
            m = re.match(r"\\([A-Za-z]+)", current[i:])
            if not m:
                out.append(current[i])
                i += 1
                continue
            cmd = m.group(1)
            after_cmd = i + len(m.group(0))

            if cmd in font_wrappers:
                arg = read_braced_arg(current, after_cmd)
                if arg is not None:
                    inner, next_pos = arg
                    out.append(inner)
                    i = next_pos
                    changed = True
                    continue

            if cmd == "mathbb":
                arg = read_braced_arg(current, after_cmd)
                if arg is not None:
                    inner, next_pos = arg
                    key = inner.strip()
                    out.append(BLACKBOARD_MAP.get(key, key))
                    i = next_pos
                    changed = True
                    continue

            if cmd in ("frac", "tfrac"):
                num_arg = read_braced_arg(current, after_cmd)
                if num_arg is not None:
                    den_arg = read_braced_arg(current, num_arg[1])
                    if den_arg is not None:
                        num_s = num_arg[0].strip()
                        den_s = den_arg[0].strip()
                        num_fmt = num_s if re.fullmatch(r"[A-Za-z0-9]+", num_s) else f"({num_s})"
                        den_fmt = den_s if re.fullmatch(r"[A-Za-z0-9]+", den_s) else f"({den_s})"
                        out.append(f"{num_fmt}/{den_fmt}")
                        i = den_arg[1]
                        changed = True
                        continue

            if cmd == "xrightarrow":
                opt = read_bracket_arg(current, after_cmd)
                pos = opt[1] if opt is not None else after_cmd
                sup = read_braced_arg(current, pos)
                if sup is not None:
                    label = sup[0].strip()
                    out.append(
                        " —∼→ "
                        if label in ("~", "∼", "")
                        else f" —({label})→ "
                    )
                    i = sup[1]
                    changed = True
                    continue

            if cmd == "pmod":
                arg = read_braced_arg(current, after_cmd)
                if arg is not None:
                    out.append(f" (mod {arg[0].strip()})")
                    i = arg[1]
                    changed = True
                    continue
                unbraced = re.match(r"\s*([A-Za-z0-9]+)", current[after_cmd:])
                if unbraced:
                    out.append(f" (mod {unbraced.group(1)})")
                    i = after_cmd + len(unbraced.group(0))
                    changed = True
                    continue

            if cmd in ("bar", "overline"):
                arg = read_braced_arg(current, after_cmd)
                if arg is not None:
                    inner = arg[0].strip()
                    out.append(f"{inner}\u0304" if len(inner) == 1 else f"bar({inner})")
                    i = arg[1]
                    changed = True
                    continue

            if cmd == "widehat":
                arg = read_braced_arg(current, after_cmd)
                if arg is not None:
                    inner = arg[0].strip()
                    out.append(f"{inner}\u0302" if len(inner) == 1 else f"hat({inner})")
                    i = arg[1]
                    changed = True
                    continue

            if cmd == "overrightarrow":
                arg = read_braced_arg(current, after_cmd)
                if arg is not None:
                    inner = arg[0].strip()
                    out.append(f"{inner}\u20d7" if len(inner) == 1 else f"vec({inner})")
                    i = arg[1]
                    changed = True
                    continue

            out.append(current[i:after_cmd])
            i = after_cmd
        current = "".join(out)
    return current


def _replace_known_symbols(expr: str) -> str:
    """Replace negated, Greek, and operator macros while preserving trailing punctuation."""
    for pattern, repl in NEGATED_MACROS:
        expr = re.sub(pattern, repl, expr)
    combined_symbols = {**GREEK_MAP, **SYMBOL_MACROS}
    expr = re.sub(
        r"\\([A-Za-z]+)",
        lambda m: combined_symbols.get(m.group(1), m.group(0)),
        expr,
    )
    return expr


def _space_binary_ops(expr: str) -> str:
    """Ensure binary relations/arrows collapsed adjacent to macros remain readable."""
    spaced_chars = "⇔⇒→≃≅∼⊨⊭≄≇∉∈⊆⊇⊊⊋⊈⊉⊄⊅∩∪⊔×⊠⊕⋊∖≠≡↦↪↣↠⇄⊣"
    cls = re.escape(spaced_chars)
    # Add space before binary op unless preceded by whitespace, opener, script op, comma, or labeled arrow.
    expr = re.sub(rf"(?<![\s(\[{{_^,/—∼])([{cls}])", r" \1", expr)
    # Add space after binary op unless followed by whitespace, closer, script op, comma, or arrow tip.
    expr = re.sub(rf"([{cls}])(?![\s)\]}},_^.:→])", r"\1 ", expr)
    # Rejoin labeled arrows like `—(f)→` or `—∼→` without stray spaces before `→`.
    expr = re.sub(r"—(\([^)]+\)|∼) →", r"—\1→", expr)
    return expr


def render_math(math_src: str) -> str:
    """Convert one LaTeX `$...$` expression into searchable Unicode text."""
    s = math_src.strip()
    s = s.replace(r"\{", SENTINEL_LBRACE).replace(r"\}", SENTINEL_RBRACE)
    s = (
        s.replace(r"\_", "_")
        .replace(r"\&", "&")
        .replace(r"\%", "%")
        .replace(r"\$", "$")
        .replace(r"\#", "#")
    )
    s = re.sub(r"\\[,;! ]", " ", s)

    # Substitute non-parametric symbols BEFORE unwrapping \mathrm / \mathcal / \mathsf
    # so adjacent sequences like \mathcal{E}\to\mathcal{S} do not fuse into \toS.
    s = _replace_known_symbols(s)
    s = _expand_parametric_macros(s)
    s = _replace_known_symbols(s)

    s = _strip_group_braces(s)
    s = s.replace(SENTINEL_LBRACE, "{").replace(SENTINEL_RBRACE, "}")
    s = _space_binary_ops(s)
    s = re.sub(r"\s{2,}", " ", s).strip()
    return s


def render_prose(segment: str, preserve_hyphens: bool) -> str:
    """Convert LaTeX prose punctuation, accents, and non-math macros outside `$...$`."""
    s = segment
    for pattern, repl in TEXT_ACCENTS:
        s = re.sub(pattern, repl, s)
    s = _expand_parametric_macros(
        s,
        font_wrappers={"text", "texttt", "textbf", "emph", "mathrm", "mathsf", "mathbf", "lean"},
    )
    s = s.replace(r"\S", "§")
    s = (
        s.replace(r"\&", "&")
        .replace(r"\_", "_")
        .replace(r"\%", "%")
        .replace(r"\#", "#")
        .replace(r"\ ", " ")
    )
    s = s.replace("~", " ")
    if not preserve_hyphens:
        s = s.replace("---", "—").replace("--", "–")
    return s


def clean_cell_for_sheets(raw: str, header: str) -> tuple[str, bool]:
    """Return `(cleaned_text, is_total_row_marker)` for a Markdown cell."""
    stripped = raw.strip()
    is_total = stripped.startswith("**") and ("Subtotal" in stripped or "Total" in stripped)

    preserve_hyphens = header in CODE_OR_ID_HEADERS
    s = stripped
    # Remove Markdown bold wrappers cleanly without eating mathematical `*` symbols.
    s = re.sub(r"\*\*([^*]+)\*\*", r"\1", s)
    s = re.sub(r"`([^`]+)`", r"\1", s)

    parts = re.split(r"(\$\$[^$]+\$\$|\$[^$]+\$)", s)
    rendered_parts: list[str] = []
    for part in parts:
        if not part:
            continue
        if (part.startswith("$$") and part.endswith("$$")) or (
            part.startswith("$") and part.endswith("$")
        ):
            inner = part[2:-2] if part.startswith("$$") else part[1:-1]
            rendered_parts.append(render_math(inner))
        else:
            rendered_parts.append(render_prose(part, preserve_hyphens=preserve_hyphens))

    cleaned = "".join(rendered_parts)
    # Strip any XML 1.0 invalid control characters while preserving tabs/newlines.
    cleaned = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", cleaned)
    cleaned = re.sub(r" {2,}", " ", cleaned).strip()
    return cleaned, is_total


def build_cleaned_sheet(
    name: str,
    raw_headers: list[str],
    raw_rows: list[list[str]],
    autofilter: bool,
    width_overrides: dict[str, float],
) -> SheetData:
    """Normalize a Markdown table into a `SheetData` object."""
    headers = [clean_cell_for_sheets(h, h)[0] for h in raw_headers]
    cleaned_rows: list[list[str]] = []
    total_row_indices: set[int] = set()

    for r_idx, raw_row in enumerate(raw_rows):
        row_cells: list[str] = []
        row_is_total = False
        for c_idx, raw_cell in enumerate(raw_row):
            hdr = raw_headers[c_idx] if c_idx < len(raw_headers) else ""
            txt, marked_total = clean_cell_for_sheets(raw_cell, hdr)
            if c_idx == 0 and marked_total:
                row_is_total = True
            row_cells.append(txt)
        cleaned_rows.append(row_cells)
        if row_is_total:
            total_row_indices.add(r_idx)

    widths: list[float] = []
    for c_idx, hdr in enumerate(headers):
        if hdr in width_overrides:
            widths.append(width_overrides[hdr])
        else:
            max_len = max(
                [len(hdr)] + [len(r[c_idx]) for r in cleaned_rows if c_idx < len(r)]
            )
            widths.append(float(max(12, min(max_len + 4, 48))))

    return SheetData(
        name=name,
        headers=headers,
        rows=cleaned_rows,
        total_row_indices=total_row_indices,
        autofilter=autofilter,
        col_widths=widths,
    )


def build_all_sheets(md_path: Path) -> list[SheetData]:
    """Parse `technical_claims_foundations.md` and construct all 8 workbook tabs."""
    tables = parse_markdown_tables(md_path)

    claim_widths: dict[str, float] = {
        "Part": 11.0,
        "Evaluated Claim?": 22.0,
        "ID / Label": 29.0,
        "Type": 15.0,
        "Line": 8.0,
        "Claim Title": 46.0,
        "Axis": 13.0,
        "Foundational Grounding": 29.0,
        "Grounding Evidence / Location": 52.0,
        "Characterization Types": 36.0,
    }
    matrix_widths: dict[str, float] = {
        "Table #": 9.0,
        "Line": 8.0,
        "LaTeX Env / Label": 28.0,
        "Table Title / Scope": 48.0,
        "Cataloged Claim IDs Covered": 44.0,
    }
    ledger_widths: dict[str, float] = {
        "Monograph Cohort": 32.0,
        "Environment / Scope": 42.0,
        "Count": 16.0,
        "Grounding Breakdown": 48.0,
        "Canonical Foundational Grounding Category": 34.0,
        "Foundational Coordinate Axis": 26.0,
    }

    part_sheets: list[SheetData] = []
    master_raw_rows: list[list[str]] = []

    part_tag_map = {
        "## 3.": "Part I",
        "## 4.": "Part II",
        "## 5.": "Part III",
    }

    for prefix, sheet_template, autofilter in TABLE_SECTIONS:
        raw_headers, raw_rows = tables[prefix]
        sheet_name = sheet_template.format(n=len(raw_rows))
        if prefix in part_tag_map:
            part_label = part_tag_map[prefix]
            type_idx = raw_headers.index("Type")
            for raw_row in raw_rows:
                row_type = clean_cell_for_sheets(raw_row[type_idx], "Type")[0]
                evaluated = (
                    "No (Definition/Problem)"
                    if row_type in ("Definition", "Problem")
                    else "Yes"
                )
                master_raw_rows.append([part_label, evaluated, *raw_row])

        overrides = (
            claim_widths
            if prefix in part_tag_map
            else (matrix_widths if prefix == "## 6." else ledger_widths)
        )
        part_sheets.append(
            build_cleaned_sheet(sheet_name, raw_headers, raw_rows, autofilter, overrides)
        )

    p1_headers = tables["## 3."][0]
    master_headers = ["Part", "Evaluated Claim?", *p1_headers]
    master_sheet = build_cleaned_sheet(
        f"Master All Claims ({len(master_raw_rows)})",
        master_headers,
        master_raw_rows,
        autofilter=True,
        width_overrides=claim_widths,
    )

    return [master_sheet, *part_sheets]


def col_to_excel(col_idx_zero_based: int) -> str:
    """Convert 0-based column index to Excel column letters (A, B, ..., AA)."""
    idx = col_idx_zero_based + 1
    letters: list[str] = []
    while idx > 0:
        idx, rem = divmod(idx - 1, 26)
        letters.append(chr(ord("A") + rem))
    return "".join(reversed(letters))


def make_styles_xml() -> str:
    """Build OOXML `xl/styles.xml` with CRMBlue header, body, integer, and total styles."""
    return """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">
  <fonts count="3">
    <font>
      <sz val="10"/>
      <color rgb="FF1A202C"/>
      <name val="Calibri"/>
    </font>
    <font>
      <b/>
      <sz val="10"/>
      <color rgb="FFFFFFFF"/>
      <name val="Calibri"/>
    </font>
    <font>
      <b/>
      <sz val="10"/>
      <color rgb="FF1B365D"/>
      <name val="Calibri"/>
    </font>
  </fonts>
  <fills count="4">
    <fill><patternFill patternType="none"/></fill>
    <fill><patternFill patternType="gray125"/></fill>
    <fill><patternFill patternType="solid"><fgColor rgb="FF1B365D"/></patternFill></fill>
    <fill><patternFill patternType="solid"><fgColor rgb="FFEAF0F6"/></patternFill></fill>
  </fills>
  <borders count="3">
    <border>
      <left style="thin"><color rgb="FFD9E1EB"/></left>
      <right style="thin"><color rgb="FFD9E1EB"/></right>
      <top style="thin"><color rgb="FFD9E1EB"/></top>
      <bottom style="thin"><color rgb="FFD9E1EB"/></bottom>
    </border>
    <border>
      <left style="thin"><color rgb="FF2C4A78"/></left>
      <right style="thin"><color rgb="FF2C4A78"/></right>
      <top style="thin"><color rgb="FF102542"/></top>
      <bottom style="medium"><color rgb="FF102542"/></bottom>
    </border>
    <border>
      <left style="thin"><color rgb="FFD9E1EB"/></left>
      <right style="thin"><color rgb="FFD9E1EB"/></right>
      <top style="thin"><color rgb="FF1B365D"/></top>
      <bottom style="medium"><color rgb="FF1B365D"/></bottom>
    </border>
  </borders>
  <cellStyleXfs count="1">
    <xf numFmtId="0" fontId="0" fillId="0" borderId="0"/>
  </cellStyleXfs>
  <cellXfs count="5">
    <xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0" applyFont="1" applyBorder="1" applyAlignment="1">
      <alignment horizontal="left" vertical="top" wrapText="1"/>
    </xf>
    <xf numFmtId="0" fontId="1" fillId="2" borderId="1" xfId="0" applyFont="1" applyFill="1" applyBorder="1" applyAlignment="1">
      <alignment horizontal="left" vertical="center" wrapText="1"/>
    </xf>
    <xf numFmtId="1" fontId="0" fillId="0" borderId="0" xfId="0" applyNumberFormat="1" applyFont="1" applyBorder="1" applyAlignment="1">
      <alignment horizontal="right" vertical="top"/>
    </xf>
    <xf numFmtId="0" fontId="2" fillId="3" borderId="2" xfId="0" applyFont="1" applyFill="1" applyBorder="1" applyAlignment="1">
      <alignment horizontal="left" vertical="top" wrapText="1"/>
    </xf>
    <xf numFmtId="1" fontId="2" fillId="3" borderId="2" xfId="0" applyNumberFormat="1" applyFont="1" applyFill="1" applyBorder="1" applyAlignment="1">
      <alignment horizontal="right" vertical="top"/>
    </xf>
  </cellXfs>
  <cellStyles count="1">
    <cellStyle name="Normal" xfId="0" builtinId="0"/>
  </cellStyles>
</styleSheet>
"""


def make_cell_xml(ref: str, value: str, style_idx: int, is_int: bool) -> str:
    """Serialize one OOXML cell element using numeric `<v>` or `<is><t>` inlineStr."""
    if is_int:
        return f'<c r="{ref}" s="{style_idx}"><v>{value}</v></c>'
    return (
        f'<c r="{ref}" s="{style_idx}" t="inlineStr">'
        f'<is><t xml:space="preserve">{escape(value)}</t></is></c>'
    )


def make_worksheet_xml(sheet: SheetData, is_first_tab: bool) -> str:
    """Serialize a `SheetData` object to ECMA-376 worksheet XML."""
    num_cols = len(sheet.headers)
    max_row = 1 + len(sheet.rows)
    last_col = col_to_excel(num_cols - 1)
    dim_ref = f"A1:{last_col}{max_row}"

    tab_attr = ' tabSelected="1"' if is_first_tab else ""
    cols_xml = "".join(
        f'<col min="{i + 1}" max="{i + 1}" width="{w:.1f}" customWidth="1"/>'
        for i, w in enumerate(sheet.col_widths)
    )

    row_xml_parts: list[str] = []
    header_cells = "".join(
        make_cell_xml(f"{col_to_excel(c)}1", hdr, style_idx=1, is_int=False)
        for c, hdr in enumerate(sheet.headers)
    )
    row_xml_parts.append(f'<row r="1" ht="28" customHeight="1">{header_cells}</row>')

    numeric_col_flags = [h in NUMERIC_HEADERS or h.startswith("Total (") for h in sheet.headers]
    for r_idx, row in enumerate(sheet.rows):
        excel_row = r_idx + 2
        is_total = r_idx in sheet.total_row_indices
        cells_xml: list[str] = []
        for c_idx in range(num_cols):
            val = row[c_idx] if c_idx < len(row) else ""
            is_int = numeric_col_flags[c_idx] and bool(re.fullmatch(r"\d+", val))
            if is_total:
                style = 4 if is_int else 3
            else:
                style = 2 if is_int else 0
            ref = f"{col_to_excel(c_idx)}{excel_row}"
            cells_xml.append(make_cell_xml(ref, val, style_idx=style, is_int=is_int))
        row_xml_parts.append(f'<row r="{excel_row}">{"".join(cells_xml)}</row>')

    autofilter_xml = f'<autoFilter ref="{dim_ref}"/>' if sheet.autofilter else ""

    return (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
        f'<dimension ref="{dim_ref}"/>'
        "<sheetViews>"
        f'<sheetView{tab_attr} workbookViewId="0">'
        '<pane ySplit="1" topLeftCell="A2" activePane="bottomLeft" state="frozen"/>'
        "</sheetView>"
        "</sheetViews>"
        '<sheetFormatPr defaultRowHeight="18"/>'
        f"<cols>{cols_xml}</cols>"
        f'<sheetData>{"".join(row_xml_parts)}</sheetData>'
        f"{autofilter_xml}"
        "</worksheet>"
    )


def write_xlsx(sheets: list[SheetData], out_path: Path) -> None:
    """Package all worksheets and styles into a valid `.xlsx` OOXML archive."""
    for s in sheets:
        if len(s.name) > 31 or re.search(r"[\\/*\[\]:?]", s.name):
            raise ValueError(f"Invalid Excel worksheet tab name: {s.name!r}")

    sheet_overrides = "".join(
        f'<Override PartName="/xl/worksheets/sheet{i}.xml" '
        'ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>'
        for i in range(1, len(sheets) + 1)
    )
    content_types = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
        '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
        '<Default Extension="xml" ContentType="application/xml"/>'
        '<Override PartName="/xl/workbook.xml" '
        'ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
        '<Override PartName="/xl/styles.xml" '
        'ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>'
        f"{sheet_overrides}"
        "</Types>"
    )

    root_rels = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        '<Relationship Id="rId1" '
        'Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" '
        'Target="xl/workbook.xml"/>'
        "</Relationships>"
    )

    sheet_elems = "".join(
        f'<sheet name="{escape(s.name)}" sheetId="{i}" r:id="rId{i}"/>'
        for i, s in enumerate(sheets, start=1)
    )
    workbook_xml = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
        'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
        "<bookViews>"
        '<workbookView xWindow="0" yWindow="0" windowWidth="24000" windowHeight="15000"/>'
        "</bookViews>"
        f"<sheets>{sheet_elems}</sheets>"
        "</workbook>"
    )

    styles_rel_id = len(sheets) + 1
    wb_rels_entries = "".join(
        f'<Relationship Id="rId{i}" '
        'Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" '
        f'Target="worksheets/sheet{i}.xml"/>'
        for i in range(1, len(sheets) + 1)
    ) + (
        f'<Relationship Id="rId{styles_rel_id}" '
        'Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" '
        'Target="styles.xml"/>'
    )
    workbook_rels = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        f"{wb_rels_entries}"
        "</Relationships>"
    )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(out_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("[Content_Types].xml", content_types.encode("utf-8"))
        zf.writestr("_rels/.rels", root_rels.encode("utf-8"))
        zf.writestr("xl/workbook.xml", workbook_xml.encode("utf-8"))
        zf.writestr("xl/_rels/workbook.xml.rels", workbook_rels.encode("utf-8"))
        zf.writestr("xl/styles.xml", make_styles_xml().encode("utf-8"))
        for idx, sheet in enumerate(sheets, start=1):
            xml_str = make_worksheet_xml(sheet, is_first_tab=(idx == 1))
            zf.writestr(f"xl/worksheets/sheet{idx}.xml", xml_str.encode("utf-8"))


def main() -> int:
    """Export docs/technical_claims_foundations.md to .xlsx and print summary."""
    sheets = build_all_sheets(INPUT_MD)
    write_xlsx(sheets, OUTPUT_XLSX)
    print(f"Wrote {OUTPUT_XLSX} ({OUTPUT_XLSX.stat().st_size} bytes)")
    for idx, sheet in enumerate(sheets, start=1):
        print(
            f"  Sheet {idx}: {sheet.name!r} "
            f"({len(sheet.rows)} data rows x {len(sheet.headers)} cols)"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
