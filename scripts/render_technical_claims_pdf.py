#!/usr/bin/env python3
"""
scripts/render_technical_claims_pdf.py

Renders docs/technical_claims_foundations.md into a crisp, multi-page landscape
LaTeX PDF at docs/technical_claims_foundations.pdf via pdflatex, matching the
monograph's newpxtext/newpxmath + CRMBlue typography and custom macros.
"""

import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MD_PATH = ROOT / "docs" / "technical_claims_foundations.md"
PDF_OUT = ROOT / "docs" / "technical_claims_foundations.pdf"
BUILD_DIR = pathlib.Path("/tmp/claims_pdf_build")

TOKEN_RE = re.compile(r"(`[^`\n]+`|\$[^$\n]+\$|\\texttt\{[^{}]*\})")


def escape_inline_code(code: str) -> str:
    """Format inline backtick code with clean pdflatex escapes and break points."""
    out: list[str] = []
    for ch in code:
        if ch == "\\":
            out.append("\\textbackslash{}")
        elif ch == "{":
            out.append("\\{")
        elif ch == "}":
            out.append("\\}")
        elif ch == "#":
            out.append("\\#")
        elif ch == "%":
            out.append("\\%")
        elif ch == "&":
            out.append("\\&")
        elif ch == "$":
            out.append("\\$")
        elif ch == "^":
            out.append("\\textasciicircum{}")
        elif ch == "~":
            out.append("\\textasciitilde{}")
        elif ch == "_":
            out.append("\\_\\allowbreak{}")
        elif ch == ".":
            out.append(".\\allowbreak{}")
        elif ch == ":":
            out.append(":\\allowbreak{}")
        elif ch == "-":
            out.append("-\\allowbreak{}")
        elif ch == "ℤ":
            out.append("\\ensuremath{\\mathbb{Z}}")
        elif ch == "ε":
            out.append("\\ensuremath{\\varepsilon}")
        elif ch == "²":
            out.append("\\textsuperscript{2}")
        elif ch == "₁":
            out.append("\\textsubscript{1}")
        elif ch == "₂":
            out.append("\\textsubscript{2}")
        else:
            out.append(ch)
    return "{\\small\\ttfamily " + "".join(out) + "}"


def convert_plain_segment(seg: str) -> str:
    """Escape plain-text specials while preserving LaTeX commands like \\S and \\v{C}."""
    seg = seg.replace("%", "\\%")
    seg = seg.replace("#", "\\#")
    seg = seg.replace("&", "\\&")
    seg = seg.replace("_", "\\_")
    seg = re.sub(r'"([^"\n]+)"', lambda m: "``" + m.group(1) + "''", seg)
    seg = re.sub(r"\*\*([^*]+)\*\*", lambda m: "\\textbf{" + m.group(1) + "}", seg)
    seg = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", lambda m: "\\emph{" + m.group(1) + "}", seg)
    return seg


def md_inline_to_latex(text: str) -> str:
    """Token-safe Markdown + inline-LaTeX converter preserving bold/emph across math/code spans."""
    parts = TOKEN_RE.split(text)
    saved: list[str] = []
    staged: list[str] = []
    for part in parts:
        if not part:
            continue
        if part.startswith("`") and part.endswith("`"):
            idx = len(saved)
            saved.append(escape_inline_code(part[1:-1]))
            staged.append(f"\x00TOK{idx}\x00")
        elif part.startswith("$") and part.endswith("$"):
            idx = len(saved)
            saved.append(part)
            staged.append(f"\x00TOK{idx}\x00")
        elif part.startswith("\\texttt{") and part.endswith("}"):
            idx = len(saved)
            saved.append(part)
            staged.append(f"\x00TOK{idx}\x00")
        else:
            staged.append(part)
    converted = convert_plain_segment("".join(staged))
    return re.sub(r"\x00TOK(\d+)\x00", lambda m: saved[int(m.group(1))], converted)


def to_pdf_plain(text: str) -> str:
    """Produce an ASCII/plain-text PDF bookmark string for \\texorpdfstring."""
    s = text.replace("`", "").replace("&", "and")
    s = re.sub(r"\$([^$]+)\$", r"\1", s)
    s = s.replace("\\", "").replace("{", "").replace("}", "")
    return s.strip()


def pick_colspec(headers: list[str]) -> str:
    """Choose landscape longtable column widths tuned to the catalog tables."""
    ncols = len(headers)
    first = headers[0].strip()
    if ncols == 8:
        return "@{}P{1.48in}P{0.58in}C{0.46in}P{1.78in}P{0.50in}P{0.92in}P{2.80in}P{0.98in}@{}"
    if ncols == 5 and first == "Table #":
        return "@{}C{0.42in}C{0.50in}P{1.42in}P{2.30in}P{5.10in}@{}"
    if ncols == 4:
        return "@{}P{2.15in}P{2.65in}C{0.85in}P{4.15in}@{}"
    if ncols == 5:
        return "@{}P{3.80in}C{1.30in}C{1.30in}C{1.50in}C{1.30in}@{}"
    w = 9.4 / max(1, ncols)
    return "@{}" + "".join([f"P{{{w:.2f}in}}" for _ in range(ncols)]) + "@{}"


def emit_table(lines: list[str], idx: int) -> tuple[list[str], int]:
    """Convert a Markdown pipe table starting at idx into a styled longtable."""
    rows: list[list[str]] = []
    while idx < len(lines):
        stripped = lines[idx].strip()
        if not (stripped.startswith("|") and stripped.endswith("|")):
            break
        cells = [c.strip() for c in stripped.strip("|").split("|")]
        rows.append(cells)
        idx += 1

    if len(rows) < 2:
        return ["\n".join(md_inline_to_latex(l) for l in rows[0])], idx

    headers = rows[0]
    data_rows = [
        r for r in rows[2:]
        if not all(set(c) <= {"-", ":"} for c in r)
    ]

    colspec = pick_colspec(headers)
    ncols = len(headers)
    hdr_tex = " & ".join(
        "\\textcolor{CRMBlue}{\\textbf{" + md_inline_to_latex(h) + "}}"
        for h in headers
    )

    out: list[str] = [
        "{",
        "\\footnotesize",
        f"\\begin{{longtable}}{{{colspec}}}",
        "\\toprule",
        hdr_tex + " \\\\",
        "\\midrule",
        "\\endfirsthead",
        f"\\multicolumn{{{ncols}}}{{@{{}}l}}{{\\scriptsize\\itshape\\textcolor{{CRMBlue}}{{Table continued from previous page}}}} \\\\[0.2em]",
        "\\toprule",
        hdr_tex + " \\\\",
        "\\midrule",
        "\\endhead",
        "\\midrule",
        f"\\multicolumn{{{ncols}}}{{@{{}}r}}{{\\scriptsize\\itshape\\textcolor{{CRMBlue}}{{Continued on next page}}}} \\\\",
        "\\endfoot",
        "\\bottomrule",
        "\\endlastfoot",
    ]

    for r_i, row in enumerate(data_rows):
        padded = row + [""] * max(0, ncols - len(row))
        cells_tex = [md_inline_to_latex(c) for c in padded[:ncols]]
        out.append(" & ".join(cells_tex) + " \\\\")
        if r_i + 1 < len(data_rows):
            out.append("\\rowsep")

    out.extend(["\\end{longtable}", "}"])
    return out, idx


def convert_markdown_body(md_text: str) -> str:
    """Convert full Markdown body to structured LaTeX document content."""
    lines = md_text.splitlines()
    out: list[str] = []
    i = 0

    # Title block from H1 + contiguous bold metadata lines
    if i < len(lines) and lines[i].startswith("# "):
        title = md_inline_to_latex(lines[i][2:].strip())
        i += 1
        while i < len(lines) and not lines[i].strip():
            i += 1
        meta_lines: list[str] = []
        while i < len(lines) and lines[i].strip().startswith("**"):
            meta_lines.append(md_inline_to_latex(lines[i].strip().rstrip()))
            i += 1
        out.append("\\begin{center}")
        out.append(f"{{\\Large\\bfseries\\color{{CRMBlue}} {title}}}\\\\[0.55em]")
        out.append("{\\small")
        out.append(" \\\\\n".join(meta_lines))
        out.append("}")
        out.append("\\end{center}")
        out.append("\\vspace{0.3em}")
        out.append("\\hrule")
        out.append("\\vspace{0.6em}")
        out.append("{\\small\\tableofcontents}")
        out.append("\\vspace{0.6em}")

    while i < len(lines):
        raw = lines[i]
        stripped = raw.strip()

        if not stripped:
            out.append("")
            i += 1
            continue

        if stripped == "---":
            out.append("\\vspace{0.25em}")
            i += 1
            continue

        if stripped.startswith("## "):
            heading_raw = stripped[3:].strip()
            heading_tex = md_inline_to_latex(heading_raw)
            heading_plain = to_pdf_plain(heading_raw)
            if any(heading_raw.startswith(p) for p in ("3.", "4.", "5.", "6.", "7.")):
                out.append("\\clearpage")
            out.append(
                f"\\section*{{\\textcolor{{CRMBlue}}{{\\texorpdfstring{{{heading_tex}}}{{{heading_plain}}}}}}}"
            )
            out.append(f"\\phantomsection\\addcontentsline{{toc}}{{section}}{{\\texorpdfstring{{{heading_tex}}}{{{heading_plain}}}}}")
            i += 1
            continue

        if stripped.startswith("### "):
            sub_raw = stripped[4:].strip()
            sub_tex = md_inline_to_latex(sub_raw)
            sub_plain = to_pdf_plain(sub_raw)
            out.append(
                f"\\subsection*{{\\textcolor{{CRMBlue}}{{\\texorpdfstring{{{sub_tex}}}{{{sub_plain}}}}}}}"
            )
            out.append(f"\\phantomsection\\addcontentsline{{toc}}{{subsection}}{{\\texorpdfstring{{{sub_tex}}}{{{sub_plain}}}}}")
            i += 1
            continue

        if stripped.startswith("|") and stripped.endswith("|"):
            tbl_tex, i = emit_table(lines, i)
            out.extend(tbl_tex)
            continue

        if stripped.startswith("> "):
            q_lines: list[str] = []
            while i < len(lines) and lines[i].strip().startswith("> "):
                q_lines.append(md_inline_to_latex(lines[i].strip()[2:].strip()))
                i += 1
            out.append("\\begin{quote}\\small")
            out.append(" ".join(q_lines))
            out.append("\\end{quote}")
            continue

        if re.match(r"^\d+\.\s+", stripped):
            out.append("\\begin{enumerate}[leftmargin=1.8em,itemsep=0.25em]")
            while i < len(lines) and re.match(r"^\d+\.\s+", lines[i].strip()):
                item_txt = re.sub(r"^\d+\.\s+", "", lines[i].strip())
                out.append("  \\item " + md_inline_to_latex(item_txt))
                i += 1
            out.append("\\end{enumerate}")
            continue

        if stripped.startswith("- "):
            out.append("\\begin{itemize}[leftmargin=1.5em,itemsep=0.2em]")
            while i < len(lines) and lines[i].strip().startswith("- "):
                item_txt = lines[i].strip()[2:].strip()
                out.append("  \\item " + md_inline_to_latex(item_txt))
                i += 1
            out.append("\\end{itemize}")
            continue

        # Standard paragraph
        para_lines: list[str] = []
        while i < len(lines):
            cur = lines[i].strip()
            if (
                not cur
                or cur == "---"
                or cur.startswith("## ")
                or cur.startswith("### ")
                or cur.startswith("> ")
                or cur.startswith("- ")
                or (cur.startswith("|") and cur.endswith("|"))
                or re.match(r"^\d+\.\s+", cur)
            ):
                break
            para_lines.append(md_inline_to_latex(cur))
            i += 1
        out.append(" ".join(para_lines) + "\n")

    return "\n".join(out)


def build_tex_document(body_tex: str) -> str:
    """Wrap generated LaTeX body in monograph-matched landscape preamble."""
    preamble = r"""\documentclass[10pt]{article}
\input{glyphtounicode}
\pdfgentounicode=1
\usepackage[utf8]{inputenc}
\DeclareUnicodeCharacter{00A7}{\S}
\DeclareUnicodeCharacter{00B2}{\textsuperscript{2}}
\DeclareUnicodeCharacter{00B7}{\ensuremath{\cdot}}
\DeclareUnicodeCharacter{03B5}{\ensuremath{\varepsilon}}
\DeclareUnicodeCharacter{2013}{--}
\DeclareUnicodeCharacter{2014}{---}
\DeclareUnicodeCharacter{2081}{\textsubscript{1}}
\DeclareUnicodeCharacter{2082}{\textsubscript{2}}
\DeclareUnicodeCharacter{2124}{\ensuremath{\mathbb{Z}}}
\usepackage[T1]{fontenc}
\usepackage[landscape,letterpaper,left=0.40in,right=0.40in,top=0.52in,bottom=0.55in]{geometry}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\IfFileExists{newpxtext.sty}{%
  \usepackage{newpxtext}%
  \usepackage{newpxmath}%
}{%
  \usepackage[sc]{mathpazo}%
  \usepackage{tgpagella}%
}
\IfFileExists{zi4.sty}{%
  \usepackage[scaled=0.88]{zi4}%
}{%
  \usepackage[scale=0.84]{tgcursor}%
}
\usepackage{microtype}
\usepackage{booktabs,longtable,array,colortbl}
\usepackage{enumitem}
\usepackage{xcolor}
\definecolor{CRMBlue}{HTML}{1B365D}
\definecolor{RowRule}{gray}{0.84}
\usepackage{fancyhdr}
\usepackage[colorlinks=true,linkcolor=CRMBlue,citecolor=CRMBlue,urlcolor=CRMBlue]{hyperref}
\usepackage{bookmark}

\newcolumntype{P}[1]{>{\raggedright\arraybackslash\hspace{0pt}}p{#1}}
\newcolumntype{C}[1]{>{\centering\arraybackslash\hspace{0pt}}p{#1}}
\setlength{\tabcolsep}{3.5pt}
\renewcommand{\arraystretch}{1.18}
\setlength{\LTpre}{4pt}
\setlength{\LTpost}{6pt}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.45em}
\emergencystretch=2em
\hbadness=10000
\vbadness=10000

\newcommand{\Eff}{\mathcal{E}\mathrm{ff}}
\newcommand{\Prism}{\mathbf{\Delta}}
\newcommand{\CohesiveQuad}{\Pi \dashv \mathrm{Disc} \dashv \Gamma \dashv \mathrm{Codisc}}
\providecommand{\sslash}{\mathbin{/\mkern-5mu/}}
\newcommand{\rowsep}{\arrayrulecolor{RowRule}\midrule\arrayrulecolor{black}}

\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\scriptsize\textcolor{CRMBlue}{Master Catalog of Technical Claims \& Foundational Grounding}}
\fancyhead[R]{\scriptsize\textcolor{CRMBlue}{\textit{Categorical Reverse Mathematics with Applications} --- James F. Walters}}
\fancyfoot[C]{\scriptsize\thepage}
\renewcommand{\headrulewidth}{0.4pt}
\renewcommand{\footrulewidth}{0pt}

\setcounter{tocdepth}{2}

\begin{document}
"""
    return preamble + "\n" + body_tex + "\n\\end{document}\n"


def main() -> int:
    if not MD_PATH.exists():
        print(f"ERROR: missing {MD_PATH}", file=sys.stderr)
        return 1

    if BUILD_DIR.exists():
        shutil.rmtree(BUILD_DIR)
    BUILD_DIR.mkdir(parents=True, exist_ok=True)

    md_text = MD_PATH.read_text(encoding="utf-8")
    body_tex = convert_markdown_body(md_text)
    full_tex = build_tex_document(body_tex)

    tex_file = BUILD_DIR / "technical_claims_foundations.tex"
    tex_file.write_text(full_tex, encoding="utf-8")

    cmd = [
        "pdflatex",
        "-interaction=nonstopmode",
        "-halt-on-error",
        tex_file.name,
    ]
    for pass_num in (1, 2):
        res = subprocess.run(
            cmd,
            cwd=BUILD_DIR,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        if res.returncode != 0:
            print(f"pdflatex failed on pass {pass_num}:", file=sys.stderr)
            print(res.stdout[-4000:], file=sys.stderr)
            print(res.stderr[-2000:], file=sys.stderr)
            return res.returncode

    built_pdf = BUILD_DIR / "technical_claims_foundations.pdf"
    if not built_pdf.exists():
        print("ERROR: expected PDF not created.", file=sys.stderr)
        return 1

    shutil.copy2(built_pdf, PDF_OUT)

    log_text = (BUILD_DIR / "technical_claims_foundations.log").read_text(
        encoding="utf-8", errors="replace"
    )
    pages_m = re.search(r"Output written on [^\n]*\((\d+)\s+pages?", log_text)
    pages = int(pages_m.group(1)) if pages_m else 0
    overfulls = re.findall(r"Overfull \\hbox \(([0-9.]+)pt too wide\)[^\n]*", log_text)
    big_overfulls = [o for o in overfulls if float(o) > 5.0]

    print(f"Rendered PDF : {PDF_OUT}")
    print(f"Pages        : {pages}")
    print(f"Overfulls    : {len(overfulls)} total, {len(big_overfulls)} > 5.0pt")
    if big_overfulls:
        for line in log_text.splitlines():
            m = re.search(r"Overfull \\hbox \(([0-9.]+)pt too wide\)", line)
            if m and float(m.group(1)) > 5.0:
                print("  WARN:", line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
