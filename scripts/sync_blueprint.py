#!/usr/bin/env python3
"""Synchronize Lean blueprint files and references.bib from docs/categorical_reverse_mathematics.tex."""
import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"
TEX_PATH = DOCS / "categorical_reverse_mathematics.tex"
LEAN_DECLS_PATH = ROOT / "blueprint" / "lean_decls"
CONTENT_PATH = ROOT / "blueprint" / "src" / "content.tex"
BIB_PATH = ROOT / "references.bib"


def _resolve_input_target(target: str) -> pathlib.Path:
    rel = target.strip()
    if not rel.endswith(".tex"):
        rel = rel + ".tex"
    for base in (DOCS, ROOT):
        cand = (base / rel).resolve()
        if cand.exists():
            return cand
    raise FileNotFoundError(f"Could not resolve \\input{{{target}}} under {DOCS} or {ROOT}")


def expand_tex_inputs(text: str) -> str:
    """Inline CWD-safe \\IfFileExists{...}{\\input{...}}{\\input{...}} and \\input{...} modules (excluding glyphtounicode)."""
    cond_pat = re.compile(
        r"\\IfFileExists\{[^}]+\}\{\\input\{([^}]+)\}\}\{\\input\{([^}]+)\}\}"
    )

    def _sub_cond(m: re.Match[str]) -> str:
        p = _resolve_input_target(m.group(1))
        return expand_tex_inputs(p.read_text(encoding="utf-8"))

    text = cond_pat.sub(_sub_cond, text)

    inp_pat = re.compile(r"(?<!%)\\input\{([^}]+)\}")

    def _sub_inp(m: re.Match[str]) -> str:
        name = m.group(1).strip()
        if name == "glyphtounicode":
            return m.group(0)
        p = _resolve_input_target(name)
        return expand_tex_inputs(p.read_text(encoding="utf-8"))

    return inp_pat.sub(_sub_inp, text)


def skip_ws_and_comments(text: str, pos: int) -> int:
    n = len(text)
    while pos < n:
        if text[pos] in " \t\r\n":
            pos += 1
        elif text[pos] == "%" and (pos == 0 or text[pos - 1] != "\\"):
            nl = text.find("\n", pos)
            pos = n if nl == -1 else nl + 1
        else:
            break
    return pos


def read_brace_group(text: str, pos: int) -> tuple[str, int] | None:
    pos = skip_ws_and_comments(text, pos)
    if pos >= len(text) or text[pos] != "{":
        return None
    depth = 0
    i = pos
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == "\\" and i + 1 < n:
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[pos + 1 : i], i + 1
        i += 1
    return None


def replace_macro_calls(text: str, macro: str, nargs: int, replacer) -> str:
    """Replace all `\\<macro>{arg1}...{argN}` respecting balanced braces and macro name boundaries."""
    out = []
    i = 0
    n = len(text)
    mlen = len(macro)
    while i < n:
        idx = text.find(macro, i)
        if idx == -1:
            out.append(text[i:])
            break
        after = idx + mlen
        if after < n and (text[after].isalpha() or text[after] == "@"):
            out.append(text[i : after])
            i = after
            continue
        cur = after
        args = []
        ok = True
        for _ in range(nargs):
            res = read_brace_group(text, cur)
            if res is None:
                ok = False
                break
            arg, cur = res
            args.append(arg)
        if not ok:
            out.append(text[i : after])
            i = after
            continue
        out.append(text[i:idx])
        out.append(replacer(args))
        # Swallow a trailing comment-continuity `%` immediately after a stripped macro if replacer returned ""
        if replacer(args) == "" and cur < n and text[cur] == "%":
            cur += 1
        i = cur
    return "".join(out)


def extract_lean_decls(content: str) -> str:
    """Extract all `\\lean{...}` declarations inside `\\leanok`-verified environments of content.tex."""
    decls = set()
    env_pat = re.compile(
        r"\\begin\{(theorem|proposition|lemma|definition|remark|conjecture|principle|problem)\}(.*?)\\end\{\1\}",
        flags=re.S,
    )
    for m in env_pat.finditer(content):
        block = m.group(2)
        if not re.search(r"\\leanok(?![a-zA-Z@])", block):
            continue
        i = 0
        n = len(block)
        macro = r"\lean"
        while i < n:
            idx = block.find(macro, i)
            if idx == -1:
                break
            after = idx + len(macro)
            if after < n and (block[after].isalpha() or block[after] == "@"):
                i = after
                continue
            res = read_brace_group(block, after)
            if res is None:
                i = after
                continue
            arg, i = res
            for piece in arg.split(","):
                name = piece.strip()
                if name:
                    decls.add(name)
    return "\n".join(sorted(decls)) + ("\n" if decls else "")


def extract_bib(body: str) -> str:
    m = re.search(
        r"\\begin\{thebibliography\}\{[^}]*\}(.*?)\\end\{thebibliography\}",
        body,
        flags=re.S,
    )
    if not m:
        return ""
    bib_body = m.group(1)
    matches = list(re.finditer(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}", bib_body))
    entries = []
    for k, match in enumerate(matches):
        key = match.group(1).strip()
        start = match.end()
        end = matches[k + 1].start() if k + 1 < len(matches) else len(bib_body)
        raw = bib_body[start:end]
        cleaned = raw.replace(r"\allowbreak", "")
        cleaned = re.sub(r"\s+", " ", cleaned).strip()
        entries.append(f"@misc{{{key},\n  note = {{{cleaned}}}\n}}\n")
    return "\n".join(entries)


def replace_float_block(pattern: str, kind: str, text: str) -> str:
    def _sub(match: re.Match[str]) -> str:
        block = match.group(0)
        labels = "".join(f"\\label{{{lbl}}}" for lbl in re.findall(r"\\label\{([^}]+)\}", block))
        return (
            f"\\begin{{center}}\\emph{{[{kind} omitted in blueprint edition; "
            f"see Royal Octavo monograph PDF.]}}{labels}\\end{{center}}"
        )

    return re.sub(pattern, _sub, text, flags=re.S)


def transform_content(body: str) -> str:
    text = body

    # Promote the section-level Ch. 1 §1.6 Lean annotation to a formal theorem node for leanblueprint.
    sec_pat = re.compile(
        r"\\section\{(?:\\texorpdfstring\{Pure Axiom-of-Infinity Residua in \$\\mathbf\{FinSet\}\$\}\{Pure Axiom-of-Infinity Residua in FinSet\}|Pure Axiom-of-Infinity Residua in \$\\mathbf\{FinSet\}\$)\}"
        r"\\label\{sec:finset-infinity\}%?\s*\\lean\{([^}]+)\}%?"
    )

    def _promote_finset(m: re.Match[str]) -> str:
        decls = m.group(1).strip()
        return (
            r"\section{Pure Axiom-of-Infinity Residua in $\mathbf{FinSet}$}\label{sec:finset-infinity}"
            "\n\n"
            r"\begin{theorem}[Pure Axiom-of-Infinity Residua in $\mathbf{FinSet}$]\label{thm:finset-infinity-residua}%"
            "\n"
            f"\\lean{{{decls}}}%\n"
            r"\leanok%"
            "\n"
            r"\uses{def:comparison-triple,def:residuum}%"
            "\n"
            r"Inside $\mathbf{FinSet}$, although $\mathrm{LEM}$ and External Choice ($\mathrm{AC}$) hold unconditionally, "
            r"withholding a Natural Numbers Object ($\mathrm{NNO}$) along Axis~III precipitates three non-trivial structural "
            r"residuums: the profinite lasso phantom $\widehat{\mathbb{N}}_{\mathrm{lasso}} \twoheadrightarrow \widehat{\mathbb{Z}}$, "
            r"the Dedekind/Pigeonhole versus nominal $\mathbb{A}$ finite-support crossing point, and the biproduct-tail "
            r"cokernel $\prod_{\mathbb{N}} A / \bigoplus_{\mathbb{N}} A \neq 0$."
            "\n"
            r"\end{theorem}"
        )

    text, n_promoted = sec_pat.subn(_promote_finset, text, count=1)
    if n_promoted != 1:
        raise RuntimeError(f"Expected 1 sec:finset-infinity section promotion, found {n_promoted}")

    # Replace floats and inline summary tables before balanced-brace macro stripping.
    text = replace_float_block(r"\\begin\{figure\}(?:\[[^\]]*\])?.*?\\end\{figure\}", "Figure", text)
    text = replace_float_block(r"\\begin\{table\}(?:\[[^\]]*\])?.*?\\end\{table\}", "Table", text)
    text = re.sub(
        r"(?:\\medskip\s*)?\\noindent\{\\scriptsize.*?\\begin\{(?:xltabular|tabularx)\}.*?\\end\{(?:xltabular|tabularx)\}\\par\}",
        r"\\begin{center}\\emph{[Summary ledger table omitted in blueprint edition; see Royal Octavo monograph PDF.]}\\end{center}",
        text,
        flags=re.S,
    )

    # Unwrap \texorpdfstring{A}{B} -> A
    text = replace_macro_calls(text, r"\texorpdfstring", 2, lambda args: args[0])

    # Strip monograph typography/index/running-head macros
    for macro, nargs in [
        (r"\index", 1),
        (r"\chapterepigraph", 2),
        (r"\sectionepigraph", 2),
        (r"\chaptermark", 1),
        (r"\markboth", 2),
        (r"\addcontentsline", 3),
        (r"\bookmarksetup", 1),
        (r"\setcounter", 2),
    ]:
        text = replace_macro_calls(text, macro, nargs, lambda _args: "")

    text = re.sub(r"\\begin\{(enumerate|itemize)\}\[[^\]]*\]", r"\\begin{\1}", text)
    text = text.replace(r"\allowbreak", "")
    text = text.replace(r"\backmatter", "")
    text = text.replace(r"\printindex", "")
    text = re.sub(r"\n{3,}", "\n\n", text).strip() + "\n"
    return text


def build_outputs() -> dict[pathlib.Path, str]:
    src = expand_tex_inputs(TEX_PATH.read_text(encoding="utf-8"))
    main_idx = src.find(r"\mainmatter")
    end_idx = src.rfind(r"\end{document}")
    if main_idx == -1 or end_idx == -1 or end_idx <= main_idx:
        raise RuntimeError("Could not locate \\mainmatter ... \\end{document} span in LaTeX source")
    body = src[main_idx + len(r"\mainmatter") : end_idx]

    bib = extract_bib(body)
    content = transform_content(body)
    lean_decls = extract_lean_decls(content)
    return {
        LEAN_DECLS_PATH: lean_decls,
        BIB_PATH: bib,
        CONTENT_PATH: content,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="Fail if generated blueprint files differ from disk")
    args = ap.parse_args()

    outputs = build_outputs()
    if args.check:
        stale = []
        for path, expected in outputs.items():
            if not path.exists() or path.read_text(encoding="utf-8") != expected:
                stale.append(str(path.relative_to(ROOT)))
        if stale:
            print("Blueprint files out of sync (run `python3 scripts/sync_blueprint.py`):", file=sys.stderr)
            for s in stale:
                print(f" - {s}", file=sys.stderr)
            return 1
        decls_count = len([ln for ln in outputs[LEAN_DECLS_PATH].splitlines() if ln.strip()])
        print(f"Blueprint sync check PASSED ({decls_count} Lean declarations in blueprint/lean_decls).")
        return 0

    for path, data in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(data, encoding="utf-8")
    decls_count = len([ln for ln in outputs[LEAN_DECLS_PATH].splitlines() if ln.strip()])
    bib_count = outputs[BIB_PATH].count("@misc{")
    print(f"Generated blueprint files: {decls_count} Lean decls, {bib_count} BibTeX entries.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
