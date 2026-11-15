#!/usr/bin/env python3
"""Deterministic local verifier for Categorical Reverse Mathematics (TeX + Lean 4)."""
import argparse, pathlib, re, shutil, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"
TEX = DOCS / "categorical_reverse_mathematics.tex"
PDF = DOCS / "categorical_reverse_mathematics.pdf"
LEAN_DIR = ROOT / "HomotopyCRM"


def resolve_lake() -> str:
    """Resolve the `lake` executable via PATH or default ~/.elan/bin/lake."""
    which_lake = shutil.which("lake")
    if which_lake:
        return which_lake
    elan_lake = pathlib.Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.exists():
        return str(elan_lake)
    return "lake"

FORBIDDEN = [
    "Categorical Reverse Mathematics Research Group",
    "Categorical Foundations Press",
    "978-0-9999999",
    "quantum chaos",
    "Hilbert-Polya",
    "Hilbert--P\\'olya",
]

def strip_lean_comments(src: str) -> str:
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth == 0 and src[i:i+2] == "--":
            while i < n and src[i] != "\n":
                i += 1
        elif src[i:i+2] == "/-":
            depth += 1; i += 2
        elif depth > 0 and src[i:i+2] == "-/":
            depth -= 1; i += 2
        else:
            if depth == 0:
                out.append(src[i])
            i += 1
    return "".join(out)

def check_tex() -> list[str]:
    errs = []
    sync_res = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "sync_blueprint.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if sync_res.returncode != 0:
        errs.append("Blueprint out of sync:\n" + (sync_res.stdout + sync_res.stderr).strip())

    txt = TEX.read_text(encoding="utf-8")
    for bad in FORBIDDEN:
        if bad.lower() in txt.lower():
            errs.append(f"Forbidden string in .tex: {bad!r}")
    bibitems = set(re.findall(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}", txt))
    cited = set()
    for m in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", txt):
        for k in m.split(","):
            if k.strip():
                cited.add(k.strip())
    uncited = sorted(bibitems - cited)
    undef_cites = sorted(cited - bibitems)
    if uncited:
        errs.append(f"Uncited \\bibitem keys ({len(uncited)}): {uncited}")
    if undef_cites:
        errs.append(f"Undefined \\cite keys ({len(undef_cites)}): {undef_cites}")

    for cmd in [
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", TEX.name],
        ["makeindex", "categorical_reverse_mathematics.idx"],
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", TEX.name],
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", TEX.name],
    ]:
        if cmd[0] == "makeindex" and not (DOCS / "categorical_reverse_mathematics.idx").exists():
            continue
        r = subprocess.run(cmd, cwd=DOCS, capture_output=True, text=True)
        if r.returncode != 0:
            errs.append(f"Command failed ({' '.join(cmd)}):\n" + "\n".join(r.stdout.splitlines()[-25:]))
            return errs

    log = (DOCS / "categorical_reverse_mathematics.log").read_text(encoding="utf-8", errors="replace")
    for pat, label in [
        (r"^! .*", "LaTeX error"),
        (r"LaTeX Warning: Reference .* undefined", "Undefined reference"),
        (r"LaTeX Warning: Citation .* undefined", "Undefined citation"),
        (r"LaTeX Warning: There were undefined references", "Undefined refs summary"),
        (r"Overfull \\[hv]box .*", "Overfull box"),
    ]:
        hits = re.findall(pat, log, flags=re.MULTILINE)
        if hits:
            errs.append(f"{label} ({len(hits)}): {hits[:5]}")

    if not errs:
        if (ROOT / TEX.name).exists():
            shutil.copy2(TEX, ROOT / TEX.name)
        if (ROOT / PDF.name).exists():
            shutil.copy2(PDF, ROOT / PDF.name)
    return errs

def check_lean(run_build: bool = True) -> list[str]:
    errs = []
    if not (ROOT / "HomotopyCRM.lean").exists():
        errs.append("Missing root entry module HomotopyCRM.lean")
    checkdecls_file = ROOT / "CheckDecls.lean"
    if not checkdecls_file.exists():
        errs.append("Missing CheckDecls.lean blueprint checker")
    else:
        chk_raw = checkdecls_file.read_text(encoding="utf-8")
        chk_code = strip_lean_comments(chk_raw)
        for bad in FORBIDDEN:
            if bad.lower() in chk_raw.lower():
                errs.append(f"Forbidden string in CheckDecls.lean: {bad!r}")
        if re.search(r"\bsorry\b", chk_code):
            errs.append("CheckDecls.lean: contains 'sorry'")
        if re.search(r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+)*axiom\b", chk_code):
            errs.append("CheckDecls.lean: contains custom 'axiom'")
        if re.search(r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+)*opaque\b", chk_code):
            errs.append("CheckDecls.lean: contains 'opaque'")
    decls_file = ROOT / "blueprint" / "lean_decls"
    if not decls_file.exists() or not [ln for ln in decls_file.read_text(encoding="utf-8").splitlines() if ln.strip()]:
        errs.append("Missing or empty blueprint/lean_decls")
    files = sorted(LEAN_DIR.glob("*.lean"))
    prod = [f for f in files if f.name != "Basic.lean"]
    if not prod:
        errs.append("No production Lean modules found in HomotopyCRM/")
        return errs
    for f in files:
        raw = f.read_text(encoding="utf-8")
        code = strip_lean_comments(raw)
        if re.search(r"\bsorry\b", code):
            errs.append(f"{f.name}: contains 'sorry'")
        if re.search(r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+)*axiom\b", code):
            errs.append(f"{f.name}: contains custom 'axiom'")
        if re.search(r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+)*opaque\b", code):
            errs.append(f"{f.name}: contains 'opaque'")
        if f in prod:
            if "namespace Checks" not in code or "#print axioms" not in code:
                errs.append(f"{f.name}: missing 'namespace Checks' or '#print axioms' gate")
    if run_build:
        r = subprocess.run([resolve_lake(), "build", "HomotopyCRM", "checkdecls"], cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            errs.append("lake build HomotopyCRM checkdecls failed:\n" + "\n".join((r.stdout + "\n" + r.stderr).splitlines()[-30:]))
        elif decls_file.exists():
            rc = subprocess.run([resolve_lake(), "exe", "checkdecls", str(decls_file)], cwd=ROOT, capture_output=True, text=True)
            if rc.returncode != 0:
                errs.append("lake exe checkdecls failed:\n" + "\n".join((rc.stdout + "\n" + rc.stderr).splitlines()[-20:]))
    print(f"Lean modules checked: {len(prod)} production modules ({sum(len(f.read_text().splitlines()) for f in prod)} lines)")
    return errs

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true", help="Run both TeX/Index and full Lean lake build gates")
    ap.add_argument("--tex-only", action="store_true", help="Run TeX/Bibliography/Index/Overfull gates only")
    ap.add_argument("--lean-only", action="store_true", help="Run Lean 4 static 4-layer and build gates only")
    ap.add_argument("--no-build", action="store_true", help="Skip invoking `lake build` inside the Lean gate")
    args = ap.parse_args()

    run_tex = not args.lean_only
    run_lean = args.full or args.lean_only

    errs = []
    if run_tex:
        errs.extend(check_tex())
    if run_lean:
        errs.extend(check_lean(run_build=not args.no_build))
    if errs:
        print("VERIFICATION FAILED:")
        for e in errs:
            print(" -", e)
        return 1
    if run_tex:
        pages = "?"
        log = (DOCS / "categorical_reverse_mathematics.log").read_text(encoding="utf-8", errors="replace")
        m = re.search(r"Output written on .*?\((\d+) pages", log)
        if m:
            pages = m.group(1)
        print(f"VERIFICATION PASSED: {TEX.name} ({len(TEX.read_text().splitlines())} lines, {pages} pages, 0 errors, 0 overfull boxes, 0 uncited bibitems).")
    if run_lean:
        print("VERIFICATION PASSED: HomotopyCRM Lean 4 gate.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
