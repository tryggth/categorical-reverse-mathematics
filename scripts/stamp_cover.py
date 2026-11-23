#!/usr/bin/env python3
"""Stamp the 2-page Royal Octavo cover onto root categorical_reverse_mathematics.pdf."""
import pathlib
import shutil
import struct
import subprocess
import sys
import tempfile

import pikepdf

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"
DOCS_PDF = DOCS / "categorical_reverse_mathematics.pdf"
ROOT_PDF = ROOT / "categorical_reverse_mathematics.pdf"
COVER_ASSET = DOCS / "assets" / "cover.jpg"
ROOT_COVER = ROOT / "cover.jpg"

SOF_MARKERS = {
    0xC0, 0xC1, 0xC2, 0xC3,
    0xC5, 0xC6, 0xC7,
    0xC9, 0xCA, 0xCB,
    0xCD, 0xCE, 0xCF,
}


def read_jpeg_size(path: pathlib.Path) -> tuple[int, int]:
    """Read (width, height) pixels directly from a JPEG header using struct."""
    data = path.read_bytes()
    if len(data) < 4 or data[:2] != b"\xff\xd8":
        raise ValueError(f"{path} is not a valid JPEG file")
    pos = 2
    n = len(data)
    while pos < n:
        while pos < n and data[pos] != 0xFF:
            pos += 1
        while pos < n and data[pos] == 0xFF:
            pos += 1
        if pos >= n:
            break
        marker = data[pos]
        pos += 1
        if marker in (0xD8, 0xD9, 0x01) or (0xD0 <= marker <= 0xD7):
            continue
        if marker == 0xDA:  # Start of Scan (entropy data follows)
            break
        if pos + 2 > n:
            break
        (seg_len,) = struct.unpack(">H", data[pos : pos + 2])
        if seg_len < 2 or pos + seg_len > n:
            raise ValueError(f"Malformed JPEG segment length at offset {pos}")
        if marker in SOF_MARKERS:
            if pos + 7 > n:
                raise ValueError("Truncated JPEG SOF segment")
            height, width = struct.unpack(">HH", data[pos + 3 : pos + 7])
            return width, height
        pos += seg_len
    raise ValueError(f"Could not find SOF frame dimensions in {path}")


def build_cover_pdf(cover_path: pathlib.Path, out_pdf: pathlib.Path) -> None:
    """Compile a 2-page Royal Octavo (6.14in x 9.21in) cover+verso PDF in a temp dir."""
    width, height = read_jpeg_size(cover_path)
    trim_ratio = 6.14 / 9.21
    scale_opt = r"height=\paperheight" if (width / height) > trim_ratio else r"width=\paperwidth"

    cover_tex = rf"""\documentclass[10pt]{{article}}
\usepackage[paperwidth=6.14in,paperheight=9.21in,margin=0pt]{{geometry}}
\usepackage{{graphicx,tikz}}
\pagestyle{{empty}}
\begin{{document}}
\thispagestyle{{empty}}%
\begin{{tikzpicture}}[remember picture,overlay]
  \node[inner sep=0pt] at (current page.center) {{\includegraphics[{scale_opt}]{{cover.jpg}}}};
\end{{tikzpicture}}%
\null\clearpage
\thispagestyle{{empty}}%
\null\clearpage
\end{{document}}
"""

    with tempfile.TemporaryDirectory(prefix="crm_cover_") as tmp:
        tmpdir = pathlib.Path(tmp)
        shutil.copy2(cover_path, tmpdir / "cover.jpg")
        tex_file = tmpdir / "cover_only.tex"
        tex_file.write_text(cover_tex, encoding="utf-8")
        for _pass in range(2):
            res = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", tex_file.name],
                cwd=tmpdir,
                capture_output=True,
                text=True,
            )
            if res.returncode != 0:
                tail = "\n".join(res.stdout.splitlines()[-25:])
                raise RuntimeError(f"pdflatex failed building cover_only.pdf:\n{tail}")
        built_pdf = tmpdir / "cover_only.pdf"
        if not built_pdf.exists():
            raise RuntimeError("cover_only.pdf was not produced by pdflatex")
        with pikepdf.open(built_pdf) as chk:
            if len(chk.pages) != 2:
                raise RuntimeError(f"Expected 2-page cover_only.pdf, got {len(chk.pages)} pages")
        shutil.copy2(built_pdf, out_pdf)


def stamp_root_pdf() -> int:
    """Prepend the 2-page cover onto root categorical_reverse_mathematics.pdf."""
    if ROOT_COVER.exists() and not COVER_ASSET.exists():
        COVER_ASSET.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT_COVER, COVER_ASSET)

    if not COVER_ASSET.exists():
        print("[stamp_cover] docs/assets/cover.jpg not present — keeping unstamped PDF")
        return 0

    if not DOCS_PDF.exists():
        print(f"[stamp_cover] Missing compiled monograph PDF: {DOCS_PDF}", file=sys.stderr)
        return 1

    with tempfile.TemporaryDirectory(prefix="crm_stamp_") as tmp:
        tmpdir = pathlib.Path(tmp)
        cover_pdf = tmpdir / "cover_only.pdf"
        merged_pdf = tmpdir / "merged.pdf"
        build_cover_pdf(COVER_ASSET, cover_pdf)

        with pikepdf.open(DOCS_PDF) as dst, pikepdf.open(cover_pdf) as src_cover:
            orig_pages = len(dst.pages)
            dst.pages.insert(0, src_cover.pages[0])
            dst.pages.insert(1, src_cover.pages[1])

            new_nums = pikepdf.Array([
                0,
                pikepdf.Dictionary(P="Cover"),
                1,
                pikepdf.Dictionary(P="IFC"),
            ])
            if "/PageLabels" in dst.Root and "/Nums" in dst.Root.PageLabels:
                old_nums = list(dst.Root.PageLabels.Nums)
                for i in range(0, len(old_nums), 2):
                    new_nums.append(int(old_nums[i]) + 2)
                    new_nums.append(old_nums[i + 1])
            else:
                new_nums.append(2)
                new_nums.append(pikepdf.Dictionary(S=pikepdf.Name("/D")))

            dst.Root.PageLabels = dst.make_indirect(pikepdf.Dictionary(Nums=new_nums))
            dst.save(merged_pdf)

        shutil.copy2(merged_pdf, ROOT_PDF)

    print(
        f"[stamp_cover] Stamped 2-page Royal Octavo cover onto {ROOT_PDF.name} "
        f"({orig_pages} -> {orig_pages + 2} pages; {DOCS_PDF.relative_to(ROOT)} kept unstamped)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(stamp_root_pdf())
