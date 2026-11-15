# Categorical Reverse Mathematics with Applications: The Structure of Necessity

[![Build Monograph PDF](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/book.yml/badge.svg?branch=main)](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/book.yml)
[![Build & Verify HomotopyCRM Lean 4](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/lean.yml)
[![Compile Blueprint & Docs](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/blueprint.yml/badge.svg?branch=main)](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/blueprint.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24238087.svg)](https://doi.org/10.5281/zenodo.24238087)
[![Download Monograph PDF (Latest)](https://img.shields.io/badge/Monograph_PDF-Latest-1B365D)](https://github.com/tryggth/categorical-reverse-mathematics/releases/latest/download/categorical_reverse_mathematics.pdf)
[![Lean 4 v4.28.0](https://img.shields.io/badge/Lean_4-v4.28.0-blue)](lean-toolchain)

**Author:** James F. Walters (Port Townsend, Washington)  
**Edition:** First Edition (November 2026)  
**Archival DOI (Zenodo):** [`10.5281/zenodo.24238087`](https://doi.org/10.5281/zenodo.24238087) (All versions Concept DOI: [`10.5281/zenodo.24238086`](https://doi.org/10.5281/zenodo.24238086))  
**Licenses:** CC BY 4.0 (Monograph) & Apache 2.0 (Lean 4 Formalization)  
**MSC 2020:** `18B25` (Topoi), `03B30` (Foundations & Reverse Mathematics), `03G30` (Categorical Logic), `18N60` ($\infty$-Categories), `18N70` ($(\infty,\infty)$-Categories), `68V15` (Formal Proof in Lean 4)

> **Live Editions & Formal Verification Portal:**  
> [**Download Current PDF (GitHub Release — 152 pp., Royal Octavo)**](https://github.com/tryggth/categorical-reverse-mathematics/releases/latest/download/categorical_reverse_mathematics.pdf) · [**GitHub Pages PDF**](https://tryggth.github.io/categorical-reverse-mathematics/categorical_reverse_mathematics.pdf) · [**Zenodo Archive**](https://doi.org/10.5281/zenodo.24238087) · [**Interactive Web Blueprint**](https://tryggth.github.io/categorical-reverse-mathematics/blueprint/) · [**Dependency Graph**](https://tryggth.github.io/categorical-reverse-mathematics/blueprint/dep_graph_document.html) · [**Lean 4 API Docs**](https://tryggth.github.io/categorical-reverse-mathematics/docs/)

---

## Overview

*Categorical Reverse Mathematics with Applications: The Structure of Necessity* develops a structural, geometric theory of deductive strength. Classical reverse mathematics calibrates theorems by comparing syntactic subsystems of second-order arithmetic over $\mathsf{RCA}_0$; **Categorical Reverse Mathematics (CRM)** measures foundational necessity directly inside the $2$-category $\mathbf{Doct}$ of **categorical doctrines**—structured classes of categorical universes such as Boolean topoi, Grothendieck topoi, elementary topoi, $(\infty,1)$-topoi, $(\infty,\infty)$-categories, and nominal/realizability universes—by tracking the structural obstructions that remain when an axiom is withheld.

Given a **doctrinal comparison triple**
$$\mathfrak{T} = (\mathcal{D}_0 \supseteq \mathcal{D}_1,\; \kappa : \Phi \Rightarrow \Psi) \in \mathrm{Dom}(\mathrm{Res}),$$
the fundamental invariant $\mathrm{Res}(\mathfrak{T})$ captures the *exact mathematical gap* separating a theorem $\Psi$ from a weaker principle $\Phi$ across **Five Foundational Coordinate Axes**:

1. **Axis I — Choice / Splitting:** Local versus external splitting, $\mathsf{AC}$, $\mathsf{DC}_\omega$, $\mathsf{COSHEP}$, $\mathsf{WISC}$, $\mathsf{IBPI}$, and $\mathsf{IDC}$.
2. **Axis II — Constructive Logic:** Excluded middle, Diaconescu's theorem, subobject classifier geometries, Kleene realizability, and Lawvere–Tierney topologies.
3. **Axis III — Arithmetic Infinity:** $\mathbf{FinSet}$ versus natural numbers objects ($\mathrm{NNO}$), profinite lasso completions, and $\delta$-ring relative perfection.
4. **Axis IV — Characteristic / $p$-Torsion:** Algebraic torsion obstructions ($R_2 = \mathbb{Z}[\eta]/(2\eta,\eta^2)$ vs.\ $\texttt{DualInt} = \mathbb{Z}[\varepsilon]/(\varepsilon^2)$), $2$-torsion Witt lift torsors, and cubical/simplicial boundary cycles.
5. **Axis V — Directional Invertibility:** Coinductive versus inductive equivalences in directed $(\infty,\infty)$-categories, ordinal-rank completeness, and Postnikov phantom towers.

Two structural principles organize the treatise:

- **Base–Fiber Conservation:** Foundational strength is conserved across geometric morphisms $f : \mathcal{E} \to \mathcal{S}$ and doctrinal adjunctions (quantified via the 5-term Leray–Serre sequence, Milnor $\varprojlim^1$, and double-solvent collapses).
- **The Anchor-Witness Covenant:** High-altitude machinery is tethered throughout to five concrete witnesses:
  1. The **odd-finset parity torsor** $[\mathcal{T}_{\mathrm{odd}}] \neq 0 \in H^1(\mathbf{Nom}; \mathrm{EvenFinset})$ in Schanuel's nominal topos $\mathbf{Nom} = \mathbf{Cont}(\mathrm{Sym}(\mathbb{N}))$ (Ch. 6);
  2. The **$2$-torsion $\delta$-ring** $R_2 = \mathbb{Z}[\eta]/(2\eta,\eta^2)$ versus dual integers `DualInt` $= \mathbb{Z}[\varepsilon]/(\varepsilon^2)$ and slice relative perfection $A_{\mathrm{perf}} = \varinjlim_\phi A$ (Ch. 3);
  3. The **step-product directed category** $\mathcal{Q} \subset \prod_k \mathcal{A}_k$ on $[1] = \{0 < 1\}$ supporting a pure Postnikov phantom $X_\bullet \in RL(\mathcal{Q}) \setminus \mathcal{Q}$ (Ch. 5);
  4. The **punctured facet-cycle complex** $F_n = \partial\Delta^{n-1}$ obstructing directed cubical $n$-amalgamation for $n \ge 3$ while $n = 2$ splits cleanly (Ch. 6);
  5. The **Cantor tail quotient** $\mathcal{Q}_{E_0} = 2^{\mathbb{N}}/E_0$, the parity torsor $E_0^{\mathrm{even}}$, and $\mathrm{UHF}(2^\infty)$ $C^*$-moduli classifying exotic $\mathbb{R}^4$'s (Ch. 4).

This repository contains the complete LaTeX source for the 152-page Royal Octavo ($6.14\,\mathrm{in} \times 9.21\,\mathrm{in}$) monograph **and** the companion Lean 4 / `mathlib4` formalization library `HomotopyCRM` (14,583 lines across 9 production modules, kernel-verified under a 4-layer gate with 0 `sorry` and 0 custom axioms), synchronized via a `leanblueprint` + `checkdecls` + `doc-gen4` pipeline linking prose theorems directly to checked Lean 4 declarations.

---

## Monograph Structure

- **Frontmatter:** Half-Title, Title Page, Cataloging & Machine-Checked Colophon, Table of Contents, *Preface: Form, Symmetry, and the Geometry of Missing Axioms*, and *Notation and Symbol Glossary*.
- **Part I — Foundations of Necessity and the Residuum Calculus**
  - **Chapter 1:** *Foundations of Categorical Reverse Mathematics* (Doctrines, $\mathbf{Doct}$, $\mathrm{Dom}(\mathrm{Res})$, Five-Axis Map, Pure Axiom-of-Infinity Residua in $\mathbf{FinSet}$, Base–Fiber Conservation)
  - **Chapter 2:** *The Choice-Geometry Residuum Atlas and Cohomological Obstruction Theory* (Diaconescu, Freyd's countermodel, $\mathrm{COSHEP}$/$\mathrm{WISC}$/$\mathrm{IBPI}$/$\mathrm{IDC}$, higher Postnikov choice)
- **Part II — Iterative Fixed Points, $\delta$-Rings, and Infinite Towers**
  - **Chapter 3:** *Non-AC Theorem Lattices: Continuum Analysis, Pointfree Spatiality, and Homological Exactness* (Categorical "Big Five", Joyal $\delta$-rings, $R_2$ vs.\ $\texttt{DualInt}$, Nygaard filtration vs.\ relative slice perfection)
  - **Chapter 4:** *Base-Topos Variation, Geometric Morphisms, and the Base-Fiber Conservation Principle* (Axis 1/2 deformations, Leray sequence, $E_0$ Cantor tail residuum, $\mathrm{UHF}(2^\infty)$ $C^*$-moduli, exotic $\mathbb{R}^4$ unclassifiability)
- **Part III — Applications to $(\infty,\infty)$-Categories, Fraïssé Topoi, and Formal Verification**
  - **Chapter 5:** *Higher Categorical Reverse Mathematics in $(\infty, 1)$-Topoi, Univalent Foundations, and Postnikov Obstruction Towers* ($\mathrm{AC}_{n,m}$, 4-tier $(\infty,\infty)$-ladder, ordinal-rank completeness, step-product $\mathcal{Q}$ phantom disproving Conjecture C1, `ICaTT` semantics)
  - **Chapter 6:** *Site-Level Combinatorics, Realizability Topoi, and Computational Reverse Mathematics* (Kleene $\mathcal{E}\mathrm{ff}$, Kihara's five-rung atomic choice spectrum, Fraïssé atomic-topology escape, directed SAP, cubical $n$-amalgamation wall $n \ge 3$, Theorem 9B coinductive stream calibration)
  - **Chapter 7:** *Master Atlas of Open Problems, Methodological Blueprints, and Research Horizons* (Conjectures C1–C5, Fourteen Open Problems, Master Lean 4 Ledger, Master Reference Atlas, Epilogue, 49-entry Bibliography, Subject Index)

---

## Repository Layout

```text
.
├── .github/
│   └── workflows/
│       ├── blueprint.yml       # CI: Web Blueprint, Dependency Graph, API Docs, & GitHub Pages deploy
│       ├── book.yml            # CI: Royal Octavo PDF build + auto-update Latest GitHub Release PDF
│       ├── lean.yml            # CI: Cached Lean 4 build, blueprint sync, checkdecls, & 4-layer gate
│       └── release.yml         # CI: Tagged v* GitHub Release PDF + automated Zenodo new version
├── .gitignore                  # Ignores LaTeX aux/PDF build outputs, .lake/, site/, and secrets
├── .zenodo.json                # Published Zenodo record metadata (DOI 10.5281/zenodo.24238087)
├── CheckDecls.lean             # Lake executable checking all cited book declarations in HomotopyCRM
├── HomotopyCRM.lean            # Root Lean 4 entry module importing all HomotopyCRM submodules
├── HomotopyCRM/
│   ├── Basic.lean              # Shared 4-tier (∞,∞) localization ladder enum (19 lines)
│   ├── InfinityResiduum.lean   # Ch. 1 §1.6: Finite lassos, profinite Z_hat, Dedekind gap (949 lines)
│   ├── DeltaRingPerfection.lean# Ch. 3 §3.5: Joyal δ-rings, R2 vs DualInt, slice perfection (1,398 lines)
│   ├── BorelTailResiduum.lean  # Ch. 4 §4.5: E_0 Cantor tail quotient & E_0^even torsor (682 lines)
│   ├── OrdinalRankCompleteness.lean # Ch. 5 §5.7: Globular ordinal-rank completeness & Lali ceiling (1,774 lines)
│   ├── StepProductPhantom.lean # Ch. 5 §5.7: Step-product Q & Postnikov phantom X_• (3,505 lines)
│   ├── DirectedFraisseSAP.lean # Ch. 6 §6.7: Flow-convex embeddings & binary directed SAP (2,125 lines)
│   ├── NominalSimplicity.lean  # Ch. 6 §6.6: Sym(N) simplicity & odd-finset parity torsor (1,275 lines)
│   ├── CubicalAmalgamation.lean# Ch. 6 §6.7: n=2 vs n≥3 cubical amalgamation & F_n cycle (1,636 lines)
│   └── NominalICaTT.lean       # Ch. 6 §6.8: Theorem 9B DC_ω stream adequacy vs Nom failure (1,239 lines)
├── blueprint/
│   ├── lean_decls              # Auto-generated list of 89 cited Lean 4 declarations checked by checkdecls
│   └── src/                    # leanblueprint templates & synced content.tex
├── docs/
│   └── categorical_reverse_mathematics.tex   # Single LaTeX source of truth (3,136 lines)
├── home_page/
│   └── index.html              # GitHub Pages landing page linking PDF, Blueprint, Graph, & Docs
├── lake-manifest.json          # Exact pinned dependencies (mathlib4 v4.28.0, doc-gen4 v4.28.0)
├── lakefile.toml               # Lake project configuration for HomotopyCRM and checkdecls
├── lean-toolchain              # Pinned toolchain: leanprover/lean4:v4.28.0
├── references.bib              # Auto-generated BibTeX entries synced from bibliography
└── scripts/
    ├── publish_zenodo.py       # Zenodo draft/DOI/publish & version automation via REST API
    ├── sync_blueprint.py       # Deterministic LaTeX -> blueprint/ & references.bib sync (--check)
    └── verify_monograph.py     # Portable automated TeX + Blueprint + Lean 4 verification harness
```

---

## Building the Book (PDF from LaTeX Source)

Every push to `main` touching [`docs/categorical_reverse_mathematics.tex`](docs/categorical_reverse_mathematics.tex) compiles a fresh PDF, updates the [**Latest GitHub Release PDF**](https://github.com/tryggth/categorical-reverse-mathematics/releases/latest/download/categorical_reverse_mathematics.pdf), and republishes the [**GitHub Pages PDF**](https://tryggth.github.io/categorical-reverse-mathematics/categorical_reverse_mathematics.pdf) alongside the interactive blueprint. To compile `docs/categorical_reverse_mathematics.pdf` locally from source:

### Prerequisites (TeX Live)

On **Ubuntu / Debian**, install the verified lightweight TeX Live package set (uses `tgpagella`, `mathpazo`, `tgcursor`, `microtype`, `TikZ`/`tikz-cd`, and `makeindex` for exact 152-page, 0-overfull reproduction):

```bash
sudo apt-get update
sudo apt-get install -y --no-install-recommends \
  texlive-latex-base \
  texlive-latex-recommended \
  texlive-latex-extra \
  texlive-fonts-recommended \
  texlive-pictures \
  texlive-science \
  tex-gyre \
  lmodern
```

> **Note:** On **macOS**, install [MacTeX](https://www.tug.org/mactex/) (`brew install --cask mactex-no-gui`). If optional `texlive-fonts-extra` (`newpxtext`/`newpxmath`/`zi4`) is also installed, the preamble selects it automatically; otherwise it falls back cleanly to TeX Gyre Pagella + Pazo math + TeX Gyre Cursor.

### Recommended Verified Build

Run the verification script from the repository root (requires Python 3.9+):

```bash
python3 scripts/verify_monograph.py --tex-only
```

This runs the full three-pass `pdflatex` + `makeindex` pipeline inside `docs/` and automatically enforces:
- `0` forbidden strings and `0` undefined `\cite` or `\ref` keys;
- `100%` citation coverage (`0` uncited `\bibitem` entries across all 49 references);
- `0` LaTeX errors and `0` `Overfull \hbox` / `\vbox` warnings across all 150 Royal Octavo pages.

### Manual `pdflatex` + `makeindex` Build

```bash
cd docs
pdflatex -interaction=nonstopmode -halt-on-error categorical_reverse_mathematics.tex
makeindex categorical_reverse_mathematics.idx
pdflatex -interaction=nonstopmode -halt-on-error categorical_reverse_mathematics.tex
pdflatex -interaction=nonstopmode -halt-on-error categorical_reverse_mathematics.tex
```

Output: `docs/categorical_reverse_mathematics.pdf`.

---

## Building & Verifying the Lean 4 Formalization (`HomotopyCRM`)

Because `HomotopyCRM` builds on `mathlib4`, compiling `mathlib4` from source would take 60–90 minutes without pre-built `.olean` files. **Instead, use `lake exe cache get` to download precompiled `mathlib4` `.olean` archives in ~20–30 seconds** before running `lake build`.

> **Important:** The repository pins `leanprover/lean4:v4.28.0` in [`lean-toolchain`](lean-toolchain) and `mathlib4` `v4.28.0` (commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`) in [`lake-manifest.json`](lake-manifest.json). **Do NOT run `lake update`**—doing so will invalidate the pinned `mathlib4` `.olean` cache and may break version-locked proofs.

### Prerequisites & Fast Build Steps

1. **Install `elan`** (Lean version manager), if not already installed:
   ```bash
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
   source "$HOME/.elan/env"
   ```
   `elan` automatically reads `lean-toolchain` and installs `leanprover/lean4:v4.28.0`.

2. **Download pre-built `mathlib4` `.olean` files (~20–30s):**
   ```bash
   lake exe cache get
   ```

3. **Compile all `HomotopyCRM` modules (~35–60s cold, ~5–15s incremental):**
   ```bash
   lake build
   ```

4. **Check a single module in isolation:**
   ```bash
   lake env lean HomotopyCRM/InfinityResiduum.lean
   ```

5. **Run the combined verification gate (TeX + Lean 4):**
   ```bash
   python3 scripts/verify_monograph.py --full
   ```
   Or check Lean 4 alone:
   ```bash
   python3 scripts/verify_monograph.py --lean-only
   ```

---

### Machine-Checked Formalization Ledger (9 Production Modules, 14,583 Lines)

Every production file in `HomotopyCRM/` passes an explicit **4-Layer Definition Check Gate** inside a trailing `namespace Checks` block:

1. **Layer 1 — Carrier Inhabitation:** Concrete `Nontrivial` witnesses (`∃ x y, x ≠ y`) proving formal carriers do not collapse.
2. **Layer 2 — Bidirectional Separation:** Both positive (`P X`) and negative (`¬ P Y`) witnesses for core predicates, ruling out vacuous `True`/`False` encodings.
3. **Layer 3 — `mathlib4` Projections & Derived Sanity:** Faithful projections/instances into stock `mathlib4` typeclasses (`CommRing`, `Preorder`, `Category`, `Submodule`, `TopologicalSpace`) plus non-trivial boundary lemmas.
4. **Layer 4 — Kernel Axiom Gate:** `166` total `#guard_msgs in #print axioms` audits permitting **only** Lean's standard logical primitives (`propext`, `Classical.choice`, `Quot.sound`) with **0 `sorry`**, **0 custom `axiom`**, and **0 `opaque`** declarations.

Supporting root/base modules: `HomotopyCRM.lean` (10 lines; root library importer) and `HomotopyCRM/Basic.lean` (19 lines; `LocalizationTier` 4-tier ladder).

| Module | Lines | Book Section | Key Results Formalized | `#print axioms` Checks |
| :--- | :---: | :--- | :--- | :---: |
| [`InfinityResiduum.lean`](HomotopyCRM/InfinityResiduum.lean) | 949 | Ch. 1, §1.6 | Finite dynamical lassos $L_{p,q}$, profinite surjection $\widehat{\mathbb{N}}_{\mathrm{lasso}} \twoheadrightarrow \widehat{\mathbb{Z}}$ vs.\ $-1$, nominal $\mathbb{A}$ finite-support `Mono = Iso` crossing, tail cokernels | 20 |
| [`DeltaRingPerfection.lean`](HomotopyCRM/DeltaRingPerfection.lean) | 1,398 | Ch. 3, §3.5 | Goldthorpe's slice endofunctor & Lambek iso, $A_{\mathrm{perf}} = \varinjlim_\phi A$ with $\phi = s^{-1}$, $2$-torsion Joyal $\delta$-ring $R_2$, Nygaard separation on `DualInt` | 21 |
| [`BorelTailResiduum.lean`](HomotopyCRM/BorelTailResiduum.lean) | 682 | Ch. 4, §4.5 | $E_0$ Cantor tail exact sequence, $\mathsf{ZFC}$ Hamel section via `Classical.choice`, Cantor coset density forcing $T_1$ constancy, $E_0^{\mathrm{even}}$ parity torsor | 19 |
| [`OrdinalRankCompleteness.lean`](HomotopyCRM/OrdinalRankCompleteness.lean) | 1,774 | Ch. 5, §5.7 | Universe-safe `GlobularInfSystem`, transfinite invertibility ranks $0 < 1 < 2 < \omega < \omega+1$, Theorem 9A ($\alpha=0$ collapse), Proposition 11A Lali $+2$ ceiling | 18 |
| [`StepProductPhantom.lean`](HomotopyCRM/StepProductPhantom.lean) | 3,505 | Ch. 5, §5.7 | $[1]$-classifier SCC trapping (Thm 12B), $1$-acyclic Postnikov completeness (Thm 12C), step-product $\mathcal{Q}$ $\omega$-completeness, phantom $X_\bullet \in RL(\mathcal{Q})\setminus\mathcal{Q}$ disproving Conjecture C1 | 22 |
| [`DirectedFraisseSAP.lean`](HomotopyCRM/DirectedFraisseSAP.lean) | 2,125 | Ch. 6, §6.7 | `OrientedGradedPoset`, Steiner cycle obstruction, two-clause `IsFlowConvex`, 1-sided cobase-change, Nicolas pinched square, binary directed SAP (`sap_flowConvex`) | 13 |
| [`NominalSimplicity.lean`](HomotopyCRM/NominalSimplicity.lean) | 1,275 | Ch. 6, §6.6 | Proper-open coset global-section emptiness, open-normal simplicity of $\mathrm{Sym}(\mathbb{N})$, non-vanishing odd-finset parity torsor $[\mathcal{T}_{\mathrm{odd}}] = \delta(1) \neq 0$ in $\mathbf{Nom}$ | 20 |
| [`CubicalAmalgamation.lean`](HomotopyCRM/CubicalAmalgamation.lean) | 1,636 | Ch. 6, §6.7 | Quotient-free `Nat.find` minimal-support `CubicalAmalgam`, all-$n$ NDAP on closed oriented posets, punctured facet-cycle complex $F_n$ forcing impossibility for $n \ge 3$ | 15 |
| [`NominalICaTT.lean`](HomotopyCRM/NominalICaTT.lean) | 1,239 | Ch. 6, §6.8 | Theorem 9B: classical $\mathsf{DC}_\omega$ coinductive stream surjectivity vs.\ finite-stage splitting & infinite fresh-stream impossibility in Schanuel's nominal topos $\mathbf{Nom}$ | 18 |
| **Total (Production Modules)** | **14,583** | — | **9 Production Modules** (`+ 29` lines in `HomotopyCRM.lean` + `Basic.lean`) | **166** |

---

## Paper ↔ Lean Synchronization, GitHub Actions CI & Zenodo Releases

### Paper ↔ Lean Blueprint Synchronization

Following the [`infinity-cosmos`](https://github.com/emilyriehl/infinity-cosmos) `leanblueprint` + `checkdecls` + `doc-gen4` architecture, formal theorems and definitions in [`docs/categorical_reverse_mathematics.tex`](docs/categorical_reverse_mathematics.tex) are annotated directly with `\lean{...}`, `\leanok`, and `\uses{...}` macros:

- Running `python3 scripts/sync_blueprint.py` deterministically updates [`blueprint/src/content.tex`](blueprint/src/content.tex), [`blueprint/lean_decls`](blueprint/lean_decls) (89 cited declarations), and [`references.bib`](references.bib) without affecting the Royal Octavo PDF layout.
- Running `python3 scripts/sync_blueprint.py --check` enforces zero drift between the monograph LaTeX source and blueprint files.
- Running `lake exe checkdecls blueprint/lean_decls` ([`CheckDecls.lean`](CheckDecls.lean)) imports the compiled `HomotopyCRM` environment and rejects any missing, renamed, or `sorry`-tainted declaration cited by the book.

### Workflows & Archival Publishing

Four automated workflows under [`.github/workflows/`](.github/workflows) keep the PDF, interactive documentation, Lean checks, and Zenodo archive synchronized:

- **[`book.yml`](.github/workflows/book.yml) (`Build Monograph PDF`):** Runs on `push` to `main` and `pull_request` when monograph or blueprint sources change. Compiles the 152-page Royal Octavo PDF, enforces `verify_monograph.py --tex-only`, uploads a workflow artifact, and clobber-uploads the fresh `categorical_reverse_mathematics.pdf` directly to the Latest GitHub Release on `main` pushes.
- **[`lean.yml`](.github/workflows/lean.yml) (`Build & Verify HomotopyCRM Lean 4`):** Runs on `push` to `main` and `pull_request` on Lean or monograph declaration changes. Uses [`leanprover/lean-action@v1`](https://github.com/leanprover/lean-action) with Mathlib4 & GitHub `.olean` caches to build `HomotopyCRM` and `checkdecls`, then runs `sync_blueprint.py --check`, `lake exe checkdecls blueprint/lean_decls`, and `verify_monograph.py --lean-only --no-build`.
- **[`blueprint.yml`](.github/workflows/blueprint.yml) (`Compile Blueprint & Docs`):** Builds the monograph PDF, compiles `HomotopyCRM`, runs [`leanprover-community/docgen-action`](https://github.com/leanprover-community/docgen-action) to generate the `leanblueprint` Web Blueprint, SVG Dependency Graph, and `doc-gen4` API documentation, and deploys the combined portal to [GitHub Pages](https://tryggth.github.io/categorical-reverse-mathematics/).
- **[`release.yml`](.github/workflows/release.yml) (`Release Monograph PDF`):** Triggered on `v*` tag pushes; compiles `docs/categorical_reverse_mathematics.pdf`, attaches it to the GitHub Release, and (when `ZENODO_TOKEN` is configured) mints and publishes a new versioned record on Zenodo via [`scripts/publish_zenodo.py`](scripts/publish_zenodo.py).

---

## Citation

```bibtex
@book{Walters2026CRM,
  author    = {James F. Walters},
  title     = {Categorical Reverse Mathematics with Applications: The Structure of Necessity},
  year      = {2026},
  month     = nov,
  address   = {Port Townsend, Washington},
  doi       = {10.5281/zenodo.24238087},
  url       = {https://github.com/tryggth/categorical-reverse-mathematics},
  note      = {Open-access treatise (CC BY 4.0) with accompanying Lean 4 / mathlib4 formalization \texttt{HomotopyCRM}},
}
```

## License

- **Monograph (`docs/categorical_reverse_mathematics.tex`):** Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
- **Lean 4 Code & Scripts (`HomotopyCRM.lean`, `HomotopyCRM/`, `scripts/`):** Licensed under the Apache License, Version 2.0. See [`LICENSE`](LICENSE) for full details.
