# Categorical Reverse Mathematics — Volume I: Obstructions, Residuums, and the Geometry of Necessity

[![Build Monograph PDF](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/book.yml/badge.svg?branch=main)](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/book.yml)
[![Build & Verify HomotopyCRM Lean 4](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/lean.yml)
[![Compile Blueprint & Docs](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/blueprint.yml/badge.svg?branch=main)](https://github.com/tryggth/categorical-reverse-mathematics/actions/workflows/blueprint.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24238087.svg)](https://doi.org/10.5281/zenodo.24238087)
[![Download Monograph PDF (Latest)](https://img.shields.io/badge/Monograph_PDF-Latest_(v2.2)-1B365D)](https://github.com/tryggth/categorical-reverse-mathematics/releases/latest/download/categorical_reverse_mathematics.pdf)
[![Lean 4 v4.28.0](https://img.shields.io/badge/Lean_4-v4.28.0-blue)](lean-toolchain)

**Author:** James F. Walters (Port Townsend, Washington)  
**Edition:** First Edition (November 2026 · Release `v2.2`)  
**Archival DOI (Zenodo):** [`10.5281/zenodo.24238087`](https://doi.org/10.5281/zenodo.24238087) (All-versions Concept DOI: [`10.5281/zenodo.24238086`](https://doi.org/10.5281/zenodo.24238086))  
**Licenses:** CC BY 4.0 (Monograph & Companion Ledgers) · Apache 2.0 (`HomotopyCRM` Lean 4 Formalization & Scripts)  
**MSC 2020:** Primary `18B25` (Topoi), `03B30` (Foundations & Reverse Mathematics), `03G30` (Categorical Logic), `18N60` ($\infty$-Categories); Secondary `18N70` ($(\infty,\infty)$-Categories), `18F10` (Grothendieck Topologies & Sheaf Topoi), `55U35` (Abstract Homotopy Theory), `03D80` (Computability Applications), `03E25` (Axiom of Choice), `03F35` (Second-Order Subsystems), `68V15` (Formal Proof in Lean 4)

> **Live Editions & Formal Verification Portal:**  
> [**Download Current PDF (GitHub Release — 239 pp., Royal Octavo)**](https://github.com/tryggth/categorical-reverse-mathematics/releases/latest/download/categorical_reverse_mathematics.pdf) · [**GitHub Pages PDF**](https://tryggth.github.io/categorical-reverse-mathematics/categorical_reverse_mathematics.pdf) · [**Zenodo Archive**](https://doi.org/10.5281/zenodo.24238087) · [**Interactive Web Blueprint**](https://tryggth.github.io/categorical-reverse-mathematics/blueprint/) · [**Dependency Graph**](https://tryggth.github.io/categorical-reverse-mathematics/blueprint/dep_graph_document.html) · [**Lean 4 API Docs**](https://tryggth.github.io/categorical-reverse-mathematics/docs/)

---

## Overview

*Categorical Reverse Mathematics — Volume I: Obstructions, Residuums, and the Geometry of Necessity* develops a structural, geometric theory of deductive strength. Classical reverse mathematics calibrates theorems by comparing syntactic subsystems of second-order arithmetic over $\mathsf{RCA}_0$; **Categorical Reverse Mathematics (CRM)** measures foundational necessity directly inside the $2$-category $\mathbf{Doct}$ of **categorical doctrines**—structured classes of mathematical universes such as Grothendieck and elementary topoi, Joyal $\delta$-rings, $(\infty,1)$-topoi, weak $(\infty,\infty)$-categories, computational realizability and Fraïssé permutation topoi, and Joyal–Moerdijk small-map class ambients $(\mathcal{C}, \mathcal{S})$—by extracting the explicit geometric, cohomological, or modal obstructions that precipitate when an axiom is withheld.

Given a **doctrinal comparison triple**
$$\mathfrak{T} = (\mathcal{D}_0 \supseteq \mathcal{D}_1,\; \kappa : \Phi \Rightarrow \Psi) \in \mathrm{Dom}(\mathrm{Res}),$$
evaluated relative to a kataphatic **Doctrinal Philosophy** $\mathfrak{P} = (\mathbb{D}, \mathcal{P})$, CRM replaces one-dimensional propositional ladders with a **tri-modal residuum calculus** distinguishing:
- **Unique Minimum Residuums:** Exact universal obstructions governed by Base–Fiber Conservation, 5-term Leray–Serre sequences, and meet-closures in Grothendieck Lawvere–Tierney lattices;
- **Pareto Schisms:** Incomparable multi-axis trade-offs in non-distributive Moore lattices, such as the 4-topos Choice frontier $\{\mathrm{Proj}_{\mathrm{sub}}, \mathrm{Localic}\}$ or Turing-incomparable subtopoi $\{j_{O_1}, j_{O_2}\}$ of the Effective Topos $\mathcal{E}\mathrm{ff}$;
- **Evanescent Residuums:** Strict subtopos cones possessing no minimal floor, exemplified by Lawvere–Tierney topologies strictly above $\mathrm{id}_\Omega$ on $\mathcal{E}\mathrm{ff}$.

Residuums are calibrated across **Five Foundational Coordinate Axes** (extended in Chapter 7 along **Axes VI–VII** when turning the residuum operator onto `"Sets"` itself):

1. **Axis I — Choice / Splitting:** Local versus external splitting, $\mathsf{AC}$, $\mathsf{IAC}$, $\mathsf{DC}_\omega$ / $\mathsf{IDC}_\omega$, $\mathsf{COSHEP}$, $\mathsf{WISC}$, $\mathsf{SVC}$, and $\mathsf{IBPI}$.
2. **Axis II — Constructive Logic:** Excluded middle, Diaconescu's theorem, subobject classifier geometries, Kleene realizability ($\mathcal{E}\mathrm{ff}$), and Lawvere–Tierney modalities.
3. **Axis III — Arithmetic Infinity:** $\mathbf{FinSet}$ versus natural numbers objects ($\mathrm{NNO}$), profinite lasso completions ($\widehat{\mathbb{N}}_{\mathrm{lasso}} \twoheadrightarrow \widehat{\mathbb{Z}}$), and $\delta$-ring sequential relative perfection.
4. **Axis IV — Characteristic / $p$-Torsion:** Joyal $\delta$-ring lift torsors ($R_2 = \mathbb{Z}[\eta]/(2\eta,\eta^2)$ versus torsion-free `DualInt` $= \mathbb{Z}[\varepsilon]/(\varepsilon^2)$) and cubical/simplicial boundary cycles.
5. **Axis V — Directional Invertibility:** Coinductive versus inductive equivalences across the strict 4-tier $(\infty,\infty)$-localization ladder $\mathrm{Cat}^L_{(\infty,\infty)} \subsetneq \mathrm{Cat}^\omega_{(\infty,\infty)} \subsetneq \mathrm{Cat}^{\mathrm{coind}}_{(\infty,\infty)} \subsetneq \mathrm{Cat}^R_{(\infty,\infty)}$ (with Bousfield contravariance, distinct from locally finite-dimensional $\mathrm{Cat}_{\le\omega}$), Postnikov phantom towers, and directed stabilization in $\mathrm{CatSp} = \mathrm{Sp}(\mathrm{Cat}^R_*)$.
6. **Axes VI & VII — Set-Theoretic Compression & Structural Truncation (Ch. 7):** Quotient/image descent $\mathrm{im}(f) \in \mathcal{S}$ separating $\mathsf{ETCS} \simeq \mathsf{Mac}$ and $\mathsf{ZC}$ from $\mathsf{ZFC}$ (Axis VI), paired with well-founded coalgebra restriction $\mathbf{Coalg}_{\mathrm{wf}}(\mathcal{P}_{\mathcal{S}}) \hookrightarrow \mathbf{Coalg}(\mathcal{P}_{\mathcal{S}})$, Boffa Quine-atom torsors, and fiberwise $(-1)$-truncation $V_0 \hookrightarrow M = \mu\mathcal{P}_{\mathrm{Anima}}$ (Axis VII).

Two structural covenants organize the treatise:

- **Base–Fiber Conservation:** Foundational strength is conserved across bounded geometric morphisms $\gamma : \mathcal{E} \to \mathcal{S}$ and cloven doctrinal fibrations (quantified via the 5-term Leray sequence, Milnor $\varprojlim^1$, and amphoteric Double-Solvent collapses).
- **The Anchor-Witness Covenant:** High-altitude machinery is tethered throughout to five concrete **Touchstone** witnesses:
  1. **Nominal Parity Torsor (Ch. 6):** $[\mathcal{T}_{\mathrm{odd}}] \neq 0 \in H^1(\mathbf{Nom}; \mathrm{EvenFinset})$ in Schanuel's nominal topos $\mathbf{Nom} = \mathbf{Cont}(\mathrm{Sym}(\mathbb{N}))$, exhibiting Pro-Discrete Blindness ($H^1(\mathbf{Nom}; \Delta(\mathbb{Z}/2\mathbb{Z})) = 0$) and empty nominal coinductive invertibility streams without $\mathsf{IDC}_\omega$;
  2. **$2$-Torsion $\delta$-Ring & Shift Chirality (Ch. 3):** $R_2 = \mathbb{Z}[\eta]/(2\eta,\eta^2)$ ($\delta_0(\eta)=0$ and $\delta_1(\eta)=\eta$ lifting the augmentation Frobenius $\phi(a+b\eta)=a$ with $\phi(\eta)=0$; $R_2 \cong \mathbb{Z}\oplus\mathbb{F}_2$ as additive groups only), contrasted with `DualInt` $= \mathbb{Z}[\varepsilon]/(\varepsilon^2)$ (stage-$2$ Nygaard separation) and $+1$/$-1$ shift chirality of slice relative perfection $A \to A_{\mathrm{perf}} = \varinjlim_\phi A$ (never conflated with general Bhatt–Scholze prisms $(A,I)$);
  3. **Step-Product Postnikov Phantom (Ch. 5):** Gaunt Noetherian rank-$\omega$ step-product $\mathcal{Q} \subset \prod_{k \ge 1} \mathcal{A}_k$ on $[1] = \{0 < 1\}$ (with $\mathcal{A}_k = \mathcal{M}_{k+1}$ having $\mathrm{Hom}(1_k,1_k) = \mathcal{M}_k \not\simeq *$ and contractible other homs, giving hom-rank $\min(m,r)$) realizing a pure Postnikov phantom $X_\bullet \in RL(\mathcal{Q}) \setminus \mathcal{Q}$ that disproves Conjecture C1;
  4. **Directed Cubical $n$-Amalgamation Dichotomy (Ch. 6):** Quotient-free minimal-support disjoint amalgamation (`CubicalAmalgam`) for all $n$ under closed embeddings, separated from the punctured facet-cycle complex $F_n = \partial\Delta^{n-1}$ ($F_3 = \partial\Delta^2$) obstructing flow-acyclic convex amalgamation for every $n \ge 3$ while binary $n = 2$ (`sap_flowConvex`) stays acyclic;
  5. **Cantor Tail Quotient & CAR Moduli (Ch. 4):** Light-condensed tail quotient $\mathcal{Q}_{E_0} = 2^{\mathbb{N}}/E_0$, parity torsor $E_0^{\mathrm{even}}$, non-splitting $\mathrm{Ext}^1_{\mathbf{CondAb}_{\mathrm{light}}}$ presentation class, and Glimm's $\mathrm{UHF}(2^\infty)$ $C^*$-algebra ($K_0 \cong \mathbb{Z}[\tfrac{1}{2}]$), linked via Borel coding to radial smoothings of $\mathbb{R}^4$.

This repository contains the complete LaTeX source (`4,167` lines across [`docs/categorical_reverse_mathematics.tex`](docs/categorical_reverse_mathematics.tex) and [`docs/ch07_sets_residuum.tex`](docs/ch07_sets_residuum.tex)) for the **239-page** Royal Octavo ($6.14\,\mathrm{in} \times 9.21\,\mathrm{in}$) monograph (`237` interior pages plus a `2`-page stamped cover), the companion Lean 4 / `mathlib4` library **`HomotopyCRM`** (**22,024 lines** across **11 production modules**, `22,043` lines including [`Basic.lean`](HomotopyCRM/Basic.lean), kernel-verified under a 4-layer gate with `234` `#guard_msgs in #print axioms` audits, `0` `sorry`, `0` custom `axiom`, and `0` `opaque`), `152` blueprint declarations checked via `lake exe checkdecls`, a `263`-entry Technical Claims & Foundations audit ledger, and a `61`-node Concept Curriculum DAG.

---

## Monograph Structure

- **Frontmatter:** Stamped Cover (release PDF), Half-Title, Title Page, Cataloging & Machine-Checked Colophon, Table of Contents, *Preface: Form, Symmetry, and the Geometry of Missing Axioms*, and *Notation and Symbol Glossary*.
- **Part I — Foundations of Necessity and the Residuum Calculus**
  - **Chapter 1:** *Foundations of Categorical Reverse Mathematics* (Doctrinal fibrations, $\mathbf{Doct}$, $\mathrm{Dom}(\mathrm{Res})$, tri-modal obstruction modes, Doctrinal Philosophies & Pareto Schisms, Choice–Geometry Atlas, Five-Axis Map, Pure Axiom-of-Infinity Residua in $\mathbf{FinSet}$, Base–Fiber Conservation)
  - **Chapter 2:** *The Choice-Geometry Residuum Atlas and Cohomological Obstruction Theory* (Anatomy of Choice, Diaconescu & Freyd's countermodel, $\mathrm{COSHEP}$/$\mathrm{WISC}$/$\mathrm{SVC}$/$\mathrm{IBPI}$/$\mathrm{IDC}$, sheaf cohomology $H^1(\mathcal{E}/Y, G)$, symmetric Boolean-valued submodels $\mathrm{HS}_{\mathcal{F}} \subset V^{\mathbb{B}}$ & equivariant Boolean sheaves $\mathbf{Sh}_{\mathcal{G},\mathcal{F}}(\mathbb{B})$ for pure-$\mathsf{ZF}$ choice separations)
- **Part II — Algebraic Frobenius Lifts, Base–Fiber Conservation, and Infinite Towers**
  - **Chapter 3:** *Joyal $\delta$-Rings, $2$-Torsion Lift Torsors ($R_2$ vs.\ `DualInt`), and Relative Slice Perfection* (Joyal's polynomial cofactors $C_p(x,y)$, 3-stage $\delta$-lift obstruction tower on $\mathbb{Z}/2\mathbb{Z}$, $R_2$, and $R_{2,2}$, Nygaard separation on `DualInt`, Goldthorpe Theorems A & B, $+1$/$-1$ shift chirality of $A_{\mathrm{perf}} = \varinjlim_\phi A$)
  - **Chapter 4:** *Base-Topos Variation, Geometric Morphisms, and the Base-Fiber Conservation Principle* (Axis 1 Lawvere–Tierney deformations, Axis 2 choiceless/ultrafilter-free Barr–Diaconescu–Freyd & Deligne–$\mathrm{BPI}$ deformations, quantitative 5-term Leray sequence & $\mathrm{SL}_2(\mathbb{F}_5)$ transgression, Double-Solvent Theorem on $\mathcal{Q}_{E_0}$, $\mathrm{UHF}(2^\infty)$ $C^*$-moduli & $E_0^{\mathrm{even}}$ parity grading, 5-rung CRM–Borel complexity dictionary)
- **Part III — Higher Categories, Site Combinatorics, and Set-Theoretic Foundations**
  - **Chapter 5:** *Higher Categorical Reverse Mathematics in $(\infty, 1)$-Topoi, Univalent Foundations, and Postnikov Obstruction Towers* ($\mathrm{AC}_{n,m}$, Postnikov $k$-invariants & Giraud $1$-gerbes, hypercompleteness, directed stabilization in $\mathrm{CatSp}$ & Barratt–Priddy–Quillen collapse, strict 4-tier $(\infty,\infty)$-ladder, ordinal-rank completeness & Lali $+2$ ceiling, step-product $\mathcal{Q}$ phantom disproving Conjecture C1, `ICaTT` clan semantics)
  - **Chapter 6:** *Site-Level Combinatorics, Realizability Topoi, and Computational Reverse Mathematics* (Kleene $\mathcal{E}\mathrm{ff}$, $\mathrm{WKL}$/$\mathrm{ULK}$ & Weihrauch–Lawvere–Tierney duality, site combinatorial dictionary, Fraïssé atomic-topology escape, Kihara's 5-rung atomic choice spectrum & nominal parity torsor $[\mathcal{T}_{\mathrm{odd}}]$, binary flow-convex SAP vs.\ $n \ge 3$ cubical $n$-amalgamation wall $F_n$, $\mathsf{IDC}_\omega$ calibration of coinductive invertibility streams)
  - **Chapter 7:** *Residuums and "$\mathbf{Sets}$"* (Fixed-set class kaleidoscope $\mathrm{Def} \dashv \pi_{\mathrm{Set}}$ & $\mathbf{Card} \hookrightarrow \mathbf{Set}$ splitting, $\mathsf{ETCS} \simeq \mathsf{Mac}$ vs.\ $\mathsf{ZC}$, Glazer's non-conservativity & Borel Determinacy escape, Joyal–Moerdijk small-map ambients $(\mathcal{C}, \mathcal{S})$ along Axes VI–VII, non-well-founded coalgebras, Boffa Quine-atom torsors, Gylterud $(-1)$-truncation $V_0 \hookrightarrow M$, scale-invariance & bridge to Volume II)
- **Part IV — Programmatic Panorama, Open Horizons, and Formal Verification**
  - **Chapter 8:** *Programmatic Panorama: External Benchmark Lattices Across Analysis, Algebra, Homotopy, and Cohesion* (Internal continuum $\mathbb{R}_C$ vs.\ $\mathbb{R}_D$ & pointfree spatiality, $\Omega$-geometry & homological exactness diamond, predicative pretopoi / two-sorted hyperdoctrines for the Categorical "Big Five" & $W$-types/HITs, univalence, Blakers–Massey excision & $\mathrm{CatSp}$ benchmarks, synthetic differential geometry & differential cohesive $(\infty,1)$-topoi)
  - **Chapter 9:** *Master Atlas of Open Problems, Methodological Blueprints, and Research Horizons* (Unified CRM architecture & Pareto frontiers, 5-step residuum protocol, Five Core Conjectures, Seventeen Open Problems across Horizons I–VIII, Two-Tier Machine-Checked Lean 4 Ledger, Master Reference Atlas, Epilogue, 113-entry Bibliography, two-column Subject Index)

---

## Repository Layout

```text
.
├── .github/
│   └── workflows/
│       ├── blueprint.yml                 # CI: Web Blueprint, Dependency Graph, API Docs, & GitHub Pages deploy
│       ├── book.yml                      # CI: Stamped Royal Octavo PDF build + update Latest GitHub Release PDF
│       ├── lean.yml                      # CI: Cached Lean 4 build, blueprint sync, checkdecls, & 4-layer gate
│       └── release.yml                   # CI: Tagged v* GitHub Release PDF + automated Zenodo new version
├── .gitignore                            # Ignores LaTeX aux/PDF build outputs, .lake/, site/, and local scratchpads
├── .zenodo.json                          # Published Zenodo record metadata (DOI 10.5281/zenodo.24238087)
├── CheckDecls.lean                       # Lake executable verifying all 152 cited declarations in HomotopyCRM
├── HomotopyCRM.lean                      # Root Lean 4 entry module importing all 12 HomotopyCRM submodules (12 lines)
├── HomotopyCRM/
│   ├── Basic.lean                        # Shared 4-tier (∞,∞) localization ladder enum (19 lines)
│   ├── InfinityResiduum.lean             # Ch. 1 §1.6: Finite lassos, profinite Z_hat, Dedekind & Nom gap (949 lines)
│   ├── DeltaRingPerfection.lean          # Ch. 3 §3.2–3.3: Full \leanok Thm 3.3.1, R_2 vs DualInt, Nygaard (2,141 lines)
│   ├── BorelTailResiduum.lean            # Ch. 4 §4.5: E_0 Cantor tail quotient & E_0^even torsor (697 lines)
│   ├── OrdinalRankCompleteness.lean      # Ch. 5 §5.7: Globular ordinal-rank completeness & Lali +2 ceiling (1,828 lines)
│   ├── StepProductPhantom.lean           # Ch. 5 §5.7: Step-product Q & Postnikov phantom X_• (3,505 lines)
│   ├── DirectedFraisseSAP.lean           # Ch. 6 §6.5/6.7: Flow-convex embeddings & binary directed SAP (2,125 lines)
│   ├── NominalSimplicity.lean            # Ch. 6 §6.4/6.6: Sym(N) simplicity & odd-finset parity torsor (1,276 lines)
│   ├── CubicalAmalgamation.lean          # Ch. 6 §6.7: Full \leanok Thm 6.7.2 cubical amalgamation & F_n wall (2,117 lines)
│   ├── NominalICaTT.lean                 # Ch. 6 §6.8: DC_ω stream adequacy vs Nom FreshRootStream emptiness (1,544 lines)
│   ├── SetsResiduum.lean                 # Ch. 7 §7.1–7.5: ClassSetModel, Card split, Quine/Boffa torsors, ZFSet (1,401 lines)
│   └── DoctrinalFibration.lean           # Chs. 1, 3, 4: Fibrations, mates, Pareto Schism, R_2/R_{2,2}, SL_2(F_5) (4,441 lines)
├── LICENSE                               # Dual licensing details: CC BY 4.0 (Monograph) & Apache 2.0 (Lean 4/Scripts)
├── blueprint/
│   ├── lean_decls                        # Auto-generated list of 152 disjoint Lean 4 declarations checked by checkdecls
│   └── src/                              # leanblueprint templates, macros, & synced content.tex
├── docs/
│   ├── assets/cover.jpg                  # Royal Octavo front cover artwork stamped onto release PDF
│   ├── categorical_reverse_mathematics.tex # Primary LaTeX source of truth (3,775 lines; \inputs ch07_sets_residuum.tex)
│   ├── ch07_sets_residuum.tex            # Chapter 7 ("Residuums and Sets") modular LaTeX source (392 lines)
│   ├── concept_curriculum.md             # 61-node, 147-edge prerequisite & monograph concept curriculum
│   ├── concept_graph.dot                 # Graphviz DOT specification of the 61-node concept DAG
│   ├── concept_graph.json                # Machine-readable JSON schema of the concept & prerequisite DAG
│   ├── technical_claims_foundations.md   # 263-entry claim-by-claim foundational grounding & audit ledger
│   ├── technical_claims_foundations.xlsx # Spreadsheet export of the 263-entry technical claims ledger
│   ├── 11_FUTURE_VISTAS_AND_SPINOUTS.md  # Deferred Volume II & spinout research horizons
│   └── REMEDIATION_V{2,3,4}_LEDGER.md    # Clean-room mathematical & Lean remediation audit ledgers
├── home_page/
│   └── index.html                        # GitHub Pages landing page linking PDF, Blueprint, Graph, & API Docs
├── lake-manifest.json                    # Exact pinned dependencies (mathlib4 v4.28.0, doc-gen4 v4.28.0)
├── lakefile.toml                         # Lake project configuration for HomotopyCRM and checkdecls
├── lean-toolchain                        # Pinned toolchain: leanprover/lean4:v4.28.0
├── references.bib                        # Auto-generated BibTeX entries (113 items) synced from bibliography
└── scripts/
    ├── create_claims_github_issues.py    # Issue-tracker sync utility for technical claims queue
    ├── export_technical_claims_xlsx.py   # Deterministic Markdown -> XLSX exporter for claims ledger
    ├── manage_claims_priority_queue.py   # Priority queue manager for clean-room claim verification
    ├── publish_zenodo.py                 # Zenodo draft/DOI/publish & version automation via REST API
    ├── render_technical_claims_pdf.py    # Renders 73-page Royal Octavo PDF of technical_claims_foundations.md
    ├── stamp_cover.py                    # Prepends 2-page Royal Octavo cover onto root PDF (237 -> 239 pp.)
    ├── sync_blueprint.py                 # Deterministic LaTeX -> blueprint/ & references.bib sync (--check)
    ├── verify_curriculum.py              # 10-gate verifier for concept_curriculum.md & concept_graph.{dot,json}
    ├── verify_monograph.py               # Master automated TeX + Claims + Blueprint + Cover + Lean 4 harness
    └── verify_technical_claims.py        # Bijective 263-claim, 152-decl, & 113-citation grounding verifier
```

---

## Building the Book (PDF from LaTeX Source)

Every push to `main` touching the monograph sources compiles a fresh PDF, stamps the 2-page Royal Octavo cover onto `categorical_reverse_mathematics.pdf`, updates the [**Latest GitHub Release PDF**](https://github.com/tryggth/categorical-reverse-mathematics/releases/latest/download/categorical_reverse_mathematics.pdf), and republishes the [**GitHub Pages PDF**](https://tryggth.github.io/categorical-reverse-mathematics/categorical_reverse_mathematics.pdf) alongside the interactive blueprint. To compile locally from source:

### Prerequisites (TeX Live + `pikepdf`)

On **Ubuntu / Debian**, install the verified TeX Live package set plus `python3-pikepdf` (for cover stamping):

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
  lmodern \
  python3-pikepdf
```

> **Note:** On **macOS**, install [MacTeX](https://www.tug.org/mactex/) (`brew install --cask mactex-no-gui`) and `pip3 install pikepdf`. If optional `texlive-fonts-extra` (`newpxtext`/`newpxmath`/`zi4`) is installed, the preamble selects it automatically; otherwise it falls back cleanly to TeX Gyre Pagella + Pazo math + TeX Gyre Cursor.

### Recommended Verified Build

Run the master verification script from the repository root (requires Python 3.9+):

```bash
python3 scripts/verify_monograph.py --tex-only
```

This executes the full build and apparatus audit pipeline:
- Verifies zero drift in [`blueprint/src/content.tex`](blueprint/src/content.tex), [`blueprint/lean_decls`](blueprint/lean_decls) (`152` declarations), and [`references.bib`](references.bib) (`113` entries) via `sync_blueprint.py --check`;
- Verifies 1-to-1 grounding across all `263` entries in [`docs/technical_claims_foundations.md`](docs/technical_claims_foundations.md) via `verify_technical_claims.py --check`;
- Enforces `0` forbidden strings, `0` undefined `\cite` or `\ref` keys, and `100%` citation coverage (`0` uncited `\bibitem` entries across all `113` references);
- Runs the three-pass `pdflatex` + `makeindex` build inside `docs/` with `0` LaTeX errors and `0` `Overfull \hbox` / `\vbox` warnings across all **237** interior Royal Octavo pages;
- Syncs root `categorical_reverse_mathematics.{tex,pdf}` and runs [`scripts/stamp_cover.py`](scripts/stamp_cover.py) to prepend the 2-page Royal Octavo cover (**239** pages total with preserved PDF `/PageLabels`, keeping `docs/categorical_reverse_mathematics.pdf` unstamped).

### Manual `pdflatex` + `makeindex` Build

```bash
cd docs
pdflatex -interaction=nonstopmode -halt-on-error categorical_reverse_mathematics.tex
makeindex categorical_reverse_mathematics.idx
pdflatex -interaction=nonstopmode -halt-on-error categorical_reverse_mathematics.tex
pdflatex -interaction=nonstopmode -halt-on-error categorical_reverse_mathematics.tex
cd ..
cp docs/categorical_reverse_mathematics.pdf categorical_reverse_mathematics.pdf
python3 scripts/stamp_cover.py
```

Outputs: `docs/categorical_reverse_mathematics.pdf` (`237` pp., unstamped interior) and `categorical_reverse_mathematics.pdf` (`239` pp., cover-stamped release edition).

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

3. **Compile all `HomotopyCRM` modules and `checkdecls` (~45–90s cold, ~5–15s incremental):**
   ```bash
   lake build HomotopyCRM checkdecls
   lake exe checkdecls blueprint/lean_decls
   ```

4. **Check a single module in isolation:**
   ```bash
   lake env lean HomotopyCRM/DeltaRingPerfection.lean
   ```

5. **Run the combined verification gate (TeX + Blueprint + Claims + Lean 4):**
   ```bash
   python3 scripts/verify_monograph.py --full
   ```
   Or check Lean 4 alone:
   ```bash
   python3 scripts/verify_monograph.py --lean-only
   ```

---

### Machine-Checked Formalization Ledger (11 Production Modules, 22,024 Lines)

Every production file in `HomotopyCRM/` passes an explicit **4-Layer Definition Check Gate** inside a trailing `namespace Checks` block:

1. **Layer 1 — Carrier Inhabitation:** Concrete `Nontrivial` witnesses (`∃ x y, x ≠ y`) proving formal carriers do not collapse.
2. **Layer 2 — Bidirectional Separation:** Both positive (`P X`) and negative (`¬ P Y`) witnesses for core predicates, ruling out vacuous `True`/`False` encodings.
3. **Layer 3 — `mathlib4` Projections & Derived Sanity:** Faithful projections/instances into stock `mathlib4` typeclasses (`CommRing`, `Preorder`, `Category`, `Submodule`, `TopologicalSpace`, `AddTorsor`) plus non-trivial boundary lemmas.
4. **Layer 4 — Kernel Axiom Gate:** **`234`** total `#guard_msgs in #print axioms` audits permitting **only** Lean's standard logical primitives (`propext`, `Classical.choice`, `Quot.sound`) with **0 `sorry`**, **0 custom `axiom`**, and **0 `opaque`** declarations.

Under the **Two-Tier Blueprint Standard**, `\leanok` is reserved strictly for formal theorems proved at full stated monograph generality in Lean 4—**Theorem 3.3.1** (`thm:slice-perfection-chirality` in [`DeltaRingPerfection.lean`](HomotopyCRM/DeltaRingPerfection.lean)) and **Theorem 6.7.2** (`thm:directed-cubical-amalgamation` in [`CubicalAmalgamation.lean`](HomotopyCRM/CubicalAmalgamation.lean))—whereas `\leanwitness` marks `24` blueprint nodes across Chapters 1–7 pairing prose proofs or external benchmarks with kernel-checked anchor witnesses or combinatorial, globular, and set-level surrogates. Supporting root/base modules: [`HomotopyCRM.lean`](HomotopyCRM.lean) (`12` lines; root library importer) and [`HomotopyCRM/Basic.lean`](HomotopyCRM/Basic.lean) (`19` lines; `LocalizationTier` 4-tier ladder, bringing `HomotopyCRM/` to `22,043` lines across all `12` `.lean` files).

| Module | Lines | Book Section | Key Results Formalized | `#print axioms` Checks |
| :--- | :---: | :--- | :--- | :---: |
| [`InfinityResiduum.lean`](HomotopyCRM/InfinityResiduum.lean) | 949 | Ch. 1, §1.6 | Finite dynamical lassos $L_{p,q}$, profinite surjection $\widehat{\mathbb{N}}_{\mathrm{lasso}} \twoheadrightarrow \widehat{\mathbb{Z}}$ vs.\ $-1$, nominal $\mathbb{A}$ finite-support `Mono = Iso` crossing, tail cokernels | 20 |
| [`DeltaRingPerfection.lean`](HomotopyCRM/DeltaRingPerfection.lean) | 2,141 | Ch. 3, §3.2–3.3 | **Full `\leanok` Thm 3.3.1:** universe-polymorphic Goldthorpe Thm A/B slice initial algebras & $+1$/$-1$ shift chirality of $A_{\mathrm{perf}} = \varinjlim_\phi A$; Joyal $\delta$-ring $R_2$ lift pair vs.\ `DualInt` stage-$2$ Nygaard separation | 28 |
| [`BorelTailResiduum.lean`](HomotopyCRM/BorelTailResiduum.lean) | 697 | Ch. 4, §4.5 | $E_0$ Cantor tail exact sequence, $\mathsf{ZFC}$ Hamel section via `Submodule.exists_isCompl`, basis-free Cantor coset density forcing $T_1$ constancy, $E_0^{\mathrm{even}}$ parity torsor | 19 |
| [`OrdinalRankCompleteness.lean`](HomotopyCRM/OrdinalRankCompleteness.lean) | 1,828 | Ch. 5, §5.7 | State-coalgebraic `GlobularInfSystem`, transfinite invertibility ranks $0 < 1 < 2 < \omega < \omega+1$ (`OmegaTowerState` / `CoindWalkState`), $\alpha=0$ completeness, Lali $K+2$ cell-height ceiling | 20 |
| [`StepProductPhantom.lean`](HomotopyCRM/StepProductPhantom.lean) | 3,505 | Ch. 5, §5.7 | $[1]$-classifier single-SCC trapping, $1$-acyclic Postnikov completeness, gaunt absorbing monoids, step-product $\mathcal{Q}$ $\omega$-completeness (hom-cardinality $2^{\min(m,r)}$), phantom $X_\bullet \in RL(\mathcal{Q})\setminus\mathcal{Q}$ disproving Conjecture C1 | 22 |
| [`DirectedFraisseSAP.lean`](HomotopyCRM/DirectedFraisseSAP.lean) | 2,125 | Ch. 6, §6.5 & §6.7 | `OrientedGradedPoset`, unbiased `FlowStep.dim_eq`, Steiner cycle obstruction, strict 3-tier embeddings (two-clause `IsFlowConvex`), 1-sided cobase-change, binary directed SAP (`sap_flowConvex`) | 13 |
| [`NominalSimplicity.lean`](HomotopyCRM/NominalSimplicity.lean) | 1,276 | Ch. 6, §6.4 & §6.6 | Proper-open coset global-section emptiness, open-normal & open-finite-index simplicity of $\mathrm{Sym}(\mathbb{N})$, non-vanishing odd-finset parity torsor $[\mathcal{T}_{\mathrm{odd}}] = \delta(1) \neq 0$ in $\mathbf{Nom}$ | 20 |
| [`CubicalAmalgamation.lean`](HomotopyCRM/CubicalAmalgamation.lean) | 2,117 | Ch. 6, §6.7 | **Full `\leanok` Thm 6.7.2:** quotient-free `Nat.find` minimal-support `CubicalAmalgam` (`instFintypeCubicalAmalgam` in `Type u`), all-$n$ closed NDAP vs.\ punctured facet-cycle $F_n$ obstructing flow-acyclic amalgamation for $n \ge 3$ | 20 |
| [`NominalICaTT.lean`](HomotopyCRM/NominalICaTT.lean) | 1,544 | Ch. 6, §6.8 | Choice-free step soundness, classical `Classical.choice` stream surjectivity, exact finite support on `CaTTTerm` rose trees, finite-stage `FreshChain n` splitting vs.\ empty nominal `FreshRootStream` | 21 |
| [`SetsResiduum.lean`](HomotopyCRM/SetsResiduum.lean) | 1,401 | Ch. 7, §7.1–7.5 | `ClassSetModel` coreflection $\mathrm{Def} \dashv \pi_{\mathrm{Set}}$, naive pullback Subclass-Separation failure, skeletal `Card` splitting $\iff$ global choice, `PSet`-to-`APG` bisimulation, Quine atom & Boffa twin $\mathbb{Z}/2\mathbb{Z}$-torsor, `ZFSet` quotient gate | 19 |
| [`DoctrinalFibration.lean`](HomotopyCRM/DoctrinalFibration.lean) | 4,441 | Chs. 1, 3, 4 | 1-categorical `DoctrinalFibration` & involutive `MateDoubleSquare`, tri-modal witness carriers, `DoctrinalPhilosophy` & 4-topos Pareto Schism (`M1Monoid`, $V$, $D_4$, `TwoGroupCat`), $3^k 2^m$ slice LTT count, $R_2$/$R_{2,2}$ $\delta$-lift counts ($2$ vs.\ $16$/$6$ orbits), $\mathrm{SL}_2(\mathbb{F}_5)$ Leray transgression | 32 |
| **Total (Production Modules)** | **22,024** | **Chs. 1, 3–7, 9** | **11 Production Modules** (`+ 19` lines in `Basic.lean` = `22,043` lines across `12` files in `HomotopyCRM/`, `+ 12` lines in `HomotopyCRM.lean`) | **234** |

---

## Paper ↔ Lean Synchronization, Companion Ledgers, CI & Zenodo Releases

### Paper ↔ Lean Blueprint Synchronization & Companion Audits

Following the [`infinity-cosmos`](https://github.com/emilyriehl/infinity-cosmos) `leanblueprint` + `checkdecls` + `doc-gen4` architecture, formal environments in [`docs/categorical_reverse_mathematics.tex`](docs/categorical_reverse_mathematics.tex) and [`docs/ch07_sets_residuum.tex`](docs/ch07_sets_residuum.tex) are annotated directly with `\lean{...}`, `\leanok`, `\leanwitness`, and `\uses{...}` macros and backed by deterministic audit suites:

- **Blueprint Sync (`sync_blueprint.py`):** Running `python3 scripts/sync_blueprint.py` deterministically updates [`blueprint/src/content.tex`](blueprint/src/content.tex), [`blueprint/lean_decls`](blueprint/lean_decls) (`152` disjoint cited declarations), and [`references.bib`](references.bib) (`113` BibTeX entries) without altering the Royal Octavo PDF layout (`--check` enforces zero drift).
- **Kernel Declaration Gate (`CheckDecls.lean`):** Running `lake exe checkdecls blueprint/lean_decls` imports the compiled `HomotopyCRM` environment and rejects any missing, renamed, or `sorry`-tainted declaration cited by the monograph.
- **Technical Claims & Foundations Ledger (`verify_technical_claims.py`):** Running `python3 scripts/verify_technical_claims.py --check` audits [`docs/technical_claims_foundations.md`](docs/technical_claims_foundations.md) (`263` cataloged entries across all `89` formal environments, `174` inline/table claims, `152` blueprint Lean declarations, and `113` literature citations; companion exports via `export_technical_claims_xlsx.py` and `render_technical_claims_pdf.py`).
- **Concept Curriculum & Prerequisite DAG (`verify_curriculum.py`):** Running `python3 scripts/verify_curriculum.py` validates all 10 structural invariants across [`docs/concept_curriculum.md`](docs/concept_curriculum.md), [`docs/concept_graph.dot`](docs/concept_graph.dot), and [`docs/concept_graph.json`](docs/concept_graph.json) (`61` canonical DAG nodes, `147` directed edges, `55` prerequisites, and `189` monograph concepts).

### Workflows & Archival Publishing

Four automated workflows under [`.github/workflows/`](.github/workflows) keep the PDF, interactive documentation, Lean checks, and Zenodo archive synchronized:

- **[`book.yml`](.github/workflows/book.yml) (`Build Monograph PDF`):** Runs on `push` to `main` and `pull_request` when monograph, claim-ledger, cover, or blueprint sources change. Compiles and audits the 239-page cover-stamped Royal Octavo PDF via `verify_monograph.py --tex-only`, uploads a workflow artifact, and clobber-uploads `categorical_reverse_mathematics.pdf` directly to the Latest GitHub Release on `main` pushes.
- **[`lean.yml`](.github/workflows/lean.yml) (`Build & Verify HomotopyCRM Lean 4`):** Runs on `push` to `main` and `pull_request` on Lean or monograph declaration changes. Uses [`leanprover/lean-action@v1`](https://github.com/leanprover/lean-action) with Mathlib4 & GitHub `.olean` caches to build `HomotopyCRM` and `checkdecls`, then runs `sync_blueprint.py --check`, `lake exe checkdecls blueprint/lean_decls`, and `verify_monograph.py --lean-only --no-build`.
- **[`blueprint.yml`](.github/workflows/blueprint.yml) (`Compile Blueprint & Docs`):** Builds the cover-stamped monograph PDF, compiles `HomotopyCRM`, runs [`leanprover-community/docgen-action`](https://github.com/leanprover-community/docgen-action) to generate the `leanblueprint` Web Blueprint, Dependency Graph, and `doc-gen4` API documentation, and deploys the combined portal to [GitHub Pages](https://tryggth.github.io/categorical-reverse-mathematics/).
- **[`release.yml`](.github/workflows/release.yml) (`Release Monograph PDF`):** Triggered on `v*` tag pushes; compiles and stamps `categorical_reverse_mathematics.pdf`, attaches it to the GitHub Release, and (when `ZENODO_TOKEN` is configured) mints and publishes a new versioned record on Zenodo via [`scripts/publish_zenodo.py`](scripts/publish_zenodo.py).

---

## Citation

```bibtex
@book{Walters2026CRM,
  author    = {James F. Walters},
  title     = {Categorical Reverse Mathematics --- Volume~I: Obstructions, Residuums, and the Geometry of Necessity},
  year      = {2026},
  month     = nov,
  edition   = {First},
  version   = {2.2},
  address   = {Port Townsend, Washington},
  doi       = {10.5281/zenodo.24238087},
  url       = {https://github.com/tryggth/categorical-reverse-mathematics},
  note      = {Open-access treatise (CC BY 4.0) with accompanying 11-module Lean 4 / mathlib4 formalization \texttt{HomotopyCRM}},
}
```

## License

- **Monograph & Companion Ledgers ([`docs/categorical_reverse_mathematics.tex`](docs/categorical_reverse_mathematics.tex), [`docs/ch07_sets_residuum.tex`](docs/ch07_sets_residuum.tex), [`docs/technical_claims_foundations.md`](docs/technical_claims_foundations.md), [`docs/concept_curriculum.md`](docs/concept_curriculum.md)):** Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
- **Lean 4 Code & Verification Scripts ([`HomotopyCRM.lean`](HomotopyCRM.lean), [`HomotopyCRM/`](HomotopyCRM), [`CheckDecls.lean`](CheckDecls.lean), [`scripts/`](scripts)):** Licensed under the Apache License, Version 2.0. See [`LICENSE`](LICENSE) for full details.
