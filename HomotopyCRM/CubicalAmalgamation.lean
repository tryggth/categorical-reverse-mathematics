/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HomotopyCRM Formalization Team
-/
import HomotopyCRM.DirectedFraisseSAP
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Find

/-!
# Cubical `n`-Amalgamation (`n-DAP`) and the All-`n ≥ 3` Directed Cycle Obstruction

This module formalizes `MSG_013` (`TODO-15` Part A, **Theorem 10B**) of the `HomotopyCRM` library,
calibrating higher cubical Disjoint `n`-Amalgamation (`n-DAP`) over punctured `n`-cubes
`𝒫⁻(n) := {S ⊆ [n] | S ⊊ [n]}` for finite directed cellular shapes whose nerves populate the
Postnikov-complete tier `Cat^L_(∞,∞)` of the strict reflective localization ladder
`Cat^L_(∞,∞) ⊊ Cat^ω_(∞,∞) ⊊ Cat^coind_(∞,∞) ⊊ Cat^R_(∞,∞) := lim_κ Cat_(∞,n)`
(Ozornova–Rovelli–Walde `arXiv:2603.11005v2`, `arXiv:2608.28355`, `arXiv:2610.38698`;
Gepner–Heine `arXiv:2603.09903`; atomic-topos amalgamation calibration following Kihara
`arXiv:2609.21111`).

## Main Results

1. **Punctured `n`-Cubes (`PuncturedCube n`):**
   - `PuncturedCube n := {S : Finset (Fin n) // S ≠ Finset.univ}` carries stock `Fintype`,
     `DecidableEq`, `DecidableLE`, and `SemilatticeInf` instances (`(S ⊓ T).1 = S.1 ∩ T.1`),
     with `Fintype.card (PuncturedCube n) = 2 ^ n - 1` (`PuncturedCube.card_eq`).

2. **Intersective Cubical Poset Diagrams & `n-DAP` (`CubicalPosetDiagram`, `HasCubicalNDAP`):**
   - `CubicalPosetDiagram n` packages functorial diagrams of `OrientedGradedPoset`s and closed
     cellular embeddings `IsClosedEmbedding` indexed by `PuncturedCube n`.
   - `CubicalPosetDiagram.IsIntersective` axiomatizes exact face-intersection pullbacks inside
     every proper face `U : PuncturedCube n`; `CubicalCocone`, `IsDisjointCubicalAmalgamation`,
     and `HasCubicalNDAP` formalize closed-embedding cocones satisfying pairwise intersection
     preservation `Set.range (leg S) ∩ Set.range (leg T) = Set.range (leg (S ⊓ T))`.

3. **Theorem 10B Part 1 — All-`n` Quotient-Free `n-DAP` (`cubical_ndap_closed_oriented_poset`):**
   - Using the **quotient-free minimal-support carrier**
     `CubicalAmalgam D := {p : Σ S, D.obj S // D.IsMinimalCell p.1 p.2}`, every intersective
     `CubicalPosetDiagram n` admits an `OrientedGradedPoset` amalgamation whose canonical legs
     `amalgamLeg` are closed cellular embeddings commuting with all face maps, inducing principal-
     closure order isomorphisms `cl (amalgamLeg hInt S x) ≃o cl x`, and satisfying global `n-DAP`
     disjointness (`hasCubicalNDAP_iff_isIntersective : HasCubicalNDAP D ↔ D.IsIntersective`).

4. **Theorem 10B Part 2 — All-`n ≥ 3` Failure on Flow-Acyclic Convex Diagrams
   (`no_flowAcyclic_cubical_amalgam_of_three_le`, `theorem10B_cubical_amalgamation_dichotomy`):**
   - Whereas binary (`n = 2`) Strong Amalgamation preserves `IsFlowAcyclic` along `IsFlowConvex`
     embeddings (`sap_flowConvex` in `DirectedFraisseSAP.lean`), for **every `n ≥ 3`** the
     facet-supported directed `n`-cycle diagram `facetCycleDiagram n hn` (`A_i = univ \ {i, i+1}`,
     `M_i = univ \ {i+1}`) is intersective, has `IsFlowAcyclic` finite faces (each containing at
     most one `1`-cell), and has `IsFlowConvex` transition maps (via `A_i ∪ A_{i+1} = M_i`), yet
     **no** `IsFlowAcyclic` `OrientedGradedPoset` admits a `CubicalCocone` on it.

5. **Mandatory 4-Layer Definition Check Gate (`namespace Checks`):**
   - Verifies Inhabitation (Layer 1), Bidirectional Separation across `IsIntersective`,
     `HasCubicalNDAP`, `IsMinimalCell`, `IsDisjointCubicalAmalgamation`, `IsFlowAcyclic` on
     `CubicalAmalgam`, and the `n = 2` vs. `n ≥ 3` dimension dichotomy (Layer 2), Mathlib
     projections & cardinality/isomorphism sanity checks (Layer 3), and `#print axioms` (Layer 4).
-/

universe u v

namespace HomotopyCRM

/-! ## Section 1: Punctured `n`-Cubes (`PuncturedCube n`) -/

/-- The **punctured `n`-cube** `𝒫⁻(n) := {S : Finset (Fin n) // S ≠ Finset.univ}` of proper faces
of the standard `n`-cube, ordered by subset inclusion. -/
def PuncturedCube (n : ℕ) : Type :=
  {S : Finset (Fin n) // S ≠ Finset.univ}

namespace PuncturedCube

instance (n : ℕ) : DecidableEq (PuncturedCube n) :=
  inferInstanceAs (DecidableEq {S : Finset (Fin n) // S ≠ Finset.univ})

instance (n : ℕ) : Fintype (PuncturedCube n) :=
  inferInstanceAs (Fintype {S : Finset (Fin n) // S ≠ Finset.univ})

/-- Extensionality of proper faces in `PuncturedCube n`. -/
@[ext]
theorem ext {n : ℕ} {S T : PuncturedCube n} (h : S.1 = T.1) : S = T :=
  Subtype.ext h

/-- `PuncturedCube n` forms a meet-semilattice (`SemilatticeInf`) under subset inclusion and
binary intersection `(S ⊓ T).1 = S.1 ∩ T.1`. -/
instance (n : ℕ) : SemilatticeInf (PuncturedCube n) where
  le S T := S.1 ⊆ T.1
  le_refl S := Finset.Subset.refl S.1
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm _ _ hST hTS := Subtype.ext (Finset.Subset.antisymm hST hTS)
  inf S T :=
    ⟨S.1 ∩ T.1, fun h ↦
      S.2 <| Finset.eq_univ_iff_forall.mpr fun k ↦ by
        have hk : k ∈ S.1 ∩ T.1 := h.symm ▸ Finset.mem_univ k
        exact (Finset.mem_inter.mp hk).1⟩
  inf_le_left _ _ := Finset.inter_subset_left
  inf_le_right _ _ := Finset.inter_subset_right
  le_inf _ _ _ := Finset.subset_inter

instance (n : ℕ) : DecidableLE (PuncturedCube n) :=
  fun S T ↦ inferInstanceAs (Decidable (S.1 ⊆ T.1))

@[simp]
theorem le_iff_subset {n : ℕ} {S T : PuncturedCube n} : S ≤ T ↔ S.1 ⊆ T.1 :=
  Iff.rfl

@[simp]
theorem mk_le_mk {n : ℕ} {S T : Finset (Fin n)} {hS : S ≠ Finset.univ} {hT : T ≠ Finset.univ} :
    (⟨S, hS⟩ : PuncturedCube n) ≤ ⟨T, hT⟩ ↔ S ⊆ T :=
  Iff.rfl

@[simp]
theorem val_inf {n : ℕ} (S T : PuncturedCube n) : (S ⊓ T).1 = S.1 ∩ T.1 :=
  rfl

/-- Every proper face `S : PuncturedCube n` omits at least one coordinate `k ∉ S.1`. -/
theorem exists_not_mem {n : ℕ} (S : PuncturedCube n) : ∃ k : Fin n, k ∉ S.1 := by
  by_contra hall
  push_neg at hall
  exact S.2 (Finset.eq_univ_iff_forall.mpr hall)

/-- The empty face `∅ ⊊ [n]` inside `PuncturedCube n` whenever `1 ≤ n`. -/
def emptyFace {n : ℕ} (hn : 1 ≤ n) : PuncturedCube n :=
  ⟨∅, fun h ↦ by
    have hmem : (⟨0, hn⟩ : Fin n) ∈ (∅ : Finset (Fin n)) := by
      rw [h]
      exact Finset.mem_univ _
    exact Finset.notMem_empty _ hmem⟩

/-- `emptyFace hn` is the bottom element below every `S : PuncturedCube n`. -/
theorem emptyFace_le {n : ℕ} (hn : 1 ≤ n) (S : PuncturedCube n) :
    emptyFace hn ≤ S :=
  Finset.empty_subset S.1

/-- Singleton coordinate face `{i} ⊊ [n]` inside `PuncturedCube n` whenever `2 ≤ n`. -/
def singletonFace {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : PuncturedCube n :=
  ⟨{i}, fun h ↦ by
    have h0 : (⟨0, by omega⟩ : Fin n) ∈ ({i} : Finset (Fin n)) :=
      h.symm ▸ Finset.mem_univ _
    have h1 : (⟨1, by omega⟩ : Fin n) ∈ ({i} : Finset (Fin n)) :=
      h.symm ▸ Finset.mem_univ _
    rw [Finset.mem_singleton] at h0 h1
    have heq : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := h0.trans h1.symm
    have hval : (0 : ℕ) = 1 := congrArg Fin.val heq
    omega⟩

/-- `PuncturedCube n` is `Nontrivial` whenever `2 ≤ n` (witnessed by `∅ ≠ {0}`). -/
theorem nontrivial_of_two_le {n : ℕ} (hn : 2 ≤ n) : Nontrivial (PuncturedCube n) := by
  refine ⟨⟨emptyFace (by omega), singletonFace hn ⟨0, by omega⟩, fun h ↦ ?_⟩⟩
  have hmem : (⟨0, by omega⟩ : Fin n) ∈ (∅ : Finset (Fin n)) := by
    have hv := congrArg Subtype.val h
    change (∅ : Finset (Fin n)) = {⟨0, by omega⟩} at hv
    rw [hv]
    exact Finset.mem_singleton_self _
  exact Finset.notMem_empty _ hmem

/-- Exact cardinality formula `Fintype.card (PuncturedCube n) = 2 ^ n - 1`. -/
theorem card_eq (n : ℕ) : Fintype.card (PuncturedCube n) = 2 ^ n - 1 := by
  change Fintype.card {S : Finset (Fin n) // S ≠ Finset.univ} = 2 ^ n - 1
  rw [Fintype.card_subtype]
  have hfilt :
      Finset.univ.filter (fun S : Finset (Fin n) ↦ S ≠ Finset.univ) =
        Finset.univ.erase Finset.univ := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

end PuncturedCube

/-! ## Section 2: Intersective Cubical Poset Diagrams, Cocones, and `n-DAP` -/

/-- A functorial diagram of `OrientedGradedPoset`s and closed cellular embeddings indexed by the
punctured `n`-cube `PuncturedCube n`. -/
structure CubicalPosetDiagram (n : ℕ) : Type (u + 1) where
  /-- Carrier type assigned to each proper face `S : PuncturedCube n`. -/
  obj : PuncturedCube n → Type u
  /-- `OrientedGradedPoset` instance on each face `obj S`. -/
  poset : ∀ S : PuncturedCube n, OrientedGradedPoset (obj S) := by infer_instance
  /-- Transition morphism along an inclusion `S ≤ T` in `PuncturedCube n`. -/
  map : ∀ {S T : PuncturedCube n}, S ≤ T → obj S → obj T
  /-- Every face transition map is a closed cellular embedding. -/
  map_closed : ∀ {S T : PuncturedCube n} (h : S ≤ T),
    @IsClosedEmbedding (obj S) (obj T) (poset S) (poset T) (map h)
  /-- Identity functoriality on each face `S`. -/
  map_id : ∀ (S : PuncturedCube n) (x : obj S), map (le_refl S) x = x
  /-- Composition functoriality along `R ≤ S ≤ T`. -/
  map_comp : ∀ {R S T : PuncturedCube n} (hRS : R ≤ S) (hST : S ≤ T) (x : obj R),
    map hST (map hRS x) = map (le_trans hRS hST) x

attribute [instance] CubicalPosetDiagram.poset

namespace CubicalPosetDiagram

/-- An **intersective** punctured `n`-cube diagram satisfies exact face-intersection pullbacks
inside every proper face `U`: whenever `x : D.obj S` and `y : D.obj T` map to the same cell in
`D.obj U` (`S ≤ U`, `T ≤ U`), they arise from a common ancestor `z : D.obj (S ⊓ T)`. -/
def IsIntersective {n : ℕ} (D : CubicalPosetDiagram.{u} n) : Prop :=
  ∀ ⦃S T U : PuncturedCube n⦄ (hSU : S ≤ U) (hTU : T ≤ U) (x : D.obj S) (y : D.obj T),
    D.map hSU x = D.map hTU y →
      ∃ z : D.obj (S ⊓ T), D.map inf_le_left z = x ∧ D.map inf_le_right z = y

/-- Set-range intersection reformulation of `IsIntersective` inside any proper face `U`. -/
theorem IsIntersective.range_inter_eq {n : ℕ} {D : CubicalPosetDiagram.{u} n}
    (hInt : D.IsIntersective) {S T U : PuncturedCube n} (hSU : S ≤ U) (hTU : T ≤ U) :
    Set.range (D.map hSU) ∩ Set.range (D.map hTU) =
      Set.range (D.map (le_trans (inf_le_left : S ⊓ T ≤ S) hSU)) := by
  ext u
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    rcases hInt hSU hTU x y hy.symm with ⟨z, hzx, _⟩
    exact ⟨z, by rw [← D.map_comp (inf_le_left : S ⊓ T ≤ S) hSU z, hzx]⟩
  · rintro ⟨z, rfl⟩
    refine ⟨⟨D.map (inf_le_left : S ⊓ T ≤ S) z,
      D.map_comp (inf_le_left : S ⊓ T ≤ S) hSU z⟩, ?_⟩
    exact ⟨D.map (inf_le_right : S ⊓ T ≤ T) z,
      D.map_comp (inf_le_right : S ⊓ T ≤ T) hTU z⟩

end CubicalPosetDiagram

/-- A **closed-embedding cocone** from `D : CubicalPosetDiagram n` into an ambient
`OrientedGradedPoset Q`. -/
structure CubicalCocone {n : ℕ} (D : CubicalPosetDiagram.{u} n) (Q : Type v)
    [OrientedGradedPoset Q] where
  /-- Cocone leg `D.obj S → Q` on each proper face `S : PuncturedCube n`. -/
  leg : ∀ S : PuncturedCube n, D.obj S → Q
  /-- Every cocone leg is a closed cellular embedding. -/
  leg_closed : ∀ S : PuncturedCube n, IsClosedEmbedding (leg S)
  /-- Naturality `leg T (D.map h x) = leg S x` along every face inclusion `h : S ≤ T`. -/
  comm : ∀ {S T : PuncturedCube n} (h : S ≤ T) (x : D.obj S), leg T (D.map h x) = leg S x

/-- A `CubicalCocone` satisfies **Disjoint `n`-Amalgamation (`n-DAP`)** when pairwise intersections
of leg images agree globally with the image of the binary meet `S ⊓ T`. -/
def IsDisjointCubicalAmalgamation {n : ℕ} {D : CubicalPosetDiagram.{u} n} {Q : Type v}
    [OrientedGradedPoset Q] (C : CubicalCocone D Q) : Prop :=
  ∀ S T : PuncturedCube n,
    Set.range (C.leg S) ∩ Set.range (C.leg T) = Set.range (C.leg (S ⊓ T))

/-- Elementwise pullback characterization of `IsDisjointCubicalAmalgamation`:
`C.leg S x = C.leg T y ↔ ∃ z : D.obj (S ⊓ T), D.map inf_le_left z = x ∧ D.map inf_le_right z = y`.
-/
theorem IsDisjointCubicalAmalgamation.leg_eq_iff {n : ℕ} {D : CubicalPosetDiagram.{u} n}
    {Q : Type v} [OrientedGradedPoset Q] {C : CubicalCocone D Q}
    (hDisj : IsDisjointCubicalAmalgamation C) (S T : PuncturedCube n)
    (x : D.obj S) (y : D.obj T) :
    C.leg S x = C.leg T y ↔
      ∃ z : D.obj (S ⊓ T), D.map inf_le_left z = x ∧ D.map inf_le_right z = y := by
  constructor
  · intro heq
    have hmem : C.leg S x ∈ Set.range (C.leg S) ∩ Set.range (C.leg T) :=
      ⟨⟨x, rfl⟩, ⟨y, heq.symm⟩⟩
    rw [hDisj S T] at hmem
    rcases hmem with ⟨z, hz⟩
    refine ⟨z, ?_, ?_⟩
    · apply (C.leg_closed S).injective
      rw [C.comm inf_le_left z, hz]
    · apply (C.leg_closed T).injective
      rw [C.comm inf_le_right z, hz, heq]
  · rintro ⟨z, rfl, rfl⟩
    rw [C.comm inf_le_left z, C.comm inf_le_right z]

/-- Any `CubicalPosetDiagram` admitting a disjoint `CubicalCocone` must be `IsIntersective`. -/
theorem IsDisjointCubicalAmalgamation.isIntersective {n : ℕ} {D : CubicalPosetDiagram.{u} n}
    {Q : Type v} [OrientedGradedPoset Q] {C : CubicalCocone D Q}
    (hDisj : IsDisjointCubicalAmalgamation C) : D.IsIntersective := by
  intro S T U hSU hTU x y hmap
  have heq : C.leg S x = C.leg T y := by
    rw [← C.comm hSU x, ← C.comm hTU y, hmap]
  exact (hDisj.leg_eq_iff S T x y).mp heq

/-- Predicate asserting that `D : CubicalPosetDiagram n` admits a disjoint cubical `n`-amalgamation
cocone (`n-DAP`) inside `OrientedGradedPoset`s in the same universe. -/
def HasCubicalNDAP {n : ℕ} (D : CubicalPosetDiagram.{u} n) : Prop :=
  ∃ (Q : Type u) (hQ : OrientedGradedPoset Q) (C : @CubicalCocone n D Q hQ),
    @IsDisjointCubicalAmalgamation n D Q hQ C

/-- Necessity of `IsIntersective` for `HasCubicalNDAP`. -/
theorem HasCubicalNDAP.isIntersective {n : ℕ} {D : CubicalPosetDiagram.{u} n}
    (h : HasCubicalNDAP D) : D.IsIntersective := by
  rcases h with ⟨Q, hQ, C, hDisj⟩
  letI : OrientedGradedPoset Q := hQ
  exact hDisj.isIntersective

/-! ## Section 3: Theorem 10B Part 1 — Minimal-Support Quotient-Free `CubicalAmalgam` -/

namespace CubicalPosetDiagram

/-- A cell `x : D.obj S` is **minimal-support** (`D.IsMinimalCell S x`) if no strictly smaller
proper face `A < S` contains a preimage of `x` along `D.map hAS`. -/
def IsMinimalCell {n : ℕ} (D : CubicalPosetDiagram.{u} n) (S : PuncturedCube n) (x : D.obj S) :
    Prop :=
  ∀ ⦃A : PuncturedCube n⦄ (hAS : A ≤ S), x ∈ Set.range (D.map hAS) → S ≤ A

end CubicalPosetDiagram

/-- Quotient-free **minimal-support amalgamation carrier** of `D : CubicalPosetDiagram n`,
consisting of pairs `⟨⟨S, x⟩, hmin⟩` with `D.IsMinimalCell S x`. -/
def CubicalAmalgam {n : ℕ} (D : CubicalPosetDiagram.{u} n) : Type u :=
  {p : Σ S : PuncturedCube n, D.obj S // D.IsMinimalCell p.1 p.2}

noncomputable instance instFintypeCubicalAmalgam {n : ℕ} (D : CubicalPosetDiagram.{u} n)
    [∀ S, Fintype (D.obj S)] : Fintype (CubicalAmalgam D) := by
  classical
  exact Subtype.fintype (fun p : Σ S : PuncturedCube n, D.obj S ↦ D.IsMinimalCell p.1 p.2)

namespace CubicalAmalgam

/-- Extensionality of minimal-support cells in `CubicalAmalgam D`. -/
@[ext]
theorem ext {n : ℕ} {D : CubicalPosetDiagram.{u} n} {p q : CubicalAmalgam D}
    (h : p.1 = q.1) : p = q :=
  Subtype.ext h

/-- Direct face-order on `CubicalAmalgam D`: `p ≤ q` holds iff `p.1.1 ≤ q.1.1` and the pushed-
forward cell `D.map h p.1.2` lies below `q.1.2` in `D.obj q.1.1`. -/
def leRel {n : ℕ} (D : CubicalPosetDiagram.{u} n) (p q : CubicalAmalgam D) : Prop :=
  ∃ h : p.1.1 ≤ q.1.1, D.map h p.1.2 ≤ q.1.2

/-- Non-dependent coface orientation sign on `CubicalAmalgam D`. -/
def signFn {n : ℕ} (D : CubicalPosetDiagram.{u} n) (p q : CubicalAmalgam D) : Bool :=
  if h : p.1.1 ≤ q.1.1 then OrientedGradedPoset.sign (D.map h p.1.2) q.1.2 else false

/-- Canonical `OrientedGradedPoset` structure on the quotient-free minimal-support carrier
`CubicalAmalgam D` (transitivity and antisymmetry hold directly without transitive closure!). -/
instance instOrientedGradedPoset {n : ℕ} (D : CubicalPosetDiagram.{u} n) :
    OrientedGradedPoset (CubicalAmalgam D) where
  le := leRel D
  le_refl p := ⟨le_refl p.1.1, by rw [D.map_id]⟩
  le_trans p q r := by
    rintro ⟨h₁, hle₁⟩ ⟨h₂, hle₂⟩
    refine ⟨le_trans h₁ h₂, ?_⟩
    rw [← D.map_comp h₁ h₂ p.1.2]
    exact le_trans ((D.map_closed h₂).mono hle₁) hle₂
  le_antisymm p q := by
    rintro ⟨h₁, hle₁⟩ ⟨h₂, hle₂⟩
    rcases p with ⟨⟨S, x⟩, hp⟩
    rcases q with ⟨⟨T, y⟩, hq⟩
    have hST : S = T := le_antisymm h₁ h₂
    subst hST
    have hx : x ≤ y := by simpa only [D.map_id] using hle₁
    have hy : y ≤ x := by simpa only [D.map_id] using hle₂
    exact Subtype.ext (congrArg (Sigma.mk S) (le_antisymm hx hy))
  dim p := OrientedGradedPoset.dim p.1.2
  dim_strictMono p q hlt := by
    rcases hlt with ⟨⟨h, hle⟩, hnot⟩
    have hne : D.map h p.1.2 ≠ q.1.2 := by
      intro heq
      have hqp : q.1.1 ≤ p.1.1 := q.2 h ⟨p.1.2, heq⟩
      rcases p with ⟨⟨S, x⟩, hp⟩
      rcases q with ⟨⟨T, y⟩, hq⟩
      have hST : S = T := le_antisymm h hqp
      subst hST
      have hxy : x = y := by simpa only [D.map_id] using heq
      subst hxy
      exact hnot ⟨le_refl S, by rw [D.map_id]⟩
    have hlt_map : D.map h p.1.2 < q.1.2 := lt_of_le_of_ne hle hne
    have hdim := OrientedGradedPoset.dim_strictMono hlt_map
    rwa [(D.map_closed h).map_dim p.1.2] at hdim
  sign := signFn D

@[simp]
theorem le_iff {n : ℕ} {D : CubicalPosetDiagram.{u} n} {p q : CubicalAmalgam D} :
    p ≤ q ↔ ∃ h : p.1.1 ≤ q.1.1, D.map h p.1.2 ≤ q.1.2 :=
  Iff.rfl

@[simp]
theorem dim_eq {n : ℕ} {D : CubicalPosetDiagram.{u} n} (p : CubicalAmalgam D) :
    OrientedGradedPoset.dim p = OrientedGradedPoset.dim p.1.2 :=
  rfl

/-- Uniqueness of minimal-support ancestors inside any common upper face `U` under
`D.IsIntersective`. -/
theorem minimalCell_unique {n : ℕ} {D : CubicalPosetDiagram.{u} n} (hInt : D.IsIntersective)
    {p q : CubicalAmalgam D} {U : PuncturedCube n}
    (hpU : p.1.1 ≤ U) (hqU : q.1.1 ≤ U) (heq : D.map hpU p.1.2 = D.map hqU q.1.2) :
    p = q := by
  rcases hInt hpU hqU p.1.2 q.1.2 heq with ⟨z, hzp, hzq⟩
  have hpq : p.1.1 ≤ q.1.1 := le_trans (p.2 inf_le_left ⟨z, hzp⟩) inf_le_right
  have hqp : q.1.1 ≤ p.1.1 := le_trans (q.2 inf_le_right ⟨z, hzq⟩) inf_le_left
  rcases p with ⟨⟨S, x⟩, hp⟩
  rcases q with ⟨⟨T, y⟩, hq⟩
  have hST : S = T := le_antisymm hpq hqp
  subst hST
  have hxy : x = y := (D.map_closed hpU).injective heq
  subst hxy
  rfl

/-- Existence of a minimal-support ancestor `p : CubicalAmalgam D` for every face `S` and cell
`x : D.obj S` under `D.IsIntersective` (by `Nat.find` on support cardinality `A.1.card`). -/
theorem exists_minimalAncestor {n : ℕ} {D : CubicalPosetDiagram.{u} n} (hInt : D.IsIntersective)
    (S : PuncturedCube n) (x : D.obj S) :
    ∃ p : CubicalAmalgam D, ∃ h : p.1.1 ≤ S, D.map h p.1.2 = x := by
  classical
  let P : ℕ → Prop := fun k ↦
    ∃ A : PuncturedCube n, A.1.card = k ∧ ∃ hAS : A ≤ S, x ∈ Set.range (D.map hAS)
  have hex : ∃ k : ℕ, P k := ⟨S.1.card, S, rfl, le_refl S, x, D.map_id S x⟩
  rcases Nat.find_spec hex with ⟨A₀, hk₀, hA₀S, x₀, hx₀⟩
  have hmin : D.IsMinimalCell A₀ x₀ := by
    intro A hAA₀ ⟨a, ha⟩
    have hAS : A ≤ S := le_trans hAA₀ hA₀S
    have haS : D.map hAS a = x := by rw [← D.map_comp hAA₀ hA₀S a, ha, hx₀]
    rcases hInt hA₀S hAS x₀ a (hx₀.trans haS.symm) with ⟨z, hz₀, _⟩
    have hInfS : A₀ ⊓ A ≤ S := le_trans inf_le_left hA₀S
    have hzS : D.map hInfS z = x := by rw [← D.map_comp inf_le_left hA₀S z, hz₀, hx₀]
    have hcard : Nat.find hex ≤ (A₀ ⊓ A).1.card :=
      Nat.find_min' hex ⟨A₀ ⊓ A, rfl, hInfS, z, hzS⟩
    rw [← hk₀] at hcard
    have heq_set : (A₀ ⊓ A).1 = A₀.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard
    have heq_face : A₀ ⊓ A = A₀ := PuncturedCube.ext heq_set
    exact heq_face ▸ inf_le_right
  exact ⟨⟨⟨A₀, x₀⟩, hmin⟩, hA₀S, hx₀⟩

end CubicalAmalgam

/-- Canonical cocone leg `D.obj S → CubicalAmalgam D` sending each cell `x : D.obj S` to its
unique minimal-support ancestor. -/
noncomputable def amalgamLeg {n : ℕ} {D : CubicalPosetDiagram.{u} n} (hInt : D.IsIntersective)
    (S : PuncturedCube n) (x : D.obj S) : CubicalAmalgam D :=
  Classical.choose (CubicalAmalgam.exists_minimalAncestor hInt S x)

/-- Support-inclusion witness `(amalgamLeg hInt S x).1.1 ≤ S`. -/
theorem amalgamLeg_face_le {n : ℕ} {D : CubicalPosetDiagram.{u} n} (hInt : D.IsIntersective)
    (S : PuncturedCube n) (x : D.obj S) :
    (amalgamLeg hInt S x).1.1 ≤ S :=
  (Classical.choose_spec (CubicalAmalgam.exists_minimalAncestor hInt S x)).choose

/-- Reconstruction identity `D.map (amalgamLeg_face_le hInt S x) (amalgamLeg hInt S x).1.2 = x`.
-/
@[simp]
theorem map_amalgamLeg {n : ℕ} {D : CubicalPosetDiagram.{u} n} (hInt : D.IsIntersective)
    (S : PuncturedCube n) (x : D.obj S) :
    D.map (amalgamLeg_face_le hInt S x) (amalgamLeg hInt S x).1.2 = x :=
  (Classical.choose_spec (CubicalAmalgam.exists_minimalAncestor hInt S x)).choose_spec

/-- Exact characterization of `amalgamLeg`: `p = amalgamLeg hInt S x` iff `p.1.1 ≤ S` pushes
`p.1.2` forward to `x`. -/
theorem eq_amalgamLeg_iff {n : ℕ} {D : CubicalPosetDiagram.{u} n} (hInt : D.IsIntersective)
    {p : CubicalAmalgam D} {S : PuncturedCube n} {x : D.obj S} :
    p = amalgamLeg hInt S x ↔ ∃ h : p.1.1 ≤ S, D.map h p.1.2 = x := by
  constructor
  · rintro rfl
    exact ⟨amalgamLeg_face_le hInt S x, map_amalgamLeg hInt S x⟩
  · rintro ⟨h, hmap⟩
    exact CubicalAmalgam.minimalCell_unique hInt h (amalgamLeg_face_le hInt S x)
      (hmap.trans (map_amalgamLeg hInt S x).symm)

/-- Every minimal cell `p : CubicalAmalgam D` is fixed by `amalgamLeg` on its own support face. -/
@[simp]
theorem amalgamLeg_self {n : ℕ} {D : CubicalPosetDiagram.{u} n} (hInt : D.IsIntersective)
    (p : CubicalAmalgam D) :
    amalgamLeg hInt p.1.1 p.1.2 = p :=
  ((eq_amalgamLeg_iff hInt).mpr ⟨le_refl p.1.1, D.map_id p.1.1 p.1.2⟩).symm

/-- Transition invariance / cocone commutativity: `amalgamLeg` commutes with all `D.map hST`. -/
@[simp]
theorem amalgamLeg_comm {n : ℕ} {D : CubicalPosetDiagram.{u} n} (hInt : D.IsIntersective)
    {S T : PuncturedCube n} (hST : S ≤ T) (x : D.obj S) :
    amalgamLeg hInt T (D.map hST x) = amalgamLeg hInt S x := by
  symm
  refine (eq_amalgamLeg_iff hInt).mpr ⟨le_trans (amalgamLeg_face_le hInt S x) hST, ?_⟩
  rw [← D.map_comp (amalgamLeg_face_le hInt S x) hST, map_amalgamLeg]

/-- Every canonical cocone leg `amalgamLeg hInt S : D.obj S → CubicalAmalgam D` is a closed
cellular embedding (`IsClosedEmbedding`). -/
theorem amalgamLeg_isClosedEmbedding {n : ℕ} {D : CubicalPosetDiagram.{u} n}
    (hInt : D.IsIntersective) (S : PuncturedCube n) :
    IsClosedEmbedding (amalgamLeg hInt S) where
  mono x y hxy := by
    let q := amalgamLeg hInt S y
    have hy : y = D.map (amalgamLeg_face_le hInt S y) q.1.2 :=
      (map_amalgamLeg hInt S y).symm
    have hx_le : x ≤ D.map (amalgamLeg_face_le hInt S y) q.1.2 := hy ▸ hxy
    rcases (D.map_closed (amalgamLeg_face_le hInt S y)).downward_closed hx_le with
      ⟨a, ha_le, ha_eq⟩
    have hp_eq : amalgamLeg hInt S x = amalgamLeg hInt q.1.1 a := by
      rw [← ha_eq, amalgamLeg_comm hInt (amalgamLeg_face_le hInt S y) a]
    rw [hp_eq]
    refine ⟨amalgamLeg_face_le hInt q.1.1 a, ?_⟩
    rw [map_amalgamLeg hInt q.1.1 a]
    exact ha_le
  injective x y hxy := by
    rcases (eq_amalgamLeg_iff hInt).mp hxy with ⟨h, hmap⟩
    exact (map_amalgamLeg hInt S x).symm.trans hmap
  downward_closed y r hr := by
    rcases hr with ⟨hrq, hle_rq⟩
    let hrS : r.1.1 ≤ S := le_trans hrq (amalgamLeg_face_le hInt S y)
    refine ⟨D.map hrS r.1.2, ?_, ?_⟩
    · calc
        D.map hrS r.1.2 = D.map (amalgamLeg_face_le hInt S y) (D.map hrq r.1.2) :=
          (D.map_comp hrq (amalgamLeg_face_le hInt S y) r.1.2).symm
        _ ≤ D.map (amalgamLeg_face_le hInt S y) (amalgamLeg hInt S y).1.2 :=
          (D.map_closed (amalgamLeg_face_le hInt S y)).mono hle_rq
        _ = y := map_amalgamLeg hInt S y
    · exact ((eq_amalgamLeg_iff hInt).mpr ⟨hrS, rfl⟩).symm
  map_dim x := by
    change OrientedGradedPoset.dim (amalgamLeg hInt S x).1.2 = OrientedGradedPoset.dim x
    have h := (D.map_closed (amalgamLeg_face_le hInt S x)).map_dim (amalgamLeg hInt S x).1.2
    rw [map_amalgamLeg hInt S x] at h
    exact h.symm
  map_sign x y hfac := by
    have hle_pq : amalgamLeg hInt S x ≤ amalgamLeg hInt S y := by
      let q := amalgamLeg hInt S y
      have hx_le : x ≤ D.map (amalgamLeg_face_le hInt S y) q.1.2 :=
        (map_amalgamLeg hInt S y).symm ▸ hfac.1
      rcases (D.map_closed (amalgamLeg_face_le hInt S y)).downward_closed hx_le with
        ⟨a, ha_le, ha_eq⟩
      have hp_eq : amalgamLeg hInt S x = amalgamLeg hInt q.1.1 a := by
        rw [← ha_eq, amalgamLeg_comm hInt (amalgamLeg_face_le hInt S y) a]
      rw [hp_eq]
      exact ⟨amalgamLeg_face_le hInt q.1.1 a, (map_amalgamLeg hInt q.1.1 a).symm ▸ ha_le⟩
    rcases hle_pq with ⟨hpq, _⟩
    change CubicalAmalgam.signFn D (amalgamLeg hInt S x) (amalgamLeg hInt S y) =
      OrientedGradedPoset.sign x y
    simp only [CubicalAmalgam.signFn, dif_pos hpq]
    let hyS := amalgamLeg_face_le hInt S y
    have hmap_x : D.map hyS (D.map hpq (amalgamLeg hInt S x).1.2) = x := by
      rw [D.map_comp hpq hyS]
      exact map_amalgamLeg hInt S x
    have hmap_y : D.map hyS (amalgamLeg hInt S y).1.2 = y :=
      map_amalgamLeg hInt S y
    have hfac_q : IsFacet (D.map hpq (amalgamLeg hInt S x).1.2) (amalgamLeg hInt S y).1.2 := by
      rw [← (D.map_closed hyS).map_isFacet_iff, hmap_x, hmap_y]
      exact hfac
    have hs := (D.map_closed hyS).map_sign hfac_q
    rw [hmap_x, hmap_y] at hs
    exact hs.symm

/-- Canonical `CubicalCocone` on `CubicalAmalgam D` for an intersective `CubicalPosetDiagram`. -/
noncomputable def cubicalAmalgamCocone {n : ℕ} {D : CubicalPosetDiagram.{u} n}
    (hInt : D.IsIntersective) : CubicalCocone D (CubicalAmalgam D) where
  leg := amalgamLeg hInt
  leg_closed := amalgamLeg_isClosedEmbedding hInt
  comm := amalgamLeg_comm hInt

/-- Global `n-DAP` range-intersection law on `cubicalAmalgamCocone`:
`Set.range (amalgamLeg hInt S) ∩ Set.range (amalgamLeg hInt T) =`
`Set.range (amalgamLeg hInt (S ⊓ T))`. -/
theorem cubicalAmalgamCocone_isDisjoint {n : ℕ} {D : CubicalPosetDiagram.{u} n}
    (hInt : D.IsIntersective) :
    IsDisjointCubicalAmalgamation (cubicalAmalgamCocone hInt) := by
  intro S T
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    let q := amalgamLeg hInt S x
    have hS : q.1.1 ≤ S := amalgamLeg_face_le hInt S x
    rcases (eq_amalgamLeg_iff hInt).mp hy.symm with ⟨hT, _⟩
    have hST : q.1.1 ≤ S ⊓ T := le_inf hS hT
    refine ⟨D.map hST q.1.2, ?_⟩
    change amalgamLeg hInt (S ⊓ T) (D.map hST q.1.2) = q
    rw [amalgamLeg_comm hInt hST q.1.2, amalgamLeg_self hInt q]
  · rintro ⟨z, rfl⟩
    exact ⟨⟨D.map inf_le_left z, amalgamLeg_comm hInt inf_le_left z⟩,
      ⟨D.map inf_le_right z, amalgamLeg_comm hInt inf_le_right z⟩⟩

/-- **Theorem 10B Part 1 — All-`n` Disjoint `n`-Amalgamation (`n-DAP`) for Closed
`OrientedGradedPoset` Diagrams (`cubical_ndap_closed_oriented_poset`):**
For every `n : ℕ` and every intersective `D : CubicalPosetDiagram n`, the quotient-free minimal-
support carrier `CubicalAmalgam D` equips `cubicalAmalgamCocone hInt` with closed cellular
embeddings commuting with all face maps, global `n-DAP` range & elementwise pullback laws, and
principal-closure order isomorphisms `cl (amalgamLeg hInt S x) ≃o cl x`. -/
theorem cubical_ndap_closed_oriented_poset {n : ℕ} {D : CubicalPosetDiagram.{u} n}
    (hInt : D.IsIntersective) :
    let j := amalgamLeg hInt
    (∀ S : PuncturedCube n, IsClosedEmbedding (j S)) ∧
      (∀ {S T : PuncturedCube n} (h : S ≤ T) (x : D.obj S), j T (D.map h x) = j S x) ∧
      (∀ S T : PuncturedCube n, Set.range (j S) ∩ Set.range (j T) = Set.range (j (S ⊓ T))) ∧
      (∀ (S T : PuncturedCube n) (x : D.obj S) (y : D.obj T),
        j S x = j T y ↔
          ∃ z : D.obj (S ⊓ T), D.map inf_le_left z = x ∧ D.map inf_le_right z = y) ∧
      (∀ (S : PuncturedCube n) (x : D.obj S), Nonempty (cl (j S x) ≃o cl x)) ∧
      HasCubicalNDAP D := by
  have hDisj := cubicalAmalgamCocone_isDisjoint hInt
  refine ⟨amalgamLeg_isClosedEmbedding hInt,
    fun h x ↦ amalgamLeg_comm hInt h x,
    hDisj,
    fun S T x y ↦ hDisj.leg_eq_iff S T x y,
    fun S x ↦ ⟨(amalgamLeg_isClosedEmbedding hInt S).clOrderIso x⟩,
    ⟨CubicalAmalgam D, inferInstance, cubicalAmalgamCocone hInt, hDisj⟩⟩

/-- Exact equivalence between `HasCubicalNDAP D` and `D.IsIntersective` for all `n : ℕ`. -/
theorem hasCubicalNDAP_iff_isIntersective {n : ℕ} (D : CubicalPosetDiagram.{u} n) :
    HasCubicalNDAP D ↔ D.IsIntersective :=
  ⟨HasCubicalNDAP.isIntersective, fun hInt ↦ (cubical_ndap_closed_oriented_poset hInt).2.2.2.2.2⟩

/-- A graded poset `P` is **covering-graded** when every order cover `a ⋖ b` (`CovBy a b`) has
codimension `1` (`IsFacet a b`, i.e. `dim b = dim a + 1`). -/
def IsCoveringGraded (P : Type u) [OrientedGradedPoset P] : Prop :=
  ∀ ⦃a b : P⦄, a ⋖ b → IsFacet a b

/-- Every closed cellular embedding `f : P → Q` preserves and reflects covering relations
`a ⋖ b`. -/
theorem IsClosedEmbedding.map_covBy_iff {P : Type*} {Q : Type*}
    [OrientedGradedPoset P] [OrientedGradedPoset Q]
    {f : P → Q} (hf : IsClosedEmbedding f) {a b : P} :
    f a ⋖ f b ↔ a ⋖ b := by
  constructor
  · rintro ⟨hab, hbtw⟩
    have hle_ab : a ≤ b := by
      rcases hf.downward_closed hab.le with ⟨a', ha'b, ha'⟩
      exact (hf.injective ha').symm ▸ ha'b
    have hlt_ab : a < b := lt_of_le_of_ne hle_ab (fun h ↦ hab.ne (h ▸ rfl))
    refine ⟨hlt_ab, fun {c} hac hcb ↦ @hbtw (f c) ?_ ?_⟩
    · exact lt_of_le_of_ne (hf.mono hac.le) (fun h ↦ hac.ne (hf.injective h))
    · exact lt_of_le_of_ne (hf.mono hcb.le) (fun h ↦ hcb.ne (hf.injective h))
  · rintro ⟨hab, hbtw⟩
    refine ⟨lt_of_le_of_ne (hf.mono hab.le) (fun h ↦ hab.ne (hf.injective h)), fun {z} hfz hzf ↦ ?_⟩
    rcases hf.downward_closed hzf.le with ⟨c, hcb, rfl⟩
    have hac_le : a ≤ c := by
      rcases hf.downward_closed hfz.le with ⟨a', ha'c, ha'⟩
      exact (hf.injective ha').symm ▸ ha'c
    have hac : a < c := lt_of_le_of_ne hac_le (fun h ↦ hfz.ne (h ▸ rfl))
    have hcb_lt : c < b := lt_of_le_of_ne hcb (fun h ↦ hzf.ne (h ▸ rfl))
    exact hbtw hac hcb_lt

/-- Closed cellular embeddings reflect `IsCoveringGraded` downward from codomain to domain. -/
theorem IsClosedEmbedding.isCoveringGraded {P : Type*} {Q : Type*}
    [OrientedGradedPoset P] [OrientedGradedPoset Q]
    {f : P → Q} (hf : IsClosedEmbedding f) (hQ : IsCoveringGraded Q) :
    IsCoveringGraded P := fun _ _ hab ↦
  hf.map_isFacet_iff.mp (hQ (hf.map_covBy_iff.mpr hab))

/-- **Covering-Graded Transfer for `CubicalAmalgam D` (`isCoveringGraded_cubicalAmalgam`):**
if every face `D.obj S` is covering-graded, then the quotient-free cubical amalgamation
`CubicalAmalgam D` is covering-graded. -/
theorem isCoveringGraded_cubicalAmalgam {n : ℕ} {D : CubicalPosetDiagram.{u} n}
    (hInt : D.IsIntersective) (hCov : ∀ S : PuncturedCube n, IsCoveringGraded (D.obj S)) :
    IsCoveringGraded (CubicalAmalgam D) := by
  intro p q hpq
  let S : PuncturedCube n := q.1.1
  let j := amalgamLeg hInt S
  have hj := amalgamLeg_isClosedEmbedding hInt S
  have hle : p ≤ q := hpq.1.le
  have hp_eq : j (D.map hle.1 p.1.2) = p :=
    (amalgamLeg_comm hInt hle.1 p.1.2).trans (amalgamLeg_self hInt p)
  have hq_eq : j q.1.2 = q := amalgamLeg_self hInt q
  rw [← hp_eq, ← hq_eq] at hpq ⊢
  exact hj.map_isFacet_iff.mpr (hCov S (hj.map_covBy_iff.mp hpq))

/-! ## Section 4: Theorem 10B Part 2 — All-`n ≥ 3` Obstruction via `facetCycleDiagram` -/

/-- Cyclic successor `i ↦ (i + 1) mod n` on `Fin n` (defined without `[NeZero n]` assumptions). -/
def finSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ i.pos⟩

/-- Explicit modular case formula for `(finSucc i).1`. -/
theorem finSucc_val {n : ℕ} (i : Fin n) :
    (finSucc i).1 = if i.1 + 1 < n then i.1 + 1 else 0 := by
  dsimp only [finSucc]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have heq : i.1 + 1 = n := by
      have hi := i.2
      omega
    rw [heq, Nat.mod_self]

/-- Agreement of `finSucc i` with `i + 1` in `Fin n` whenever `[NeZero n]` is in scope. -/
@[simp]
theorem finSucc_eq_add_one {n : ℕ} [NeZero n] (i : Fin n) : finSucc i = i + 1 := by
  apply Fin.ext
  change (i.1 + 1) % n = (i.1 + 1 % n) % n
  exact (Nat.add_mod_mod i.1 1 n).symm

/-- Injectivity of the cyclic shift `finSucc` on `Fin n`. -/
theorem finSucc_injective {n : ℕ} : Function.Injective (finSucc (n := n)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [finSucc_val] at hv
  have hi := i.2
  have hj := j.2
  split_ifs at hv <;> omega

/-- No element of `Fin n` is fixed by `finSucc` when `2 ≤ n`. -/
theorem finSucc_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finSucc i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [finSucc_val] at hv
  have hi := i.2
  split_ifs at hv <;> omega

/-- No element of `Fin n` has period `2` under `finSucc` when `3 ≤ n` (`i + 2 ≠ i`). -/
theorem finSucc_finSucc_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finSucc (finSucc i) ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [finSucc_val] at hv
  have hi := i.2
  split_ifs at hv <;> omega

/-- Underlying cell type of the directed `n`-cycle `C_n`: `Sum.inl i` represents `0`-cell `v_i` and
`Sum.inr i` represents directed `1`-cell `e_i : v_i → v_{i+1}`. -/
def DirectedCycleCell (n : ℕ) : Type :=
  Fin n ⊕ Fin n

namespace DirectedCycleCell

instance (n : ℕ) : DecidableEq (DirectedCycleCell n) :=
  inferInstanceAs (DecidableEq (Fin n ⊕ Fin n))

instance (n : ℕ) : Fintype (DirectedCycleCell n) :=
  inferInstanceAs (Fintype (Fin n ⊕ Fin n))

/-- Partial order relation on `DirectedCycleCell n`: reflexive, plus `Sum.inl i ≤ Sum.inr i` and
`Sum.inl (finSucc i) ≤ Sum.inr i`. -/
def cycleLE {n : ℕ} : DirectedCycleCell n → DirectedCycleCell n → Prop
  | Sum.inl v, Sum.inl w => v = w
  | Sum.inl v, Sum.inr e => v = e ∨ v = finSucc e
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr e₁, Sum.inr e₂ => e₁ = e₂

/-- Dimension grading on `DirectedCycleCell n` (`0` on vertices, `1` on directed edges). -/
def cycleDim {n : ℕ} : DirectedCycleCell n → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Coface sign on `DirectedCycleCell n`: `Sum.inl i` has sign `false` (`-`) in `Sum.inr i` (for
`2 ≤ n`) and `Sum.inl (finSucc i)` has sign `true` (`+`) in `Sum.inr i`. -/
def cycleSign {n : ℕ} : DirectedCycleCell n → DirectedCycleCell n → Bool
  | Sum.inl v, Sum.inr e => decide (v = finSucc e)
  | _, _ => false

instance instOrientedGradedPoset (n : ℕ) : OrientedGradedPoset (DirectedCycleCell n) where
  le := cycleLE
  le_refl x := by
    cases x with
    | inl _ => rfl
    | inr _ => rfl
  le_trans a b c hab hbc := by
    cases a with
    | inl va =>
      cases b with
      | inl vb =>
        cases c with
        | inl vc => exact hab.trans hbc
        | inr ec => exact hab ▸ hbc
      | inr eb =>
        cases c with
        | inl vc => exact False.elim hbc
        | inr ec => exact hbc ▸ hab
    | inr ea =>
      cases b with
      | inl _ => exact False.elim hab
      | inr eb =>
        cases c with
        | inl _ => exact False.elim hbc
        | inr ec => exact hab.trans hbc
  le_antisymm a b hab hba := by
    cases a with
    | inl va =>
      cases b with
      | inl vb => exact congrArg Sum.inl hab
      | inr _ => exact False.elim hba
    | inr ea =>
      cases b with
      | inl _ => exact False.elim hab
      | inr eb => exact congrArg Sum.inr hab
  dim := cycleDim
  dim_strictMono a b hlt := by
    rcases hlt with ⟨hle, hnot⟩
    cases a with
    | inl va =>
      cases b with
      | inl vb => exact False.elim (hnot (hle.symm ▸ rfl))
      | inr _ => exact Nat.zero_lt_one
    | inr ea =>
      cases b with
      | inl _ => exact False.elim hle
      | inr eb => exact False.elim (hnot (hle.symm ▸ rfl))
  sign := cycleSign

instance (n : ℕ) : DecidableLE (DirectedCycleCell n) := fun a b ↦ by
  cases a with
  | inl va =>
    cases b with
    | inl vb => exact inferInstanceAs (Decidable (va = vb))
    | inr eb => exact inferInstanceAs (Decidable (va = eb ∨ va = finSucc eb))
  | inr ea =>
    cases b with
    | inl _ => exact inferInstanceAs (Decidable False)
    | inr eb => exact inferInstanceAs (Decidable (ea = eb))

/-- Exact characterization of codimension-1 facets in `DirectedCycleCell n`. -/
theorem isFacet_iff {n : ℕ} {x y : DirectedCycleCell n} :
    IsFacet x y ↔ ∃ e : Fin n, y = Sum.inr e ∧ (x = Sum.inl e ∨ x = Sum.inl (finSucc e)) := by
  constructor
  · rintro ⟨hle, hdim⟩
    cases x with
    | inl v =>
      cases y with
      | inl _ => simp [OrientedGradedPoset.dim, cycleDim] at hdim
      | inr e =>
        refine ⟨e, rfl, ?_⟩
        rcases hle with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    | inr _ =>
      cases y with
      | inl _ => exact False.elim hle
      | inr _ => simp [OrientedGradedPoset.dim, cycleDim] at hdim
  · rintro ⟨e, rfl, rfl | rfl⟩
    · exact ⟨Or.inl rfl, rfl⟩
    · exact ⟨Or.inr rfl, rfl⟩

/-- Exact characterization of `FlowStep` in `DirectedCycleCell n` for `2 ≤ n`. -/
theorem flowStep_iff {n : ℕ} (hn : 2 ≤ n) {x y : DirectedCycleCell n} :
    FlowStep x y ↔ ∃ e : Fin n, x = Sum.inl e ∧ y = Sum.inl (finSucc e) := by
  constructor
  · rintro ⟨w, hxw, hsx, hyw, hsy⟩
    rcases isFacet_iff.mp hxw with ⟨e, hw, hx | hx⟩
    · subst hw hx
      rcases isFacet_iff.mp hyw with ⟨e', he', hy | hy⟩
      · have hee' : e' = e := Sum.inr.inj he'.symm
        subst e'
        subst hy
        exfalso
        change decide (e = finSucc e) = true at hsy
        exact finSucc_ne_self hn e (of_decide_eq_true hsy).symm
      · have hee' : e' = e := Sum.inr.inj he'.symm
        subst e'
        exact ⟨e, rfl, hy⟩
    · subst hw hx
      exfalso
      change decide (finSucc e = finSucc e) = false at hsx
      simp at hsx
  · rintro ⟨e, rfl, rfl⟩
    refine ⟨Sum.inr e, ⟨Or.inl rfl, rfl⟩, ?_, ⟨Or.inr rfl, rfl⟩, ?_⟩
    · change decide (e = finSucc e) = false
      exact decide_eq_false (fun h ↦ finSucc_ne_self hn e h.symm)
    · change decide (finSucc e = finSucc e) = true
      exact decide_eq_true rfl

end DirectedCycleCell

/-- Coordinate support `cycleCellSupport n c : Finset (Fin n)` of each cell of
`DirectedCycleCell n`: `A_i = univ \ {i, i + 1}` on `0`-cells `Sum.inl i` and `M_i = univ \ {i + 1}`
on `1`-cells `Sum.inr i`. -/
def cycleCellSupport (n : ℕ) : DirectedCycleCell n → Finset (Fin n)
  | Sum.inl i => (Finset.univ.erase i).erase (finSucc i)
  | Sum.inr i => Finset.univ.erase (finSucc i)

@[simp]
theorem mem_cycleCellSupport_inl {n : ℕ} {i k : Fin n} :
    k ∈ cycleCellSupport n (Sum.inl i) ↔ k ≠ finSucc i ∧ k ≠ i := by
  simp only [cycleCellSupport, Finset.mem_erase, Finset.mem_univ, and_true]

@[simp]
theorem mem_cycleCellSupport_inr {n : ℕ} {i k : Fin n} :
    k ∈ cycleCellSupport n (Sum.inr i) ↔ k ≠ finSucc i := by
  simp only [cycleCellSupport, Finset.mem_erase, Finset.mem_univ, and_true]

/-- Every cell of `DirectedCycleCell n` has a strictly proper support `≠ Finset.univ` (since
`finSucc i` is always omitted). -/
theorem cycleCellSupport_ne_univ {n : ℕ} (c : DirectedCycleCell n) :
    cycleCellSupport n c ≠ Finset.univ := by
  cases c with
  | inl i =>
    intro h
    have hmem : finSucc i ∈ cycleCellSupport n (Sum.inl i) := h.symm ▸ Finset.mem_univ _
    exact (mem_cycleCellSupport_inl.mp hmem).1 rfl
  | inr i =>
    intro h
    have hmem : finSucc i ∈ cycleCellSupport n (Sum.inr i) := h.symm ▸ Finset.mem_univ _
    exact (mem_cycleCellSupport_inr.mp hmem) rfl

/-- Monotonicity of `cycleCellSupport n` along face inclusions `x ≤ y` in `DirectedCycleCell n`. -/
theorem cycleCellSupport_mono {n : ℕ} {x y : DirectedCycleCell n} (hxy : x ≤ y) :
    cycleCellSupport n x ⊆ cycleCellSupport n y := by
  cases x with
  | inl v =>
    cases y with
    | inl w =>
      change v = w at hxy
      subst hxy
      exact Finset.Subset.refl _
    | inr e =>
      rcases hxy with rfl | rfl
      · intro k hk
        exact mem_cycleCellSupport_inr.mpr (mem_cycleCellSupport_inl.mp hk).1
      · intro k hk
        exact mem_cycleCellSupport_inr.mpr (mem_cycleCellSupport_inl.mp hk).2
  | inr e₁ =>
    cases y with
    | inl _ => exact False.elim hxy
    | inr e₂ =>
      change e₁ = e₂ at hxy
      subst hxy
      exact Finset.Subset.refl _

/-- Inclusion `A_i ⊆ M_i` of the source vertex support into its outgoing edge support. -/
theorem cycleCellSupport_inl_subset_inr {n : ℕ} (i : Fin n) :
    cycleCellSupport n (Sum.inl i) ⊆ cycleCellSupport n (Sum.inr i) := fun _ hk ↦
  mem_cycleCellSupport_inr.mpr (mem_cycleCellSupport_inl.mp hk).1

/-- Inclusion `A_{i+1} ⊆ M_i` of the target vertex support into its incoming edge support. -/
theorem cycleCellSupport_inl_finSucc_subset_inr {n : ℕ} (i : Fin n) :
    cycleCellSupport n (Sum.inl (finSucc i)) ⊆ cycleCellSupport n (Sum.inr i) := fun _ hk ↦
  mem_cycleCellSupport_inr.mpr (mem_cycleCellSupport_inl.mp hk).2

/-- **Key `n ≥ 3` Support-Union Identity (`A_i ∪ A_{i+1} = M_i`):** for `3 ≤ n`, the union of the
vertex supports of `v_i` and `v_{i+1}` equals the facet support `M_i` of `e_i : v_i → v_{i+1}`
(using `finSucc (finSucc i) ≠ i`). -/
theorem cycleCellSupport_union {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    cycleCellSupport n (Sum.inl i) ∪ cycleCellSupport n (Sum.inl (finSucc i)) =
      cycleCellSupport n (Sum.inr i) := by
  ext k
  simp only [Finset.mem_union, mem_cycleCellSupport_inl, mem_cycleCellSupport_inr]
  constructor
  · rintro (⟨hk, _⟩ | ⟨_, hk⟩) <;> exact hk
  · intro hk
    by_cases hki : k = i
    · subst hki
      exact Or.inr ⟨fun h ↦ finSucc_finSucc_ne_self hn k h.symm, hk⟩
    · exact Or.inl ⟨hk, hki⟩

/-- Proper-face subcomplex `{c : DirectedCycleCell n // cycleCellSupport n c ⊆ S.1}` assigned to
`S : PuncturedCube n` in `facetCycleDiagram`. -/
def FacetCycleFace (n : ℕ) (S : PuncturedCube n) : Type :=
  {c : DirectedCycleCell n // cycleCellSupport n c ⊆ S.1}

namespace FacetCycleFace

instance (n : ℕ) (S : PuncturedCube n) : DecidableEq (FacetCycleFace n S) :=
  inferInstanceAs (DecidableEq {c : DirectedCycleCell n // cycleCellSupport n c ⊆ S.1})

instance (n : ℕ) (S : PuncturedCube n) : Fintype (FacetCycleFace n S) :=
  inferInstanceAs (Fintype {c : DirectedCycleCell n // cycleCellSupport n c ⊆ S.1})

/-- Underlying cell projection `FacetCycleFace n S → DirectedCycleCell n`. -/
def val {n : ℕ} {S : PuncturedCube n} (x : FacetCycleFace n S) : DirectedCycleCell n :=
  x.1

/-- Extensionality on `FacetCycleFace n S`. -/
@[ext]
theorem ext {n : ℕ} {S : PuncturedCube n} {x y : FacetCycleFace n S} (h : x.1 = y.1) : x = y :=
  Subtype.ext h

instance instOrientedGradedPoset (n : ℕ) (S : PuncturedCube n) :
    OrientedGradedPoset (FacetCycleFace n S) where
  le x y := x.1 ≤ y.1
  le_refl x := le_refl x.1
  le_trans _ _ _ := le_trans
  le_antisymm _ _ hxy hyx := Subtype.ext (le_antisymm hxy hyx)
  dim x := OrientedGradedPoset.dim x.1
  dim_strictMono _ _ hlt := OrientedGradedPoset.dim_strictMono hlt
  sign x y := OrientedGradedPoset.sign x.1 y.1

/-- Canonical inclusion `FacetCycleFace.val` into `DirectedCycleCell n` is a closed cellular
embedding. -/
theorem isClosedEmbedding_val {n : ℕ} (S : PuncturedCube n) :
    IsClosedEmbedding (val (n := n) (S := S)) where
  mono _ _ h := h
  injective _ _ h := Subtype.ext h
  downward_closed x q hq := ⟨⟨q, Finset.Subset.trans (cycleCellSupport_mono hq) x.2⟩, hq, rfl⟩
  map_dim _ := rfl
  map_sign _ _ _ := rfl

/-- Transition inclusion `FacetCycleFace n S → FacetCycleFace n T` along `S ≤ T`. -/
def map {n : ℕ} {S T : PuncturedCube n} (hST : S ≤ T) (x : FacetCycleFace n S) :
    FacetCycleFace n T :=
  ⟨x.1, Finset.Subset.trans x.2 hST⟩

/-- Every transition map `FacetCycleFace.map hST` is a closed cellular embedding. -/
theorem isClosedEmbedding_map {n : ℕ} {S T : PuncturedCube n} (hST : S ≤ T) :
    IsClosedEmbedding (map hST) where
  mono _ _ h := h
  injective _ _ h := Subtype.ext (congrArg (fun z : FacetCycleFace n T ↦ z.1) h)
  downward_closed x q hq :=
    ⟨⟨q.1, Finset.Subset.trans (cycleCellSupport_mono hq) x.2⟩, hq, Subtype.ext rfl⟩
  map_dim _ := rfl
  map_sign _ _ _ := rfl

/-- Every proper face `FacetCycleFace n S` contains **at most one** `1`-cell `Sum.inr e`: omitting
`k₀ ∉ S.1` forces `finSucc e = k₀`. -/
theorem edge_unique {n : ℕ} {S : PuncturedCube n} {e₁ e₂ : Fin n}
    (he₁ : cycleCellSupport n (Sum.inr e₁) ⊆ S.1)
    (he₂ : cycleCellSupport n (Sum.inr e₂) ⊆ S.1) : e₁ = e₂ := by
  rcases S.exists_not_mem with ⟨k₀, hk₀⟩
  have h₁ : k₀ = finSucc e₁ := by
    by_contra hne
    exact hk₀ (he₁ (mem_cycleCellSupport_inr.mpr hne))
  have h₂ : k₀ = finSucc e₂ := by
    by_contra hne
    exact hk₀ (he₂ (mem_cycleCellSupport_inr.mpr hne))
  exact finSucc_injective (h₁.symm.trans h₂)

/-- Characterization of `FlowStep` inside `FacetCycleFace n S` for `2 ≤ n`. -/
theorem flowStep_dest {n : ℕ} (hn : 2 ≤ n) {S : PuncturedCube n} {x y : FacetCycleFace n S}
    (h : FlowStep x y) :
    ∃ e : Fin n, cycleCellSupport n (Sum.inr e) ⊆ S.1 ∧
      x.1 = Sum.inl e ∧ y.1 = Sum.inl (finSucc e) := by
  rcases h with ⟨w, hxw, hsx, hyw, hsy⟩
  have hval := isClosedEmbedding_val S
  have hstep_amb : FlowStep x.1 y.1 :=
    ⟨w.1, hval.map_isFacet_iff.mpr hxw, hsx, hval.map_isFacet_iff.mpr hyw, hsy⟩
  rcases (DirectedCycleCell.flowStep_iff hn).mp hstep_amb with ⟨e, hx, hy⟩
  rcases DirectedCycleCell.isFacet_iff.mp (hval.map_isFacet_iff.mpr hxw) with ⟨e', hw, hxe'⟩
  have hw' : w.1 = Sum.inr e' := hw
  have he_eq : e' = e := by
    rcases hxe' with h₁ | h₂
    · exact Sum.inl.inj (h₁.symm.trans hx)
    · exfalso
      have hv : e = finSucc e' := Sum.inl.inj (hx.symm.trans h₂)
      have hsx' : DirectedCycleCell.cycleSign x.1 w.1 = false := hsx
      rw [hx, hv, hw'] at hsx'
      change decide (finSucc e' = finSucc e') = false at hsx'
      simp at hsx'
  subst e'
  exact ⟨e, hw' ▸ w.2, hx, hy⟩

/-- No proper face `FacetCycleFace n S` (`2 ≤ n`) admits a composable 2-step `FlowStep` chain
`x → y → z`. -/
theorem not_step_step {n : ℕ} (hn : 2 ≤ n) {S : PuncturedCube n}
    {x y z : FacetCycleFace n S} (hxy : FlowStep x y) (hyz : FlowStep y z) : False := by
  rcases flowStep_dest hn hxy with ⟨e₁, he₁S, _, hy₁⟩
  rcases flowStep_dest hn hyz with ⟨e₂, he₂S, hy₂, _⟩
  have he₁₂ : e₁ = e₂ := edge_unique he₁S he₂S
  subst he₁₂
  have hsucc : finSucc e₁ = e₁ := Sum.inl.inj (hy₁.symm.trans hy₂)
  exact finSucc_ne_self hn e₁ hsucc

/-- In any proper face `FacetCycleFace n S` (`2 ≤ n`), `FlowReach` collapses to a single
`FlowStep`. -/
theorem flowReach_iff_flowStep {n : ℕ} (hn : 2 ≤ n) {S : PuncturedCube n}
    {x y : FacetCycleFace n S} :
    FlowReach x y ↔ FlowStep x y := by
  constructor
  · intro h
    induction h with
    | single hs => exact hs
    | tail _ hs ih => exact False.elim (not_step_step hn ih hs)
  · exact Relation.TransGen.single

/-- Every face `FacetCycleFace n S` is `IsCoveringGraded` (all cells have dimension `0` or `1`). -/
theorem isCoveringGraded_facetCycleFace {n : ℕ} (S : PuncturedCube n) :
    IsCoveringGraded (FacetCycleFace n S) := by
  intro x y hcov
  have hlt : x < y := hcov.1
  have hdim_lt : OrientedGradedPoset.dim x < OrientedGradedPoset.dim y :=
    OrientedGradedPoset.dim_strictMono hlt
  have hdx : OrientedGradedPoset.dim x = 0 := by
    change DirectedCycleCell.cycleDim x.1 = 0
    have hdy : DirectedCycleCell.cycleDim y.1 ≤ 1 := by
      cases y.1 <;> simp [DirectedCycleCell.cycleDim]
    change DirectedCycleCell.cycleDim x.1 < DirectedCycleCell.cycleDim y.1 at hdim_lt
    omega
  have hdy : OrientedGradedPoset.dim y = 1 := by
    change DirectedCycleCell.cycleDim y.1 = 1
    have hle : DirectedCycleCell.cycleDim y.1 ≤ 1 := by
      cases y.1 <;> simp [DirectedCycleCell.cycleDim]
    change DirectedCycleCell.cycleDim x.1 < DirectedCycleCell.cycleDim y.1 at hdim_lt
    omega
  exact ⟨hlt.le, by rw [hdx, hdy]⟩

/-- Every face `FacetCycleFace n S` contains **at most two** `0`-cells (`dim = 0`): fixing any
omitted coordinate `k₀ ∉ S.1`, any vertex `v_i ∈ FacetCycleFace n S` must satisfy `i = k₀` or
`finSucc i = k₀`, yielding an injection into `Bool`. -/
theorem facetCycleFace_zeroCells_card_le_two {n : ℕ} (S : PuncturedCube n) :
    Fintype.card {x : FacetCycleFace n S // OrientedGradedPoset.dim x = 0} ≤ 2 := by
  classical
  rcases S.exists_not_mem with ⟨k₀, hk₀⟩
  let cls : {x : FacetCycleFace n S // OrientedGradedPoset.dim x = 0} → Bool :=
    fun x ↦ decide (x.1.1 = Sum.inl k₀)
  have hinj : Function.Injective cls := by
    intro x y hxy
    have hx_dim : DirectedCycleCell.cycleDim x.1.1 = 0 := x.2
    have hy_dim : DirectedCycleCell.cycleDim y.1.1 = 0 := y.2
    cases hx : x.1.1 with
    | inr e => simp [hx, DirectedCycleCell.cycleDim] at hx_dim
    | inl i =>
      cases hy : y.1.1 with
      | inr e => simp [hy, DirectedCycleCell.cycleDim] at hy_dim
      | inl j =>
        have hi_not : k₀ ∉ cycleCellSupport n (Sum.inl i) := fun h ↦ hk₀ (x.1.2 (hx ▸ h))
        have hj_not : k₀ ∉ cycleCellSupport n (Sum.inl j) := fun h ↦ hk₀ (y.1.2 (hy ▸ h))
        rw [mem_cycleCellSupport_inl, not_and_or, not_not, not_not] at hi_not hj_not
        have hij : i = j := by
          by_cases hik : i = k₀
          · have hcx : cls x = true := by simp [cls, hx, hik]
            rw [hxy] at hcx
            have hjk : j = k₀ := by
              have hd := of_decide_eq_true (by simpa [cls, hy] using hcx)
              exact Sum.inl.inj hd
            exact hik.trans hjk.symm
          · have hcx : cls x = false := by
              simp only [cls, hx]
              exact decide_eq_false (fun h ↦ hik (Sum.inl.inj h))
            rw [hxy] at hcx
            have hjk : j ≠ k₀ := by
              intro hEq
              simp [cls, hy, hEq] at hcx
            have hsi : finSucc i = k₀ := (hi_not.resolve_right (Ne.symm hik)).symm
            have hsj : finSucc j = k₀ := (hj_not.resolve_right (Ne.symm hjk)).symm
            exact finSucc_injective (hsi.trans hsj.symm)
        exact Subtype.ext (FacetCycleFace.ext (hx.trans (congrArg Sum.inl hij |>.trans hy.symm)))
  calc
    Fintype.card {x : FacetCycleFace n S // OrientedGradedPoset.dim x = 0}
        ≤ Fintype.card Bool := Fintype.card_le_of_injective cls hinj
    _ = 2 := by decide

/-- Every face `FacetCycleFace n S` contains **at most one** `1`-cell (`dim = 1`). -/
theorem facetCycleFace_edgeCells_card_le_one {n : ℕ} (S : PuncturedCube n) :
    Fintype.card {x : FacetCycleFace n S // OrientedGradedPoset.dim x = 1} ≤ 1 := by
  classical
  have hsub : Subsingleton {x : FacetCycleFace n S // OrientedGradedPoset.dim x = 1} := by
    constructor
    intro x y
    have hx_dim : DirectedCycleCell.cycleDim x.1.1 = 1 := x.2
    have hy_dim : DirectedCycleCell.cycleDim y.1.1 = 1 := y.2
    cases hx : x.1.1 with
    | inl _ => simp [hx, DirectedCycleCell.cycleDim] at hx_dim
    | inr e₁ =>
      cases hy : y.1.1 with
      | inl _ => simp [hy, DirectedCycleCell.cycleDim] at hy_dim
      | inr e₂ =>
        have he : e₁ = e₂ := edge_unique (hx ▸ x.1.2) (hy ▸ y.1.2)
        exact Subtype.ext (FacetCycleFace.ext (hx.trans (congrArg Sum.inr he |>.trans hy.symm)))
  exact Fintype.card_le_one_iff_subsingleton.mpr hsub

/-- When `3 ≤ n` and `S` contains no `1`-cell support `M_e`, `FacetCycleFace n S` has size
**at most one** (`0` or `1` vertices). -/
theorem facetCycleFace_noEdge_card_le_one {n : ℕ} (hn : 3 ≤ n) {S : PuncturedCube n}
    (hNoEdge : ∀ e : Fin n, ¬ cycleCellSupport n (Sum.inr e) ⊆ S.1) :
    Fintype.card (FacetCycleFace n S) ≤ 1 := by
  classical
  rcases S.exists_not_mem with ⟨k₀, hk₀⟩
  have hk₁ : ∃ k₁ : Fin n, k₁ ∉ S.1 ∧ k₁ ≠ k₀ := by
    by_contra hnone
    push_neg at hnone
    let e : Fin n := ⟨(k₀.1 + (n - 1)) % n, Nat.mod_lt _ k₀.pos⟩
    have hse : finSucc e = k₀ := by
      apply Fin.ext
      change ((k₀.1 + (n - 1)) % n + 1) % n = k₀.1
      rw [Nat.mod_add_mod]
      have hklt := k₀.2
      have hsum : k₀.1 + (n - 1) + 1 = k₀.1 + n := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hklt]
    refine hNoEdge e (fun k hk ↦ ?_)
    rw [mem_cycleCellSupport_inr, hse] at hk
    by_contra hkS
    exact hk (hnone k hkS)
  rcases hk₁ with ⟨k₁, hk₁, hne⟩
  have hmiss : ∀ {i k : Fin n}, cycleCellSupport n (Sum.inl i) ⊆ S.1 → k ∉ S.1 →
      k = finSucc i ∨ k = i := by
    intro i k hiS hkS
    by_contra hc
    push_neg at hc
    exact hkS (hiS (mem_cycleCellSupport_inl.mpr hc))
  have hsub : Subsingleton (FacetCycleFace n S) := by
    constructor
    intro x y
    cases hx : x.1 with
    | inr e => exact False.elim (hNoEdge e (hx ▸ x.2))
    | inl i =>
      cases hy : y.1 with
      | inr e => exact False.elim (hNoEdge e (hy ▸ y.2))
      | inl j =>
        have hi₀ : k₀ = finSucc i ∨ k₀ = i := hmiss (hx ▸ x.2) hk₀
        have hi₁ : k₁ = finSucc i ∨ k₁ = i := hmiss (hx ▸ x.2) hk₁
        have hj₀ : k₀ = finSucc j ∨ k₀ = j := hmiss (hy ▸ y.2) hk₀
        have hj₁ : k₁ = finSucc j ∨ k₁ = j := hmiss (hy ▸ y.2) hk₁
        have hij : i = j := by
          rcases hi₀ with hi₀ | hi₀ <;> rcases hi₁ with hi₁ | hi₁
          · exact False.elim (hne (hi₁.trans hi₀.symm))
          · rcases hj₀ with hj₀ | hj₀ <;> rcases hj₁ with hj₁ | hj₁
            · exact False.elim (hne (hj₁.trans hj₀.symm))
            · exact finSucc_injective (hi₀.symm.trans hj₀)
            · have h2 : finSucc (finSucc i) = i := by
                have hA : finSucc i = j := hi₀.symm.trans hj₀
                have hB : finSucc j = i := hj₁.symm.trans hi₁
                simpa [hA] using hB
              exact False.elim (finSucc_finSucc_ne_self hn i h2)
            · exact False.elim (hne (hj₁.trans hj₀.symm))
          · rcases hj₀ with hj₀ | hj₀ <;> rcases hj₁ with hj₁ | hj₁
            · exact False.elim (hne (hj₁.trans hj₀.symm))
            · have h2 : finSucc (finSucc i) = i := by
                have hA : finSucc j = i := hj₀.symm.trans hi₀
                have hB : finSucc i = j := hi₁.symm.trans hj₁
                simpa [hB] using hA
              exact False.elim (finSucc_finSucc_ne_self hn i h2)
            · exact hi₀.symm.trans hj₀
            · exact False.elim (hne (hj₁.trans hj₀.symm))
          · exact False.elim (hne (hi₁.trans hi₀.symm))
        exact FacetCycleFace.ext (hx.trans (congrArg Sum.inl hij |>.trans hy.symm))
  exact Fintype.card_le_one_iff_subsingleton.mpr hsub

private theorem facetCycleFace_mem_cases_of_edge {n : ℕ} {S : PuncturedCube n} {e : Fin n}
    (heS : cycleCellSupport n (Sum.inr e) ⊆ S.1) (x : FacetCycleFace n S) :
    x.1 = Sum.inl e ∨ x.1 = Sum.inl (finSucc e) ∨ x.1 = Sum.inr e := by
  have hS_sub : S.1 ⊆ Finset.univ.erase (finSucc e) := by
    intro k hk
    exact Finset.mem_erase.mpr ⟨fun hEq ↦ by
      subst hEq
      exact S.2 (Finset.eq_univ_iff_forall.mpr fun m ↦ by
        by_cases hm : m = finSucc e
        · exact hm ▸ hk
        · exact heS (mem_cycleCellSupport_inr.mpr hm)), Finset.mem_univ k⟩
  cases hx : x.1 with
  | inl i =>
    have hmiss : finSucc e ∉ cycleCellSupport n (Sum.inl i) :=
      fun h ↦ (Finset.mem_erase.mp (hS_sub (x.2 (hx ▸ h)))).1 rfl
    rw [mem_cycleCellSupport_inl, not_and_or, not_not, not_not] at hmiss
    rcases hmiss with hEq | hEq
    · exact Or.inl (congrArg Sum.inl (finSucc_injective hEq).symm)
    · exact Or.inr (Or.inl (congrArg Sum.inl hEq.symm))
  | inr e' =>
    exact Or.inr (Or.inr (congrArg Sum.inr (edge_unique (hx ▸ x.2) heS)))

/-- **Explicit `FacetCycleFace` Size & Cell Classification Theorem (`3 ≤ n`):**
every proper face `FacetCycleFace n S` has at most `2` vertices (`0`-cells), at most `1` directed
edge (`1`-cell), cardinality in `{0, 1, 3}`, and whenever it is not of cardinality `≤ 1` (`Empty`
or a `0`-cell point) it is isomorphic as an `OrientedGradedPoset` (`Hom` in both directions) to
`WalkingArrow = (0 → 1)`. -/
theorem facetCycleFace_classification {n : ℕ} (hn : 3 ≤ n) (S : PuncturedCube n) :
    Fintype.card {x : FacetCycleFace n S // OrientedGradedPoset.dim x = 0} ≤ 2 ∧
      Fintype.card {x : FacetCycleFace n S // OrientedGradedPoset.dim x = 1} ≤ 1 ∧
      ((IsEmpty (FacetCycleFace n S)) ∨
        (Fintype.card (FacetCycleFace n S) = 1 ∧
          ∀ x : FacetCycleFace n S, OrientedGradedPoset.dim x = 0) ∨
        (Fintype.card (FacetCycleFace n S) = 3 ∧
          ∃ (f : OrientedGradedPoset.Hom (FacetCycleFace n S) WalkingArrow)
            (g : OrientedGradedPoset.Hom WalkingArrow (FacetCycleFace n S)),
            (∀ x, g (f x) = x) ∧ (∀ w, f (g w) = w))) := by
  classical
  refine ⟨facetCycleFace_zeroCells_card_le_two S, facetCycleFace_edgeCells_card_le_one S, ?_⟩
  by_cases hEdge : ∃ e : Fin n, cycleCellSupport n (Sum.inr e) ⊆ S.1
  · rcases hEdge with ⟨e, heS⟩
    have hn2 : 2 ≤ n := by omega
    have hSne : finSucc e ≠ e := finSucc_ne_self hn2 e
    let v0 : FacetCycleFace n S :=
      ⟨Sum.inl e, Finset.Subset.trans (cycleCellSupport_inl_subset_inr e) heS⟩
    let v1 : FacetCycleFace n S :=
      ⟨Sum.inl (finSucc e), Finset.Subset.trans (cycleCellSupport_inl_finSucc_subset_inr e) heS⟩
    let ed : FacetCycleFace n S := ⟨Sum.inr e, heS⟩
    let toW : FacetCycleFace n S → WalkingArrow := fun x ↦
      match x.1 with
      | Sum.inl i => if i = e then .v0 else .v1
      | Sum.inr _ => .edge
    let ofW : WalkingArrow → FacetCycleFace n S
      | .v0 => v0
      | .v1 => v1
      | .edge => ed
    have ht0 : ∀ {x : FacetCycleFace n S}, x.1 = Sum.inl e → toW x = .v0 := fun {x} hx ↦ by
      dsimp [toW]; rw [hx]; exact if_pos rfl
    have ht1 : ∀ {x : FacetCycleFace n S}, x.1 = Sum.inl (finSucc e) → toW x = .v1 :=
      fun {x} hx ↦ by dsimp [toW]; rw [hx]; exact if_neg hSne
    have htE : ∀ {x : FacetCycleFace n S}, x.1 = Sum.inr e → toW x = .edge :=
      fun {x} hx ↦ by dsimp [toW]; rw [hx]
    have hfg : ∀ w : WalkingArrow, toW (ofW w) = w := by
      intro w
      cases w with
      | v0 => exact ht0 (x := v0) rfl
      | v1 => exact ht1 (x := v1) rfl
      | edge => exact htE (x := ed) rfl
    have hgf : ∀ x : FacetCycleFace n S, ofW (toW x) = x := by
      intro x
      rcases facetCycleFace_mem_cases_of_edge heS x with h0 | h1 | h2
      · rw [ht0 h0]; exact FacetCycleFace.ext h0.symm
      · rw [ht1 h1]; exact FacetCycleFace.ext h1.symm
      · rw [htE h2]; exact FacetCycleFace.ext h2.symm
    have hdim_ofW : ∀ w : WalkingArrow,
        OrientedGradedPoset.dim (ofW w) = OrientedGradedPoset.dim w := by
      intro w; cases w <;> rfl
    have hdim_toW : ∀ x : FacetCycleFace n S,
        OrientedGradedPoset.dim (toW x) = OrientedGradedPoset.dim x := by
      intro x
      rcases facetCycleFace_mem_cases_of_edge heS x with h0 | h1 | h2
      · rw [ht0 h0]; change 0 = DirectedCycleCell.cycleDim x.1; rw [h0]; rfl
      · rw [ht1 h1]; change 0 = DirectedCycleCell.cycleDim x.1; rw [h1]; rfl
      · rw [htE h2]; change 1 = DirectedCycleCell.cycleDim x.1; rw [h2]; rfl
    have hmono_ofW : Monotone ofW := by
      intro w₁ w₂ hw
      cases w₁ <;> cases w₂
      · exact le_refl _
      · exact False.elim (by revert hw; decide)
      · change e = e ∨ e = finSucc e; exact Or.inl rfl
      · exact False.elim (by revert hw; decide)
      · exact le_refl _
      · change finSucc e = e ∨ finSucc e = finSucc e; exact Or.inr rfl
      · exact False.elim (by revert hw; decide)
      · exact False.elim (by revert hw; decide)
      · exact le_refl _
    have hmono_toW : Monotone toW := by
      intro x y hxy
      have hxy' : x.1 ≤ y.1 := hxy
      rcases facetCycleFace_mem_cases_of_edge heS x with hx | hx | hx <;>
        rcases facetCycleFace_mem_cases_of_edge heS y with hy | hy | hy
      · rw [ht0 hx, ht0 hy]
      · exfalso; rw [hx, hy] at hxy'; change e = finSucc e at hxy'; exact hSne hxy'.symm
      · rw [ht0 hx, htE hy]; decide
      · exfalso; rw [hx, hy] at hxy'; change finSucc e = e at hxy'; exact hSne hxy'
      · rw [ht1 hx, ht1 hy]
      · rw [ht1 hx, htE hy]; decide
      · exfalso; rw [hx, hy] at hxy'; exact hxy'
      · exfalso; rw [hx, hy] at hxy'; exact hxy'
      · rw [htE hx, htE hy]
    have hsign_ofW : ∀ ⦃a b : WalkingArrow⦄,
        IsFacet a b → OrientedGradedPoset.sign (ofW a) (ofW b) = OrientedGradedPoset.sign a b := by
      intro a b hab
      cases a <;> cases b
      all_goals
        first
        | (cases hab with
          | intro _ hd =>
            change walkingArrowDim _ = walkingArrowDim _ + 1 at hd
            simp [walkingArrowDim] at hd)
        | (change DirectedCycleCell.cycleSign (Sum.inl e) (Sum.inr e) = false
           simp [DirectedCycleCell.cycleSign, hSne.symm])
        | (change DirectedCycleCell.cycleSign (Sum.inl (finSucc e)) (Sum.inr e) = true
           simp [DirectedCycleCell.cycleSign])
    have hsign_toW : ∀ ⦃x y : FacetCycleFace n S⦄,
        IsFacet x y → OrientedGradedPoset.sign (toW x) (toW y) = OrientedGradedPoset.sign x y := by
      intro x y hxy
      rcases hxy with ⟨hle, hd⟩
      rcases facetCycleFace_mem_cases_of_edge heS x with hx | hx | hx <;>
        rcases facetCycleFace_mem_cases_of_edge heS y with hy | hy | hy
      all_goals
        change DirectedCycleCell.cycleDim y.1 = DirectedCycleCell.cycleDim x.1 + 1 at hd
        simp only [hx, hy, DirectedCycleCell.cycleDim] at hd
        try (exfalso; omega)
      · rw [ht0 hx, htE hy]
        change walkingArrowSign .v0 .edge = DirectedCycleCell.cycleSign x.1 y.1
        rw [hx, hy]
        simp [walkingArrowSign, DirectedCycleCell.cycleSign, hSne.symm]
      · rw [ht1 hx, htE hy]
        change walkingArrowSign .v1 .edge = DirectedCycleCell.cycleSign x.1 y.1
        rw [hx, hy]
        simp [walkingArrowSign, DirectedCycleCell.cycleSign]
    let fHom : OrientedGradedPoset.Hom (FacetCycleFace n S) WalkingArrow :=
      ⟨toW, hmono_toW, hdim_toW, fun _ _ h ↦ hsign_toW h⟩
    let gHom : OrientedGradedPoset.Hom WalkingArrow (FacetCycleFace n S) :=
      ⟨ofW, hmono_ofW, hdim_ofW, fun _ _ h ↦ hsign_ofW h⟩
    have heq : Equiv (FacetCycleFace n S) WalkingArrow := ⟨toW, ofW, hgf, hfg⟩
    let wEquivFin3 : Equiv WalkingArrow (Fin 3) :=
      { toFun := fun | .v0 => 0 | .v1 => 1 | .edge => 2
        invFun := fun
          | ⟨0, _⟩ => .v0
          | ⟨1, _⟩ => .v1
          | ⟨_ + 2, _⟩ => .edge
        left_inv := fun | .v0 => rfl | .v1 => rfl | .edge => rfl
        right_inv := fun i ↦ by
          rcases i with ⟨_ | _ | _ | k, hk⟩
          · rfl
          · rfl
          · rfl
          · omega }
    have hcard : Fintype.card (FacetCycleFace n S) = 3 := by
      rw [Fintype.card_congr (heq.trans wEquivFin3), Fintype.card_fin]
    exact Or.inr (Or.inr ⟨hcard, fHom, gHom, hgf, hfg⟩)
  · push_neg at hEdge
    have hle1 := facetCycleFace_noEdge_card_le_one hn hEdge
    by_cases hEmpty : IsEmpty (FacetCycleFace n S)
    · exact Or.inl hEmpty
    · rw [not_isEmpty_iff] at hEmpty
      have hpos : 0 < Fintype.card (FacetCycleFace n S) := Fintype.card_pos
      have hcard1 : Fintype.card (FacetCycleFace n S) = 1 := by omega
      refine Or.inr (Or.inl ⟨hcard1, fun x ↦ ?_⟩)
      cases hx : x.1 with
      | inl _ => simp [OrientedGradedPoset.dim, hx, DirectedCycleCell.cycleDim]
      | inr e => exact False.elim (hEdge e (hx ▸ x.2))

end FacetCycleFace

/-- The **facet-supported directed `n`-cycle cubical diagram** `F_n` (`3 ≤ n`) over
`PuncturedCube n`, assigning each proper face `S ⊊ [n]` the subcomplex `FacetCycleFace n S`. -/
def facetCycleDiagram (n : ℕ) (_hn : 3 ≤ n) : CubicalPosetDiagram n where
  obj := FacetCycleFace n
  map h := FacetCycleFace.map h
  map_closed h := FacetCycleFace.isClosedEmbedding_map h
  map_id _ _ := rfl
  map_comp _ _ _ := rfl

instance instFintypeFacetCycleDiagramObj (n : ℕ) (hn : 3 ≤ n) (S : PuncturedCube n) :
    Fintype ((facetCycleDiagram n hn).obj S) :=
  inferInstanceAs (Fintype (FacetCycleFace n S))

/-- `facetCycleDiagram n hn` satisfies exact face-intersection pullbacks (`IsIntersective`). -/
theorem facetCycleDiagram_isIntersective (n : ℕ) (hn : 3 ≤ n) :
    (facetCycleDiagram n hn).IsIntersective := by
  intro S T U _ _ x y heq
  have hx_eq : x.1 = y.1 := congrArg FacetCycleFace.val heq
  have hsub : cycleCellSupport n x.1 ⊆ (S ⊓ T).1 :=
    Finset.subset_inter x.2 (hx_eq ▸ y.2)
  exact ⟨⟨x.1, hsub⟩, Subtype.ext rfl, Subtype.ext hx_eq⟩

/-- Every proper face of `facetCycleDiagram n hn` (`3 ≤ n`) is `IsFlowAcyclic`. -/
theorem facetCycleFace_isFlowAcyclic (n : ℕ) (hn : 3 ≤ n) (S : PuncturedCube n) :
    IsFlowAcyclic ((facetCycleDiagram n hn).obj S) := by
  have hn2 : 2 ≤ n := by omega
  intro x hxx
  have hstep : FlowStep x x := (FacetCycleFace.flowReach_iff_flowStep hn2).mp hxx
  exact FacetCycleFace.not_step_step hn2 hstep hstep

/-- Every transition map of `facetCycleDiagram n hn` (`3 ≤ n`) is **flow-convex** (`IsFlowConvex`,
and therefore also `IsFlowReachReflecting` and `IsClosedEmbedding`). -/
theorem facetCycleMap_isFlowConvex (n : ℕ) (hn : 3 ≤ n) {S T : PuncturedCube n} (hST : S ≤ T) :
    IsFlowConvex ((facetCycleDiagram n hn).map hST) := by
  have hn2 : 2 ≤ n := by omega
  refine IsFlowConvex.ofClosedEmbedding ((facetCycleDiagram n hn).map_closed hST) ?_ ?_
  · intro x y w hxw hsx hyw hsy
    have hstep : FlowStep ((facetCycleDiagram n hn).map hST x)
        ((facetCycleDiagram n hn).map hST y) := ⟨w, hxw, hsx, hyw, hsy⟩
    rcases FacetCycleFace.flowStep_dest hn2 hstep with ⟨e, _, hx, hy⟩
    have hx' : x.1 = Sum.inl e := hx
    have hy' : y.1 = Sum.inl (finSucc e) := hy
    have hvalT := FacetCycleFace.isClosedEmbedding_val T
    rcases DirectedCycleCell.isFacet_iff.mp (hvalT.map_isFacet_iff.mpr hxw) with ⟨e', hw, hxe'⟩
    have hw' : w.1 = Sum.inr e' := hw
    have he_eq : e' = e := by
      rcases hxe' with h₁ | h₂
      · exact Sum.inl.inj (h₁.symm.trans hx')
      · exfalso
        have hv : e = finSucc e' := Sum.inl.inj (hx'.symm.trans h₂)
        have hsx' : DirectedCycleCell.cycleSign x.1 w.1 = false := hsx
        rw [hx', hv, hw'] at hsx'
        change decide (finSucc e' = finSucc e') = false at hsx'
        simp at hsx'
    subst e'
    have hxS : cycleCellSupport n (Sum.inl e) ⊆ S.1 := hx' ▸ x.2
    have hyS : cycleCellSupport n (Sum.inl (finSucc e)) ⊆ S.1 := hy' ▸ y.2
    have hwS : cycleCellSupport n w.1 ⊆ S.1 := by
      rw [hw', ← cycleCellSupport_union hn e]
      exact Finset.union_subset hxS hyS
    exact ⟨⟨w.1, hwS⟩, Subtype.ext rfl⟩
  · intro x y u hxu huy
    have hs₁ : FlowStep ((facetCycleDiagram n hn).map hST x) u :=
      (FacetCycleFace.flowReach_iff_flowStep hn2).mp hxu
    have hs₂ : FlowStep u ((facetCycleDiagram n hn).map hST y) :=
      (FacetCycleFace.flowReach_iff_flowStep hn2).mp huy
    exact False.elim (FacetCycleFace.not_step_step hn2 hs₁ hs₂)

/-- Helper: any cyclic `Fin n`-indexed family of `FlowStep`s (`1 ≤ n`) creates a `FlowReach`
self-loop at index `0`. -/
private theorem flowReach_self_of_finSucc_steps {Q : Type*} [OrientedGradedPoset Q]
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → Q) (hstep : ∀ i : Fin n, FlowStep (q i) (q (finSucc i))) :
    FlowReach (q ⟨0, hn⟩) (q ⟨0, hn⟩) := by
  let wrap : ℕ → Fin n := fun m ↦ ⟨m % n, Nat.mod_lt m hn⟩
  have hwrap_succ : ∀ m : ℕ, finSucc (wrap m) = wrap (m + 1) := fun m ↦ by
    apply Fin.ext
    exact Nat.mod_add_mod m n 1
  have hreach : ∀ k : ℕ, 1 ≤ k → FlowReach (q (wrap 0)) (q (wrap k)) := by
    intro k hk
    induction k with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 0
      · subst hm
        have hs := hstep (wrap 0)
        rw [hwrap_succ 0] at hs
        exact .single hs
      · have hm1 : 1 ≤ m := by omega
        have hs := hstep (wrap m)
        rw [hwrap_succ m] at hs
        exact (ih hm1).tail hs
  have hloop := hreach n hn
  have hw0 : wrap 0 = ⟨0, hn⟩ := Fin.ext (Nat.zero_mod n)
  have hwn : wrap n = ⟨0, hn⟩ := Fin.ext (Nat.mod_self n)
  rwa [hw0, hwn] at hloop

/-- **Theorem 10B Part 2 — All-`n ≥ 3` Flow-Acyclicity Obstruction
(`no_flowAcyclic_cubical_amalgam_of_three_le`):**
For every `n ≥ 3`, although `facetCycleDiagram n hn` is intersective, has `IsFlowAcyclic` proper
faces, and has `IsFlowConvex` transition maps, **no** `IsFlowAcyclic` `OrientedGradedPoset Q`
admits a `CubicalCocone (facetCycleDiagram n hn) Q`. -/
theorem no_flowAcyclic_cubical_amalgam_of_three_le (n : ℕ) (hn : 3 ≤ n)
    {Q : Type v} [OrientedGradedPoset Q] (hAcyc : IsFlowAcyclic Q) :
    IsEmpty (CubicalCocone (facetCycleDiagram n hn) Q) := by
  refine ⟨fun C ↦ ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  let A_face : Fin n → PuncturedCube n := fun i ↦
    ⟨cycleCellSupport n (Sum.inl i), cycleCellSupport_ne_univ (Sum.inl i)⟩
  let M_face : Fin n → PuncturedCube n := fun i ↦
    ⟨cycleCellSupport n (Sum.inr i), cycleCellSupport_ne_univ (Sum.inr i)⟩
  let v_cell : ∀ i : Fin n, (facetCycleDiagram n hn).obj (A_face i) := fun i ↦
    ⟨Sum.inl i, Finset.Subset.refl _⟩
  let q : Fin n → Q := fun i ↦ C.leg (A_face i) (v_cell i)
  have hstep : ∀ i : Fin n, FlowStep (q i) (q (finSucc i)) := by
    intro i
    have hAM₀ : A_face i ≤ M_face i := cycleCellSupport_inl_subset_inr i
    have hAM₁ : A_face (finSucc i) ≤ M_face i := cycleCellSupport_inl_finSucc_subset_inr i
    let u₀ : (facetCycleDiagram n hn).obj (M_face i) :=
      (facetCycleDiagram n hn).map hAM₀ (v_cell i)
    let u₁ : (facetCycleDiagram n hn).obj (M_face i) :=
      (facetCycleDiagram n hn).map hAM₁ (v_cell (finSucc i))
    let e_cell : (facetCycleDiagram n hn).obj (M_face i) :=
      ⟨Sum.inr i, Finset.Subset.refl _⟩
    have hf₀ : IsFacet u₀ e_cell := ⟨Or.inl rfl, rfl⟩
    have hf₁ : IsFacet u₁ e_cell := ⟨Or.inr rfl, rfl⟩
    have hs₀ : OrientedGradedPoset.sign u₀ e_cell = false := by
      change decide (i = finSucc i) = false
      exact decide_eq_false (fun h ↦ finSucc_ne_self hn2 i h.symm)
    have hs₁ : OrientedGradedPoset.sign u₁ e_cell = true := by
      change decide (finSucc i = finSucc i) = true
      exact decide_eq_true rfl
    have hM_step : FlowStep u₀ u₁ := ⟨e_cell, hf₀, hs₀, hf₁, hs₁⟩
    have hQ_step : FlowStep (C.leg (M_face i) u₀) (C.leg (M_face i) u₁) :=
      (C.leg_closed (M_face i)).map_flowStep hM_step
    rwa [C.comm hAM₀ (v_cell i), C.comm hAM₁ (v_cell (finSucc i))] at hQ_step
  exact hAcyc (q ⟨0, hn1⟩) (flowReach_self_of_finSucc_steps hn1 q hstep)

/-- In particular, for every `n ≥ 3`, the canonical minimal-support amalgamation
`CubicalAmalgam (facetCycleDiagram n hn)` violates `IsFlowAcyclic`. -/
theorem not_isFlowAcyclic_cubicalAmalgam_facetCycle (n : ℕ) (hn : 3 ≤ n) :
    ¬ IsFlowAcyclic (CubicalAmalgam (facetCycleDiagram n hn)) := by
  intro hAcyc
  exact (no_flowAcyclic_cubical_amalgam_of_three_le n hn hAcyc).false
    (cubicalAmalgamCocone (facetCycleDiagram_isIntersective n hn))

/-- **Headline Theorem 10B — Cubical Amalgamation Dichotomy
(`theorem10B_cubical_amalgamation_dichotomy`):**
1. **(All-`n` `n-DAP` for Closed Oriented Graded Posets):** Every intersective punctured `n`-cube
   diagram `D : CubicalPosetDiagram n` admits `HasCubicalNDAP D` (via `CubicalAmalgam D`).
2. **(All-`n ≥ 3` Failure on Flow-Acyclic Convex Complexes):** For every `n ≥ 3`,
   `facetCycleDiagram n hn` is intersective, has `IsFlowAcyclic` finite faces, and has
   `IsFlowConvex` transition maps, yet admits **no** `CubicalCocone` into any `IsFlowAcyclic`
   `OrientedGradedPoset`. -/
theorem theorem10B_cubical_amalgamation_dichotomy :
    (∀ (n : ℕ) (D : CubicalPosetDiagram.{0} n), D.IsIntersective → HasCubicalNDAP D) ∧
      (∀ (n : ℕ) (hn : 3 ≤ n),
        (facetCycleDiagram n hn).IsIntersective ∧
          (∀ S : PuncturedCube n, IsFlowAcyclic ((facetCycleDiagram n hn).obj S)) ∧
          (∀ {S T : PuncturedCube n} (h : S ≤ T),
            IsFlowConvex ((facetCycleDiagram n hn).map h)) ∧
          (∀ (Q : Type) [OrientedGradedPoset Q], IsFlowAcyclic Q →
            IsEmpty (CubicalCocone (facetCycleDiagram n hn) Q))) :=
  ⟨fun _ _ hInt ↦ (cubical_ndap_closed_oriented_poset hInt).2.2.2.2.2,
    fun n hn ↦ ⟨facetCycleDiagram_isIntersective n hn,
      facetCycleFace_isFlowAcyclic n hn,
      fun h ↦ facetCycleMap_isFlowConvex n hn h,
      fun _ _ hAcyc ↦ no_flowAcyclic_cubical_amalgam_of_three_le n hn hAcyc⟩⟩

/-! ## Section 5: Mandatory 4-Layer Lean 4 Definition Check Gate (`namespace Checks`) -/

namespace Checks

/-! ### Layer 1: Inhabitation (Non-Degeneracy of Formalized Carriers) -/

/-- Layer 1 witness: `PuncturedCube 3` is `Nontrivial`. -/
instance instNontrivialPuncturedCubeThree : Nontrivial (PuncturedCube 3) :=
  PuncturedCube.nontrivial_of_two_le (by decide)

/-- Explicit existential non-degeneracy witness on `PuncturedCube 3`. -/
theorem puncturedCubeThree_exists_ne : ∃ S T : PuncturedCube 3, S ≠ T :=
  exists_pair_ne (PuncturedCube 3)

/-- Layer 1 witness: `DirectedCycleCell 3` is `Nontrivial` (`Sum.inl 0 ≠ Sum.inr 0`). -/
instance instNontrivialDirectedCycleCellThree : Nontrivial (DirectedCycleCell 3) :=
  ⟨⟨Sum.inl 0, Sum.inr 0, by decide⟩⟩

/-- Codimension-1 facet `M_0 = univ \ {1} = {0, 2}` of `PuncturedCube 3`. -/
def facetM0Three : PuncturedCube 3 :=
  ⟨cycleCellSupport 3 (Sum.inr 0), cycleCellSupport_ne_univ (Sum.inr 0)⟩

/-- Layer 1 witness: the proper face `(facetCycleDiagram 3 _).obj facetM0Three` is `Nontrivial`
(containing both `v_0 = Sum.inl 0` and `e_0 = Sum.inr 0`). -/
instance instNontrivialFacetCycleFaceThree :
    Nontrivial ((facetCycleDiagram 3 (by decide)).obj facetM0Three) :=
  ⟨⟨⟨Sum.inl 0, cycleCellSupport_inl_subset_inr 0⟩,
    ⟨Sum.inr 0, Finset.Subset.refl _⟩,
    fun h ↦ by cases congrArg FacetCycleFace.val h⟩⟩

/-- Support face `A_i` of `0`-cell `Sum.inl i` inside `PuncturedCube n`. -/
def vertexSupportFace {n : ℕ} (i : Fin n) : PuncturedCube n :=
  ⟨cycleCellSupport n (Sum.inl i), cycleCellSupport_ne_univ (Sum.inl i)⟩

/-- Minimal-support proof for `Sum.inl i` on its support face `vertexSupportFace i`. -/
theorem isMinimalCell_vertex {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    (facetCycleDiagram n hn).IsMinimalCell (vertexSupportFace i)
      ⟨Sum.inl i, Finset.Subset.refl _⟩ := by
  intro B _ ⟨b, hb⟩
  have hb_eq : b.1 = Sum.inl i := congrArg FacetCycleFace.val hb
  change cycleCellSupport n (Sum.inl i) ⊆ B.1
  rw [← hb_eq]
  exact b.2

/-- Layer 1 witness: `CubicalAmalgam (facetCycleDiagram 3 (by decide))` is `Nontrivial`. -/
instance instNontrivialCubicalAmalgamThree :
    Nontrivial (CubicalAmalgam (facetCycleDiagram 3 (by decide))) := by
  refine ⟨⟨⟨⟨vertexSupportFace 0, ⟨Sum.inl 0, Finset.Subset.refl _⟩⟩,
      isMinimalCell_vertex (by decide) 0⟩,
    ⟨⟨vertexSupportFace 1, ⟨Sum.inl 1, Finset.Subset.refl _⟩⟩,
      isMinimalCell_vertex (by decide) 1⟩,
    fun h ↦ ?_⟩⟩
  have hv : cycleCellSupport 3 (Sum.inl 0) = cycleCellSupport 3 (Sum.inl 1) :=
    congrArg (fun p : CubicalAmalgam (facetCycleDiagram 3 (by decide)) ↦ p.1.1.1) h
  exact absurd hv (by decide)

/-- Explicit existential non-degeneracy witness on `CubicalAmalgam (facetCycleDiagram 3 _)`. -/
theorem cubicalAmalgamThree_exists_ne :
    ∃ p q : CubicalAmalgam (facetCycleDiagram 3 (by decide)), p ≠ q :=
  exists_pair_ne _

/-! ### Layer 2: Bidirectional Separation of Core Predicates -/

/-- One-point `0`-dimensional `OrientedGradedPoset` carrier `PointPoset` (fresh inductive avoiding
preexisting `PartialOrder Unit` diamonds). -/
inductive PointPoset : Type
  | pt
  deriving DecidableEq, Repr

instance instOrientedGradedPosetPointPoset : OrientedGradedPoset PointPoset where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  le_antisymm a b _ _ := by
    cases a
    cases b
    rfl
  dim _ := 0
  dim_strictMono _ _ h := False.elim (h.2 trivial)
  sign _ _ := false

/-- Subtype `{_u : PointPoset // S.1 ≠ ∅}`: empty over `S = ∅` and a single `0`-cell over every
non-empty proper face `S ≠ ∅`. -/
def NonEmptyFaceCell (n : ℕ) (S : PuncturedCube n) : Type :=
  {_u : PointPoset // S.1 ≠ ∅}

instance instOrientedGradedPosetNonEmptyFaceCell (n : ℕ) (S : PuncturedCube n) :
    OrientedGradedPoset (NonEmptyFaceCell n S) where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  le_antisymm a b _ _ := by
    rcases a with ⟨⟨⟩, _⟩
    rcases b with ⟨⟨⟩, _⟩
    rfl
  dim _ := 0
  dim_strictMono _ _ h := False.elim (h.2 trivial)
  sign _ _ := false

/-- Transition map on `NonEmptyFaceCell n` along `S ≤ T`. -/
def nonEmptyFaceCellMap {n : ℕ} {S T : PuncturedCube n} (hST : S ≤ T)
    (x : NonEmptyFaceCell n S) : NonEmptyFaceCell n T :=
  ⟨.pt, fun hT ↦ x.2 (Finset.subset_empty.mp (hT ▸ hST))⟩

/-- Punctured `n`-cube diagram sending `∅` to the empty poset and every non-empty proper face to a
single `0`-cell: intersective at `n = 2` (`{0} ∪ {1} = univ`), yet **non-intersective** for `n ≥ 3`
(`{0}` and `{1}` meet inside `{0, 1} ⊊ [n]` while `{0} ∩ {1} = ∅` is empty). -/
def puncturedEmptyApexDiagram (n : ℕ) : CubicalPosetDiagram n where
  obj := NonEmptyFaceCell n
  map h := nonEmptyFaceCellMap h
  map_closed hST :=
    { mono := fun _ _ _ ↦ trivial
      injective := fun a b _ ↦ by
        rcases a with ⟨⟨⟩, _⟩
        rcases b with ⟨⟨⟩, _⟩
        rfl
      downward_closed := fun x q _ ↦ by
        rcases x with ⟨⟨⟩, hx⟩
        rcases q with ⟨⟨⟩, _⟩
        exact ⟨⟨.pt, hx⟩, trivial, rfl⟩
      map_dim := fun _ ↦ rfl
      map_sign := fun _ _ hfac ↦ by
        rcases hfac with ⟨_, hd⟩
        simp [OrientedGradedPoset.dim] at hd }
  map_id _ x := by
    rcases x with ⟨⟨⟩, _⟩
    rfl
  map_comp _ _ _ := rfl

/-- Layer 2 positive witness for `IsIntersective` and `HasCubicalNDAP` at `n = 3`. -/
theorem layer2_pos_isIntersective_and_ndap :
    (facetCycleDiagram 3 (by decide)).IsIntersective ∧
      HasCubicalNDAP (facetCycleDiagram 3 (by decide)) :=
  ⟨facetCycleDiagram_isIntersective 3 (by decide),
    (cubical_ndap_closed_oriented_poset (facetCycleDiagram_isIntersective 3 (by decide))).2.2.2.2.2⟩

/-- Layer 2 negative counter-witness for `IsIntersective` AND `HasCubicalNDAP` at `n = 3`:
in `puncturedEmptyApexDiagram 3`, faces `{0}` and `{1}` map to the same point inside `{0, 1} ⊊ [3]`
while `{0} ∩ {1} = ∅` has empty fiber. -/
theorem layer2_neg_isIntersective_and_ndap :
    ¬ (puncturedEmptyApexDiagram 3).IsIntersective ∧
      ¬ HasCubicalNDAP (puncturedEmptyApexDiagram 3) := by
  have hnotInt : ¬ (puncturedEmptyApexDiagram 3).IsIntersective := by
    intro hInt
    let S : PuncturedCube 3 := PuncturedCube.singletonFace (by decide) 0
    let T : PuncturedCube 3 := PuncturedCube.singletonFace (by decide) 1
    let U : PuncturedCube 3 := ⟨{0, 1}, by decide⟩
    have hSU : S ≤ U := by decide
    have hTU : T ≤ U := by decide
    let x : (puncturedEmptyApexDiagram 3).obj S := ⟨.pt, by decide⟩
    let y : (puncturedEmptyApexDiagram 3).obj T := ⟨.pt, by decide⟩
    rcases hInt hSU hTU x y rfl with ⟨z, _⟩
    exact z.2 (by decide)
  exact ⟨hnotInt, fun hndap ↦ hnotInt hndap.isIntersective⟩

/-- Layer 2 positive witness for `IsMinimalCell`: `v_0` on its minimal support `A_0 = {2}` in
`facetCycleDiagram 3`. -/
theorem layer2_pos_isMinimalCell :
    (facetCycleDiagram 3 (by decide)).IsMinimalCell (vertexSupportFace 0)
      ⟨Sum.inl 0, Finset.Subset.refl _⟩ :=
  isMinimalCell_vertex (by decide) 0

/-- Layer 2 negative counter-witness for `IsMinimalCell`: `v_0` viewed inside the strictly larger
edge facet `M_0 = {0, 2}` is NOT a minimal cell. -/
theorem layer2_neg_isMinimalCell :
    ¬ (facetCycleDiagram 3 (by decide)).IsMinimalCell facetM0Three
        ⟨Sum.inl 0, cycleCellSupport_inl_subset_inr 0⟩ := by
  intro hmin
  have hAM : vertexSupportFace (0 : Fin 3) ≤ facetM0Three :=
    cycleCellSupport_inl_subset_inr 0
  have hmem :
      (⟨Sum.inl 0, hAM⟩ : (facetCycleDiagram 3 (by decide)).obj facetM0Three) ∈
        Set.range ((facetCycleDiagram 3 (by decide)).map hAM) :=
    ⟨⟨Sum.inl 0, Finset.Subset.refl _⟩, rfl⟩
  have hMA : facetM0Three ≤ vertexSupportFace (0 : Fin 3) := hmin hAM hmem
  have h0 : (0 : Fin 3) ∈ (vertexSupportFace (0 : Fin 3)).1 := hMA (by decide)
  exact (mem_cycleCellSupport_inl.mp h0).2 rfl

/-- Collapsing cocone from `puncturedEmptyApexDiagram 2` to `PointPoset`, identifying the disjoint
`0`-cells on `{0}` and `{1}` over an empty intersection `∅`. -/
def collapsingTwoCubeCocone : CubicalCocone (puncturedEmptyApexDiagram 2) PointPoset where
  leg _ _ := .pt
  leg_closed _ :=
    { mono := fun _ _ _ ↦ trivial
      injective := fun a b _ ↦ by
        rcases a with ⟨⟨⟩, _⟩
        rcases b with ⟨⟨⟩, _⟩
        rfl
      downward_closed := fun x q _ ↦ by
        rcases x with ⟨⟨⟩, hx⟩
        cases q
        exact ⟨⟨.pt, hx⟩, trivial, rfl⟩
      map_dim := fun _ ↦ rfl
      map_sign := fun _ _ hfac ↦ by
        rcases hfac with ⟨_, hd⟩
        change (0 : ℕ) = 0 + 1 at hd
        omega }
  comm _ _ := rfl

/-- `puncturedEmptyApexDiagram 2` IS intersective (since `{0} ∪ {1} = univ` in `Fin 2`), so its
`cubicalAmalgamCocone` satisfies `IsDisjointCubicalAmalgamation`, whereas `collapsingTwoCubeCocone`
is a valid `CubicalCocone` that **violates** `IsDisjointCubicalAmalgamation`. -/
theorem layer2_sep_cocone_not_disjoint :
    (puncturedEmptyApexDiagram 2).IsIntersective ∧
      ¬ IsDisjointCubicalAmalgamation collapsingTwoCubeCocone := by
  have haux : ∀ S T U : PuncturedCube 2, S ≤ U → T ≤ U → S.1 ≠ ∅ → T.1 ≠ ∅ → (S ⊓ T).1 ≠ ∅ := by
    decide
  have hInt2 : (puncturedEmptyApexDiagram 2).IsIntersective := by
    intro S T U hSU hTU x y _
    refine ⟨⟨.pt, haux S T U hSU hTU x.2 y.2⟩, ?_, ?_⟩
    · rcases x with ⟨⟨⟩, _⟩
      rfl
    · rcases y with ⟨⟨⟩, _⟩
      rfl
  refine ⟨hInt2, fun hDisj ↦ ?_⟩
  let S₀ : PuncturedCube 2 := PuncturedCube.singletonFace (by decide) 0
  let S₁ : PuncturedCube 2 := PuncturedCube.singletonFace (by decide) 1
  let x₀ : (puncturedEmptyApexDiagram 2).obj S₀ := ⟨.pt, by decide⟩
  let x₁ : (puncturedEmptyApexDiagram 2).obj S₁ := ⟨.pt, by decide⟩
  have hmem : PointPoset.pt ∈ Set.range (collapsingTwoCubeCocone.leg S₀) ∩
      Set.range (collapsingTwoCubeCocone.leg S₁) := ⟨⟨x₀, rfl⟩, ⟨x₁, rfl⟩⟩
  rw [hDisj S₀ S₁] at hmem
  rcases hmem with ⟨z, _⟩
  exact z.2 (by decide)

/-- Constant punctured `n`-cube diagram assigning a fixed `OrientedGradedPoset P` and identity maps
to every proper face. -/
def constCubicalDiagram (n : ℕ) (P : Type u) [OrientedGradedPoset P] : CubicalPosetDiagram n where
  obj _ := P
  map _ := _root_.id
  map_closed _ := IsClosedEmbedding.id P
  map_id _ _ := rfl
  map_comp _ _ _ := rfl

/-- Every constant cubical diagram `constCubicalDiagram n P` is intersective. -/
theorem constCubicalDiagram_isIntersective (n : ℕ) (P : Type u) [OrientedGradedPoset P] :
    (constCubicalDiagram n P).IsIntersective :=
  fun _ _ _ _ _ x _ hxy ↦ ⟨x, rfl, hxy⟩

/-- Projection `CubicalAmalgam (constCubicalDiagram n P) → P` (`p ↦ p.1.2`) is a closed cellular
embedding whenever `1 ≤ n`, hence reflects flow cycles from `CubicalAmalgam` to `P`. -/
theorem isFlowAcyclic_cubicalAmalgam_const {n : ℕ} (hn : 1 ≤ n) {P : Type u}
    [OrientedGradedPoset P] (hP : IsFlowAcyclic P) :
    IsFlowAcyclic (CubicalAmalgam (constCubicalDiagram n P)) := by
  have huniq : ∀ p : CubicalAmalgam (constCubicalDiagram n P),
      p.1.1 = PuncturedCube.emptyFace hn := fun p ↦
    le_antisymm (p.2 (PuncturedCube.emptyFace_le hn p.1.1) ⟨p.1.2, rfl⟩)
      (PuncturedCube.emptyFace_le hn p.1.1)
  have hcl : IsClosedEmbedding (fun p : CubicalAmalgam (constCubicalDiagram n P) ↦ p.1.2) :=
    { mono := fun _ _ ⟨_, hle⟩ ↦ hle
      injective := fun p q hpq ↦ by
        have hS : p.1.1 = q.1.1 := (huniq p).trans (huniq q).symm
        rcases p with ⟨⟨S, x⟩, hp⟩
        rcases q with ⟨⟨T, y⟩, hq⟩
        dsimp only at hS hpq
        subst hS hpq
        rfl
      downward_closed := fun p y hy ↦ by
        have hmin : (constCubicalDiagram n P).IsMinimalCell (PuncturedCube.emptyFace hn) y :=
          fun _ hA _ ↦ le_trans (PuncturedCube.emptyFace_le hn _) (le_of_le_of_eq le_rfl
            (le_antisymm hA (PuncturedCube.emptyFace_le hn _)).symm)
        refine ⟨⟨⟨PuncturedCube.emptyFace hn, y⟩, hmin⟩, ?_, rfl⟩
        exact ⟨PuncturedCube.emptyFace_le hn p.1.1, hy⟩
      map_dim := fun _ ↦ rfl
      map_sign := fun p q hfac ↦ by
        rcases hfac with ⟨⟨hpq, _⟩, _⟩
        change OrientedGradedPoset.sign p.1.2 q.1.2 =
          CubicalAmalgam.signFn (constCubicalDiagram n P) p q
        simp only [CubicalAmalgam.signFn, dif_pos hpq]
        rfl }
  exact hcl.isFlowAcyclic_domain hP

/-- Layer 2 positive vs. negative separation of `IsFlowAcyclic` on `CubicalAmalgam` at `n = 3`:
`CubicalAmalgam (constCubicalDiagram 3 WalkingArrow)` IS `IsFlowAcyclic` (and carries a non-trivial
directed flow step), whereas `CubicalAmalgam (facetCycleDiagram 3 _)` is NOT `IsFlowAcyclic`. -/
theorem layer2_sep_cubicalAmalgam_isFlowAcyclic :
    IsFlowAcyclic (CubicalAmalgam (constCubicalDiagram 3 WalkingArrow)) ∧
      (∃ u v : CubicalAmalgam (constCubicalDiagram 3 WalkingArrow), FlowStep u v) ∧
      ¬ IsFlowAcyclic (CubicalAmalgam (facetCycleDiagram 3 (by decide))) := by
  have hInt := constCubicalDiagram_isIntersective 3 WalkingArrow
  let S₀ := PuncturedCube.emptyFace (n := 3) (by decide)
  have hcl := amalgamLeg_isClosedEmbedding hInt S₀
  refine ⟨isFlowAcyclic_cubicalAmalgam_const (by decide) isFlowAcyclic_walkingArrow,
    ⟨amalgamLeg hInt S₀ .v0, amalgamLeg hInt S₀ .v1,
      hcl.map_flowStep (walkingArrow_flowStep_iff.mpr ⟨rfl, rfl⟩)⟩,
    not_isFlowAcyclic_cubicalAmalgam_facetCycle 3 (by decide)⟩

/-- **Dimension `n = 2` vs. `n = 3` Convex Acyclicity Dichotomy:**
For `n = 2` (`SAP`), `IsFlowConvex` pushouts of `IsFlowAcyclic` posets ALWAYS preserve
`IsFlowAcyclic` (`sap_flowConvex`), whereas at `n = 3` (`facetCycleDiagram 3`), all faces are
`IsFlowAcyclic` and all face maps are `IsFlowConvex`, yet cubical `3`-amalgamation destroys
`IsFlowAcyclic` in EVERY cocone target! -/
theorem layer2_dim2_vs_dim3_convex_acyclicity :
    (∀ (A B₁ B₂ : Type) [OrientedGradedPoset A] [OrientedGradedPoset B₁] [OrientedGradedPoset B₂]
        (i₁ : A → B₁) (i₂ : A → B₂) (hi₁ : IsFlowConvex i₁) (hi₂ : IsFlowConvex i₂),
      IsFlowAcyclic B₁ → IsFlowAcyclic B₂ →
        @IsFlowAcyclic (CanonicalPushout i₁ i₂)
          (canonicalPushoutOrientedGradedPoset hi₁.toIsClosedEmbedding hi₂.toIsClosedEmbedding)) ∧
    ((∀ S : PuncturedCube 3, IsFlowAcyclic ((facetCycleDiagram 3 (by decide)).obj S)) ∧
      (∀ {S T : PuncturedCube 3} (h : S ≤ T),
        IsFlowConvex ((facetCycleDiagram 3 (by decide)).map h)) ∧
      (∀ (Q : Type) [OrientedGradedPoset Q], IsFlowAcyclic Q →
        IsEmpty (CubicalCocone (facetCycleDiagram 3 (by decide)) Q))) :=
  ⟨fun _ _ _ _ _ _ _ _ hi₁ hi₂ hB₁ hB₂ ↦ (sap_flowConvex hi₁ hi₂).2.2.2.2.2 hB₁ hB₂,
    ⟨facetCycleFace_isFlowAcyclic 3 (by decide),
      fun h ↦ facetCycleMap_isFlowConvex 3 (by decide) h,
      fun _ _ hQ ↦ no_flowAcyclic_cubical_amalgam_of_three_le 3 (by decide) hQ⟩⟩

/-! ### Layer 3: Projection & Derived Sanity (Stock Mathlib Classes & Cardinality/Iso Lemmas) -/

/-- Layer 3 stock `SemilatticeInf` projection check on `PuncturedCube n`. -/
def puncturedCubeSemilatticeInfCheck (n : ℕ) : SemilatticeInf (PuncturedCube n) := inferInstance

/-- Layer 3 stock `PartialOrder` projection check on `PuncturedCube n`. -/
def puncturedCubePartialOrderCheck (n : ℕ) : PartialOrder (PuncturedCube n) := inferInstance

/-- Layer 3 stock `Fintype` projection check on `PuncturedCube n`. -/
def puncturedCubeFintypeCheck (n : ℕ) : Fintype (PuncturedCube n) := inferInstance

/-- Layer 3 stock `PartialOrder` projection check on `CubicalAmalgam D`. -/
def cubicalAmalgamPartialOrderCheck {n : ℕ} (D : CubicalPosetDiagram n) :
    PartialOrder (CubicalAmalgam D) := inferInstance

/-- Layer 3 stock `OrderIso` (`≃o`) principal-closure equivalence check on `amalgamLeg`. -/
noncomputable def amalgamLegClosureOrderIsoCheck {n : ℕ} {D : CubicalPosetDiagram n}
    (hInt : D.IsIntersective) (S : PuncturedCube n) (x : D.obj S) :
    cl (amalgamLeg hInt S x) ≃o cl x :=
  (amalgamLeg_isClosedEmbedding hInt S).clOrderIso x

/-- Derived sanity check 1: `PuncturedCube 3` has `2^3 - 1 = 7` proper faces. -/
theorem derived_card_puncturedCube_three : Fintype.card (PuncturedCube 3) = 7 := by
  rw [PuncturedCube.card_eq]
  rfl

/-- Derived sanity check 2: support cardinalities `|A_i| = n - 2` and `|M_i| = n - 1` for `2 ≤ n`.
-/
theorem derived_card_cycleCellSupports {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (cycleCellSupport n (Sum.inl i)).card = n - 2 ∧
      (cycleCellSupport n (Sum.inr i)).card = n - 1 := by
  have hmem_succ : finSucc i ∈ (Finset.univ : Finset (Fin n)).erase i :=
    Finset.mem_erase.mpr ⟨finSucc_ne_self hn i, Finset.mem_univ _⟩
  constructor
  · simp only [cycleCellSupport, Finset.card_erase_of_mem hmem_succ,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  · simp only [cycleCellSupport, Finset.card_erase_of_mem (Finset.mem_univ (finSucc i)),
      Finset.card_univ, Fintype.card_fin]

/-- Exact characterization of minimal cells in `facetCycleDiagram n hn`: `(S, ⟨c, hc⟩)` is minimal
iff `S.1 = cycleCellSupport n c`. -/
theorem facetCycle_isMinimalCell_iff {n : ℕ} (hn : 3 ≤ n) (S : PuncturedCube n)
    (x : (facetCycleDiagram n hn).obj S) :
    (facetCycleDiagram n hn).IsMinimalCell S x ↔ S.1 = cycleCellSupport n x.1 := by
  let A_x : PuncturedCube n := ⟨cycleCellSupport n x.1, cycleCellSupport_ne_univ x.1⟩
  constructor
  · intro hmin
    have hAS : A_x ≤ S := x.2
    have hSA : S ≤ A_x := hmin hAS ⟨⟨x.1, Finset.Subset.refl _⟩, Subtype.ext rfl⟩
    exact congrArg Subtype.val (le_antisymm hSA hAS)
  · intro hS B _ ⟨b, hb⟩
    have hbx : b.1 = x.1 := congrArg FacetCycleFace.val hb
    change S.1 ⊆ B.1
    rw [hS, ← hbx]
    exact b.2

/-- Derived sanity check 3: explicit `OrderIso` (`≃o`) identifying the minimal-support amalgamation
`CubicalAmalgam (facetCycleDiagram n hn)` with the full directed `n`-cycle `DirectedCycleCell n`.
-/
def cubicalAmalgamFacetCycleOrderIso (n : ℕ) (hn : 3 ≤ n) :
    CubicalAmalgam (facetCycleDiagram n hn) ≃o DirectedCycleCell n where
  toFun p := p.1.2.1
  invFun c :=
    ⟨⟨⟨cycleCellSupport n c, cycleCellSupport_ne_univ c⟩, ⟨c, Finset.Subset.refl _⟩⟩,
      (facetCycle_isMinimalCell_iff hn ⟨cycleCellSupport n c, cycleCellSupport_ne_univ c⟩
        ⟨c, Finset.Subset.refl _⟩).mpr rfl⟩
  left_inv p := by
    rcases p with ⟨⟨S, ⟨c, hc⟩⟩, hmin⟩
    have hS : S = ⟨cycleCellSupport n c, cycleCellSupport_ne_univ c⟩ :=
      PuncturedCube.ext ((facetCycle_isMinimalCell_iff hn S ⟨c, hc⟩).mp hmin)
    subst hS
    rfl
  right_inv _ := rfl
  map_rel_iff' {p q} := by
    constructor
    · intro hle
      have hpS : p.1.1.1 = cycleCellSupport n p.1.2.1 :=
        (facetCycle_isMinimalCell_iff hn p.1.1 p.1.2).mp p.2
      have hqS : q.1.1.1 = cycleCellSupport n q.1.2.1 :=
        (facetCycle_isMinimalCell_iff hn q.1.1 q.1.2).mp q.2
      have hpq : p.1.1 ≤ q.1.1 := by
        change p.1.1.1 ⊆ q.1.1.1
        rw [hpS, hqS]
        exact cycleCellSupport_mono hle
      exact ⟨hpq, hle⟩
    · rintro ⟨_, hle⟩
      exact hle

/-- Derived sanity check 4: `CubicalAmalgam (facetCycleDiagram n hn)` has `2 * n` cells (`6` cells
= `3` vertices + `3` directed edges at `n = 3`). -/
theorem derived_card_cubicalAmalgam_facetCycle (n : ℕ) (hn : 3 ≤ n) :
    Fintype.card (CubicalAmalgam (facetCycleDiagram n hn)) = 2 * n ∧
      Fintype.card (CubicalAmalgam (facetCycleDiagram 3 (by decide))) = 6 := by
  have hcard : ∀ (m : ℕ) (hm : 3 ≤ m),
      Fintype.card (CubicalAmalgam (facetCycleDiagram m hm)) = 2 * m := fun m hm ↦ by
    rw [Fintype.card_congr (cubicalAmalgamFacetCycleOrderIso m hm).toEquiv]
    change Fintype.card (Fin m ⊕ Fin m) = 2 * m
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  exact ⟨hcard n hn, hcard 3 (by decide)⟩

/-- `2`-element graded poset `GapPoset` (`bot < top` with `dim bot = 0`, `dim top = 2`), providing a
negative `IsCoveringGraded` witness. -/
inductive GapPoset : Type
  | bot
  | top
  deriving DecidableEq, Repr

instance instOrientedGradedPosetGapPoset : OrientedGradedPoset GapPoset where
  le a b := a = .bot ∨ b = .top
  le_refl a := by cases a <;> simp
  le_trans a b c hab hbc := by cases a <;> cases b <;> cases c <;> simp_all
  le_antisymm a b hab hba := by cases a <;> cases b <;> simp_all
  dim
    | .bot => 0
    | .top => 2
  dim_strictMono a b h := by
    rcases h with ⟨hab, hba⟩
    cases a <;> cases b <;> simp_all
  sign _ _ := false

/-- Layer 2 `IsCoveringGraded` separation: `PointPoset`, `WalkingArrow`, `FacetCycleFace n S`,
and `CubicalAmalgam (puncturedEmptyApexDiagram 2)` satisfy `IsCoveringGraded`, whereas `GapPoset`
violates `IsCoveringGraded`. -/
theorem layer2_sep_isCoveringGraded :
    IsCoveringGraded PointPoset ∧
      IsCoveringGraded WalkingArrow ∧
      IsCoveringGraded (CubicalAmalgam (puncturedEmptyApexDiagram 2)) ∧
      ¬ IsCoveringGraded GapPoset := by
  have hPt : IsCoveringGraded PointPoset := fun a b h ↦ by
    rcases a with ⟨⟩; rcases b with ⟨⟩
    exact False.elim (lt_irrefl PointPoset.pt h.1)
  have hWalk : IsCoveringGraded WalkingArrow := by
    intro a b hcov
    have hlt := hcov.1
    cases a <;> cases b
    · exact False.elim (lt_irrefl _ hlt)
    · exfalso
      have h1 : ¬ (WalkingArrow.v0 ≤ WalkingArrow.v1) := by decide
      exact h1 hlt.le
    · exact ⟨hlt.le, rfl⟩
    · exfalso
      have h1 : ¬ (WalkingArrow.v1 ≤ WalkingArrow.v0) := by decide
      exact h1 hlt.le
    · exact False.elim (lt_irrefl _ hlt)
    · exact ⟨hlt.le, rfl⟩
    · exact False.elim ((by decide : ¬ (WalkingArrow.edge ≤ WalkingArrow.v0)) hlt.le)
    · exact False.elim ((by decide : ¬ (WalkingArrow.edge ≤ WalkingArrow.v1)) hlt.le)
    · exact False.elim (lt_irrefl WalkingArrow.edge hlt)
  have hInt2 : (puncturedEmptyApexDiagram 2).IsIntersective := by
    have haux : ∀ S T U : PuncturedCube 2, S ≤ U → T ≤ U → S.1 ≠ ∅ → T.1 ≠ ∅ → (S ⊓ T).1 ≠ ∅ := by
      decide
    intro S T U hSU hTU x y _
    refine ⟨⟨.pt, haux S T U hSU hTU x.2 y.2⟩, ?_, ?_⟩ <;> · cases x; cases y; rfl
  have hFaceCov :
      ∀ S : PuncturedCube 2, IsCoveringGraded ((puncturedEmptyApexDiagram 2).obj S) := by
    intro S a b hcov
    have heq : a = b := by
      rcases a with ⟨⟨⟩, _⟩; rcases b with ⟨⟨⟩, _⟩; rfl
    exact False.elim (hcov.1.ne heq)
  have hNeg : ¬ IsCoveringGraded GapPoset := by
    intro hCov
    have hcov : GapPoset.bot ⋖ GapPoset.top := by
      refine ⟨⟨Or.inl rfl, fun h ↦ ?_⟩, fun c hbc hct ↦ ?_⟩
      · cases h with
        | inl h => cases h
        | inr h => cases h
      · cases c
        · exact hbc.ne rfl
        · exact hct.ne rfl
    have hfac := hCov hcov
    have hd := hfac.2
    change (2 : ℕ) = 0 + 1 at hd
    omega
  exact ⟨hPt, hWalk, isCoveringGraded_cubicalAmalgam hInt2 hFaceCov, hNeg⟩

/-! ### Layer 4: Kernel Axiom Gate (`#guard_msgs in #print axioms`) -/

section KernelAxiomGate

set_option linter.hashCommand false

/-- info: 'HomotopyCRM.PuncturedCube.card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.PuncturedCube.card_eq

/-- info: 'HomotopyCRM.cubical_ndap_closed_oriented_poset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.cubical_ndap_closed_oriented_poset

/-- info: 'HomotopyCRM.hasCubicalNDAP_iff_isIntersective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.hasCubicalNDAP_iff_isIntersective

/-- info: 'HomotopyCRM.facetCycleDiagram_isIntersective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.facetCycleDiagram_isIntersective

/-- info: 'HomotopyCRM.facetCycleFace_isFlowAcyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.facetCycleFace_isFlowAcyclic

/-- info: 'HomotopyCRM.facetCycleMap_isFlowConvex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.facetCycleMap_isFlowConvex

/-- info: 'HomotopyCRM.no_flowAcyclic_cubical_amalgam_of_three_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.no_flowAcyclic_cubical_amalgam_of_three_le

/-- info: 'HomotopyCRM.theorem10B_cubical_amalgamation_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theorem10B_cubical_amalgamation_dichotomy

/-- info: 'HomotopyCRM.Checks.layer2_pos_isIntersective_and_ndap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_pos_isIntersective_and_ndap

/-- info: 'HomotopyCRM.Checks.layer2_neg_isIntersective_and_ndap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_neg_isIntersective_and_ndap

/-- info: 'HomotopyCRM.Checks.layer2_sep_cocone_not_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_cocone_not_disjoint

/-- info: 'HomotopyCRM.Checks.layer2_sep_cubicalAmalgam_isFlowAcyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_cubicalAmalgam_isFlowAcyclic

/-- info: 'HomotopyCRM.Checks.layer2_dim2_vs_dim3_convex_acyclicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_dim2_vs_dim3_convex_acyclicity

/-- info: 'HomotopyCRM.Checks.cubicalAmalgamFacetCycleOrderIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.cubicalAmalgamFacetCycleOrderIso

/-- info: 'HomotopyCRM.Checks.derived_card_cubicalAmalgam_facetCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.derived_card_cubicalAmalgam_facetCycle

/-- info: 'HomotopyCRM.isCoveringGraded_cubicalAmalgam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.isCoveringGraded_cubicalAmalgam

/-- info: 'HomotopyCRM.FacetCycleFace.isCoveringGraded_facetCycleFace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.FacetCycleFace.isCoveringGraded_facetCycleFace

/--
info: 'HomotopyCRM.FacetCycleFace.facetCycleFace_zeroCells_card_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.FacetCycleFace.facetCycleFace_zeroCells_card_le_two

/-- info: 'HomotopyCRM.FacetCycleFace.facetCycleFace_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.FacetCycleFace.facetCycleFace_classification

/-- info: 'HomotopyCRM.Checks.layer2_sep_isCoveringGraded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_isCoveringGraded

end KernelAxiomGate

end Checks

end HomotopyCRM
