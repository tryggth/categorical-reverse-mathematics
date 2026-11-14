/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HomotopyCRM Formalization Team
-/
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Transfinite Ordinal Rank Completeness (`Theorem 9A`) and Lali Stabilization (`Proposition 11A`)

This module formalizes `MSG_014` (`TODO-15` Part B, **Theorem 9A** & **Proposition 11A**) of the
`HomotopyCRM` library, calibrating transfinite equivalence hierarchies and Noetherian Lali
split-idempotent ceilings along the verified strict 4-tier reflective localization ladder
`Cat^L_(∞,∞) ⊊ Cat^ω_(∞,∞) ⊊ Cat^coind_(∞,∞) ⊊ Cat^R_(∞,∞) := lim_κ Cat_(∞,n)`
(Ozornova–Rovelli–Walde `arXiv:2603.11005v2`, `arXiv:2608.28355`, `arXiv:2610.38698`;
Gepner–Heine `arXiv:2603.09903`).

## Main Results

1. **Coalgebraic Globular `(∞,∞)`-Systems & Equivalence Hierarchy (`GlobularInfSystem`):**
   - `GlobularInfSystem S` axiomatizes infinite-dimensional globular environments over a state
     space `S : Type u` (`Obj : S → Type u`, `hom : Obj s → Obj s → S`, `idMor`, `compMor`,
     `id_comp_id`) with zero universe bumps.
   - Formalizes genuine bottom-up inductive equivalences (`IsEquiv`), coinductive bisimulation
     equivalences (`IsCoindEquiv`), transfinite `θ`-stage candidate-inverse invertibility
     (`IsOrdinalInv θ`, well-founded on `Ordinal.{0}`), and `ω`-invertibility (`IsOmegaInv`),
     establishing `IsEquiv → IsCoindEquiv → IsOmegaInv ↔ IsOrdinalInv Ordinal.omega0`.

2. **Theorem 9A, Proposition 1A, & ORW Question 5.58 `α = 0` Stabilization (`RankedInfCat`):**
   - `RankedInfCat S` equips `GlobularInfSystem S` with `rank : S → Ordinal.{0}` decreasing
     strictly on positive-rank `hom`-states and forcing `rank s = 0 → IsEquiv`.
   - **Theorem 9A (`theorem9A_ordinal_rank_completeness`, `theorem9A_omega_completeness`):**
     Whenever `rank s ≤ θ`, `IsOrdinalInv θ f ↔ IsEquiv f`; at `θ = Ordinal.omega0`,
     `rank s ≤ Ordinal.omega0 → (IsOmegaInv f ↔ IsEquiv f)`.
   - **Proposition 1A (`ranked_coindEquiv_iff_isEquiv`):** In *any* `RankedInfCat` (arbitrary
     transfinite ordinal rank, even `ω + 1`), `IsCoindEquiv f ↔ IsEquiv f`.
   - **ORW Question 5.58 `α = 0` Stabilization (`orw_question558_stabilizes_at_zero`):** Whenever
     `rank s ≤ Ordinal.omega0`, every reachable `k`-cell hom-state `ReachableFrom s t` (`k ≥ 1`)
     satisfies `{f | IsOmegaInv f} = {f | IsEquiv f}` at stage `α = 0`.

3. **Unified `OmegaTowerState` & `CoindWalkState` Separation Models:**
   - `OmegaTowerState` is a single `RankedInfCat` simultaneously realizing rank `0` (`boolDisc` =
     `S⁰`), rank `1` (`chain 0` = `[1]`), rank `2` non-equivalence split-idempotent `2`-retracts
     (`chain 1`), all finite heights `chain d` (`rank = d + 1`), rank `ω` (`endo1`), and rank
     `ω + 1` (`apex`), proving `apexArrow_isOmegaInv : IsOmegaInv apexArrow` and
     `apexArrow_not_isEquiv : ¬ IsEquiv apexArrow` (exact sharpness of Theorem 9A at `ω + 1`).
   - `CoindWalkState` models the gaunt walking coinductive equivalence `E_coind`, separating
     `IsCoindEquiv` from `IsEquiv` outside `RankedInfCat`.

4. **Proposition 11A — Inductive Lali Split-Idempotent Ceiling `max K_x K_y + 2`:**
   - Formalizes coalgebraic `GlobularSimulation`, `LaliRetraction`, grounded higher cell boundaries
     `HomBoundary r t`, and local `(K, K)`-cell height `HasHomCellHeight K t`.
   - **Proposition 11A Part 1 (`prop11A_lali_stabilization_above_ceiling`):** Above ambient
     dimension `max K_x K_y + 2` (`m = r + 3`, `max K_x K_y ≤ r`), all grounded ambient `m`-cell
     spaces are contractible, every ambient `m`-cell satisfies `IsEquiv`, and the Lali
     split-idempotent endofunctor `E = L ∘ R` induces a bijection on ambient `m`-cells.
   - **Proposition 11A Part 2 (`prop11A_ceiling_sharp_at_max_add_two`):** On
     `JoinSuspState.joinCone K` (`{a} ⋆ Σ^{K+1}(S⁰)`), every hom-state has cell height `K`
     (`max K_x K_y + 2 = K + 2`), yet `E = const_a` fails to be bijective on ambient `(K + 2)`-cells
     (`Empty → Unit`) for **every** `K : ℕ`.

5. **Mandatory 4-Layer Definition Check Gate (`namespace Checks`):**
   - Verifies Inhabitation (Layer 1), Bidirectional Separation across all rank thresholds,
     split-idempotent `2`-retracts, coinductive vs. inductive equivalence, `HasHomCellHeight`, and
     the `K + 2` vs. `K + 3` Lali boundary (Layer 2), Mathlib `Ordinal` order/arithmetic sanity
     and strict 4-tier predicate separation (Layer 3), and the `#guard_msgs in #print axioms`
     Kernel Axiom Gate (Layer 4).
-/

namespace HomotopyCRM

universe u u₁ u₂ u₃

/-! ## Section 1: State-Coalgebraic `GlobularInfSystem` & Transfinite `IsOrdinalInv` -/

/-- A state-coalgebraic globular `(∞,∞)`-categorical environment over a state space `S : Type u`.
For `s : S`, `Obj s` is the type of `0`-cells of `s`, and `hom x y : S` is the state classifying
`1`-morphisms `x → y`; iterating `hom` yields `k`-morphisms of every dimension `k ≥ 1` without
universe bumps. -/
class GlobularInfSystem (S : Type u) where
  /-- Type of `0`-cells in state `s : S`. -/
  Obj : S → Type u
  /-- Hom-state `hom x y : S` classifying `1`-morphisms from `x` to `y`. -/
  hom : ∀ {s : S}, Obj s → Obj s → S
  /-- Identity `1`-morphism `idMor x : Obj (hom x x)` on `x : Obj s`. -/
  idMor : ∀ {s : S} (x : Obj s), Obj (hom x x)
  /-- Diagrammatic `1`-morphism composition `compMor f g : Obj (hom x z)`. -/
  compMor : ∀ {s : S} {x y z : Obj s}, Obj (hom x y) → Obj (hom y z) → Obj (hom x z)
  /-- Identity self-composition law `compMor (idMor x) (idMor x) = idMor x`. -/
  id_comp_id : ∀ {s : S} (x : Obj s), compMor (idMor x) (idMor x) = idMor x

open GlobularInfSystem

/-- Genuine bottom-up inductive equivalence (`IsEquiv f`) in a `GlobularInfSystem S`, generated by
identity `1`-morphisms `idMor x` and reversible pairs `(f, g)` carrying inductively invertible
`2`-morphism cancellation witnesses `η : compMor f g ⇒ idMor x` and `ε : compMor g f ⇒ idMor y`. -/
inductive IsEquiv {S : Type u} [GlobularInfSystem S] :
    ∀ {s : S} {x y : Obj s}, Obj (hom x y) → Prop
  | id {s : S} (x : Obj s) : IsEquiv (idMor x)
  | mk {s : S} {x y : Obj s} (f : Obj (hom x y)) (g : Obj (hom y x))
      (η : Obj (hom (compMor f g) (idMor x)))
      (ε : Obj (hom (compMor g f) (idMor y))) :
      IsEquiv η → IsEquiv ε → IsEquiv f

/-- Coinductive equivalence (`IsCoindEquiv f`) in a `GlobularInfSystem S`, defined as the greatest
post-fixed point (bisimulation) of reversible `1`-morphisms across all states. -/
def IsCoindEquiv {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} (f : Obj (hom x y)) : Prop :=
  ∃ Inv : ∀ {t : S} {u w : Obj t}, Obj (hom u w) → Prop,
    Inv f ∧ ∀ {t : S} {u w : Obj t} {h : Obj (hom u w)}, Inv h →
      ∃ (g : Obj (hom w u))
        (η : Obj (hom (compMor h g) (idMor u)))
        (ε : Obj (hom (compMor g h) (idMor w))),
        Inv η ∧ Inv ε

/-- Every inductive equivalence `IsEquiv f` is a coinductive equivalence `IsCoindEquiv f`. -/
theorem IsEquiv.isCoindEquiv {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} {f : Obj (hom x y)} (hf : IsEquiv f) :
    IsCoindEquiv f := by
  refine ⟨fun h ↦ IsEquiv h, hf, ?_⟩
  intro t u w h hh
  cases hh with
  | id =>
    refine ⟨idMor u, ?_⟩
    rw [id_comp_id u]
    exact ⟨idMor (idMor u), idMor (idMor u), IsEquiv.id _, IsEquiv.id _⟩
  | mk _ g η ε hη hε =>
    exact ⟨g, η, ε, hη, hε⟩

/-- Transfinite ordinal-indexed candidate-inverse invertibility (`IsOrdinalInv θ f`) in a
`GlobularInfSystem S`, defined by well-founded recursion on `θ : Ordinal.{0}`. -/
def IsOrdinalInv {S : Type u} [GlobularInfSystem S] (θ : Ordinal.{0})
    {s : S} {x y : Obj s} (f : Obj (hom x y)) : Prop :=
  ∀ α < θ, ∃ (g : Obj (hom y x))
    (η : Obj (hom (compMor f g) (idMor x)))
    (ε : Obj (hom (compMor g f) (idMor y))),
    IsOrdinalInv α η ∧ IsOrdinalInv α ε
termination_by θ

/-- Explicit unfolding characterization of `IsOrdinalInv θ f`. -/
theorem isOrdinalInv_iff {S : Type u} [GlobularInfSystem S] (θ : Ordinal.{0})
    {s : S} {x y : Obj s} (f : Obj (hom x y)) :
    IsOrdinalInv θ f ↔
      ∀ α < θ, ∃ (g : Obj (hom y x))
        (η : Obj (hom (compMor f g) (idMor x)))
        (ε : Obj (hom (compMor g f) (idMor y))),
        IsOrdinalInv α η ∧ IsOrdinalInv α ε := by
  rw [IsOrdinalInv]

/-- Stage `0` invertibility `IsOrdinalInv 0 f` holds vacuously for every `1`-morphism `f`. -/
@[simp]
theorem isOrdinalInv_zero {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} (f : Obj (hom x y)) :
    IsOrdinalInv 0 f ↔ True := by
  rw [isOrdinalInv_iff]
  exact ⟨fun _ ↦ trivial, fun _ α hα ↦ False.elim ((zero_le α).not_gt hα)⟩

/-- Unconditional proof of `IsOrdinalInv 0 f` for any `1`-morphism `f`. -/
theorem isOrdinalInv_zero_of_any {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} (f : Obj (hom x y)) :
    IsOrdinalInv 0 f :=
  (isOrdinalInv_zero f).mpr trivial

/-- Antitonicity of `IsOrdinalInv`: higher ordinal stages imply all lower ordinal stages. -/
theorem isOrdinalInv_anti {S : Type u} [GlobularInfSystem S]
    {θ₁ θ₂ : Ordinal.{0}} (hθ : θ₁ ≤ θ₂) {s : S} {x y : Obj s} {f : Obj (hom x y)}
    (hf : IsOrdinalInv θ₂ f) :
    IsOrdinalInv θ₁ f := by
  rw [isOrdinalInv_iff] at hf ⊢
  exact fun α hα ↦ hf α (lt_of_lt_of_le hα hθ)

/-- Successor unfolding law `IsOrdinalInv (θ + 1) f` via `θ`-invertible cancellation witnesses. -/
theorem isOrdinalInv_add_one {S : Type u} [GlobularInfSystem S] (θ : Ordinal.{0})
    {s : S} {x y : Obj s} (f : Obj (hom x y)) :
    IsOrdinalInv (θ + 1) f ↔
      ∃ (g : Obj (hom y x))
        (η : Obj (hom (compMor f g) (idMor x)))
        (ε : Obj (hom (compMor g f) (idMor y))),
        IsOrdinalInv θ η ∧ IsOrdinalInv θ ε := by
  rw [isOrdinalInv_iff, Ordinal.add_one_eq_succ]
  constructor
  · intro h
    exact h θ (Order.lt_succ θ)
  · rintro ⟨g, η, ε, hη, hε⟩ α hα
    have hle : α ≤ θ := Order.lt_succ_iff.mp hα
    exact ⟨g, η, ε, isOrdinalInv_anti hle hη, isOrdinalInv_anti hle hε⟩

/-- Every coinductive equivalence is `θ`-invertible at every ordinal `θ : Ordinal.{0}`. -/
theorem IsCoindEquiv.isOrdinalInv {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} {f : Obj (hom x y)} (hf : IsCoindEquiv f) (θ : Ordinal.{0}) :
    IsOrdinalInv θ f := by
  rcases hf with ⟨Inv, hf₀, hstep⟩
  have hmain : ∀ (β : Ordinal.{0}) {t : S} {u w : Obj t} {h : Obj (hom u w)},
      Inv h → IsOrdinalInv β h := by
    intro β
    induction β using Ordinal.induction with
    | h β ih =>
      intro t u w h hh
      rw [isOrdinalInv_iff]
      intro α hα
      rcases hstep hh with ⟨g, η, ε, hη, hε⟩
      exact ⟨g, η, ε, ih α hα hη, ih α hα hε⟩
  exact hmain θ hf₀

/-- Every inductive equivalence is `θ`-invertible at every ordinal `θ : Ordinal.{0}`. -/
theorem IsEquiv.isOrdinalInv {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} {f : Obj (hom x y)} (hf : IsEquiv f) (θ : Ordinal.{0}) :
    IsOrdinalInv θ f :=
  hf.isCoindEquiv.isOrdinalInv θ

/-- Identity `1`-morphisms `idMor x` are `θ`-invertible at every ordinal `θ : Ordinal.{0}`. -/
theorem isOrdinalInv_id {S : Type u} [GlobularInfSystem S] (θ : Ordinal.{0})
    {s : S} (x : Obj s) :
    IsOrdinalInv θ (idMor x) :=
  (IsEquiv.id x).isOrdinalInv θ

/-- Finite-stage `ω`-invertibility (`IsOmegaInv f`), requiring `n`-invertibility at all `n : ℕ`. -/
def IsOmegaInv {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} (f : Obj (hom x y)) : Prop :=
  ∀ n : ℕ, IsOrdinalInv (n : Ordinal.{0}) f

/-- Exact equivalence between `IsOmegaInv f` (`∀ n : ℕ, IsOrdinalInv n f`) and limit-stage
invertibility `IsOrdinalInv Ordinal.omega0 f` at the first infinite ordinal `ω`. -/
theorem isOmegaInv_iff_isOrdinalInv_omega0 {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} {f : Obj (hom x y)} :
    IsOmegaInv f ↔ IsOrdinalInv Ordinal.omega0 f := by
  constructor
  · intro hf
    rw [isOrdinalInv_iff]
    intro α hα
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hα
    have hlt : (n : Ordinal.{0}) < ((n + 1 : ℕ) : Ordinal.{0}) :=
      Nat.cast_lt.mpr (Nat.lt_succ_self n)
    exact (isOrdinalInv_iff ((n + 1 : ℕ) : Ordinal.{0}) f).mp (hf (n + 1)) n hlt
  · intro hf n
    exact isOrdinalInv_anti (le_of_lt (Ordinal.nat_lt_omega0 n)) hf

/-- Every coinductive equivalence is `ω`-invertible (`IsOmegaInv`). -/
theorem IsCoindEquiv.isOmegaInv {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} {f : Obj (hom x y)} (hf : IsCoindEquiv f) :
    IsOmegaInv f :=
  isOmegaInv_iff_isOrdinalInv_omega0.mpr (hf.isOrdinalInv Ordinal.omega0)

/-- Every inductive equivalence is `ω`-invertible (`IsOmegaInv`). -/
theorem IsEquiv.isOmegaInv {S : Type u} [GlobularInfSystem S]
    {s : S} {x y : Obj s} {f : Obj (hom x y)} (hf : IsEquiv f) :
    IsOmegaInv f :=
  hf.isCoindEquiv.isOmegaInv

/-! ## Section 2: `RankedInfCat`, Theorem 9A, Proposition 1A, & ORW Question 5.58 -/

/-- An ordinal-ranked `(∞,∞)`-categorical environment (`RankedInfCat S`), equipping a
`GlobularInfSystem S` with an ordinal rank `rank : S → Ordinal.{0}` such that rank-`0` states are
groupoidal (`IsEquiv` on all `1`-morphisms with rank-`0` hom-animae) and positive-rank states have
strictly lower-rank `hom`-states. -/
class RankedInfCat (S : Type u) extends GlobularInfSystem S where
  /-- Ordinal hom-rank assigned to each categorical state `s : S`. -/
  rank : S → Ordinal.{0}
  /-- Rank-`0` states have only inductive equivalences as `1`-morphisms. -/
  rank_zero_equiv : ∀ {s : S}, rank s = 0 → ∀ {x y : Obj s} (f : Obj (hom x y)),
    @IsEquiv S toGlobularInfSystem s x y f
  /-- Hom-states of a rank-`0` groupoidal state also have ordinal rank `0`. -/
  rank_hom_zero : ∀ {s : S}, rank s = 0 → ∀ (x y : Obj s), rank (hom x y) = 0
  /-- Strict ordinal descent along `hom x y` whenever `0 < rank s`. -/
  rank_hom_lt : ∀ {s : S}, 0 < rank s → ∀ (x y : Obj s), rank (hom x y) < rank s

open RankedInfCat

/-- In any `RankedInfCat S`, `rank (hom x y) ≤ rank s` holds unconditionally. -/
theorem rank_hom_le {S : Type u} [RankedInfCat S] {s : S} (x y : Obj s) :
    rank (hom x y) ≤ rank s := by
  rcases eq_or_lt_of_le (zero_le (rank s)) with hzero | hpos
  · rw [rank_hom_zero hzero.symm x y, ← hzero]
  · exact le_of_lt (rank_hom_lt hpos x y)

/-- **Theorem 9A — Transfinite Ordinal Rank Completeness (`theorem9A_ordinal_rank_completeness`):**
In any `RankedInfCat S`, if `rank s ≤ θ`, then transfinite `θ`-stage invertibility `IsOrdinalInv θ`
coincides with genuine bottom-up inductive equivalence `IsEquiv` on `s`. -/
theorem theorem9A_ordinal_rank_completeness {S : Type u} [RankedInfCat S]
    {θ : Ordinal.{0}} {s : S} (hrank : rank s ≤ θ)
    {x y : Obj s} {f : Obj (hom x y)} :
    IsOrdinalInv θ f ↔ IsEquiv f := by
  refine ⟨?_, fun hf ↦ hf.isOrdinalInv θ⟩
  revert s x y f hrank
  induction θ using Ordinal.induction with
  | h θ ih =>
    intro s hrank x y f hf
    rcases eq_or_lt_of_le (zero_le (rank s)) with hzero | hpos
    · exact rank_zero_equiv hzero.symm f
    · let α : Ordinal.{0} := max (rank (hom x x)) (rank (hom y y))
      have hα_lt_s : α < rank s :=
        max_lt (rank_hom_lt hpos x x) (rank_hom_lt hpos y y)
      have hα_lt_θ : α < θ := lt_of_lt_of_le hα_lt_s hrank
      rcases (isOrdinalInv_iff θ f).mp hf α hα_lt_θ with ⟨g, η, ε, hη, hε⟩
      have hη_eq : IsEquiv η := ih α hα_lt_θ (le_max_left _ _) hη
      have hε_eq : IsEquiv ε := ih α hα_lt_θ (le_max_right _ _) hε
      exact IsEquiv.mk f g η ε hη_eq hε_eq

/-- At `θ = rank s`, `IsOrdinalInv (rank s) f ↔ IsEquiv f` holds unconditionally in any
`RankedInfCat S`. -/
theorem ranked_isOrdinalInv_rank_iff_isEquiv {S : Type u} [RankedInfCat S]
    {s : S} {x y : Obj s} {f : Obj (hom x y)} :
    IsOrdinalInv (rank s) f ↔ IsEquiv f :=
  theorem9A_ordinal_rank_completeness le_rfl

/-- **Proposition 1A — Unconditional Coinductive Completeness of Ordinal-Ranked Systems
(`ranked_coindEquiv_iff_isEquiv`):**
In *any* `RankedInfCat S` (of arbitrary transfinite ordinal rank `rank s`, including `ω + 1`),
coinductive equivalence `IsCoindEquiv` collapses to genuine inductive equivalence `IsEquiv`. -/
theorem ranked_coindEquiv_iff_isEquiv {S : Type u} [RankedInfCat S]
    {s : S} {x y : Obj s} {f : Obj (hom x y)} :
    IsCoindEquiv f ↔ IsEquiv f :=
  ⟨fun hf ↦ ranked_isOrdinalInv_rank_iff_isEquiv.mp (hf.isOrdinalInv (rank s)),
    IsEquiv.isCoindEquiv⟩

/-- **Theorem 9A (`θ = ω` Specialization — `theorem9A_omega_completeness`):**
In any `RankedInfCat S`, if `rank s ≤ Ordinal.omega0`, then `ω`-invertibility `IsOmegaInv f`
coincides with genuine inductive equivalence `IsEquiv f`. -/
theorem theorem9A_omega_completeness {S : Type u} [RankedInfCat S]
    {s : S} (hrank : rank s ≤ Ordinal.omega0)
    {x y : Obj s} {f : Obj (hom x y)} :
    IsOmegaInv f ↔ IsEquiv f :=
  isOmegaInv_iff_isOrdinalInv_omega0.trans (theorem9A_ordinal_rank_completeness hrank)

/-- Reflexive-transitive closure of `hom`-state transitions (`ReachableFrom s t`), indexing all
higher `k`-morphism hom-environments (`k ≥ 1`) nested inside `s : S`. -/
inductive ReachableFrom {S : Type u} [GlobularInfSystem S] (s : S) : S → Prop
  | refl : ReachableFrom s s
  | step {t : S} : ReachableFrom s t → ∀ (x y : Obj t), ReachableFrom s (hom x y)

/-- Ordinal rank is monotone non-increasing along arbitrary nested `hom`-transitions
`ReachableFrom s t`. -/
theorem ReachableFrom.rank_le {S : Type u} [RankedInfCat S] {s t : S}
    (h : ReachableFrom s t) :
    rank t ≤ rank s := by
  induction h with
  | refl => exact le_rfl
  | step _ x y ih => exact le_trans (rank_hom_le x y) ih

/-- **ORW Question 5.58 `α = 0` Stabilization Corollary (`orw_question558_stabilizes_at_zero`):**
Whenever `rank s ≤ Ordinal.omega0`, the single-step `ω`-invertible generator class
`{f | IsOmegaInv f}` equals `{f | IsEquiv f}` simultaneously across *every* reachable `k`-cell
hom-environment `ReachableFrom s t` (`k ≥ 1`), so Ozornova–Rovelli–Walde's transfinite
`α`-inductive localization tower (`arXiv:2603.11005v2`, Question 5.58) stabilizes immediately at
stage `α = 0`. -/
theorem orw_question558_stabilizes_at_zero {S : Type u} [RankedInfCat S]
    {s : S} (hrank : rank s ≤ Ordinal.omega0) :
    (∀ (x y : Obj s),
      {f : Obj (hom x y) | IsOmegaInv f} = {f : Obj (hom x y) | IsEquiv f}) ∧
      ∀ {t : S}, ReachableFrom s t → ∀ (u w : Obj t),
        {f : Obj (hom u w) | IsOmegaInv f} = {f : Obj (hom u w) | IsEquiv f} := by
  refine ⟨fun x y ↦ ?_, fun ht u w ↦ ?_⟩
  · ext f
    exact theorem9A_omega_completeness hrank
  · ext f
    exact theorem9A_omega_completeness (le_trans ht.rank_le hrank)

/-! ## Section 3: Unified `OmegaTowerState` (`0`, `1`, `2`-Retract, `ω`, `ω + 1`) & `CoindWalkState`
-/

/-- Unified inductive state space `OmegaTowerState` simultaneously realizing:
- `pt`, `empty`, `natDisc`, `boolDisc` (`S⁰`) at ordinal rank `0`,
- `chain 0` = walking directed `1`-arrow `[1]` at ordinal rank `1`,
- `chain 1` = non-equivalence split-idempotent `2`-retract (Lali `2`-category) at ordinal rank `2`,
- `chain d` = finite candidate-inverse probe of exact invertibility height `d` (`rank = d + 1`),
- `endo1` = supremum-rank `ω` endomorphism environment (`rank = ω`), and
- `apex` = rank-`(ω + 1)` retract counterexample (`rank = ω + 1`) proving sharpness of Theorem 9A.
-/
inductive OmegaTowerState : Type
  | pt : OmegaTowerState
  | empty : OmegaTowerState
  | natDisc : OmegaTowerState
  | boolDisc : OmegaTowerState
  | chain : ℕ → OmegaTowerState
  | endo1 : OmegaTowerState
  | apex : OmegaTowerState
  deriving DecidableEq, Repr

namespace OmegaTowerState

/-- Underlying `0`-cell type of each state in `OmegaTowerState`. -/
def omegaObj : OmegaTowerState → Type
  | .pt => Unit
  | .empty => Empty
  | .natDisc => ℕ
  | .boolDisc => Bool
  | .chain _ => Bool
  | .endo1 => Option ℕ
  | .apex => Bool

/-- Hom-state classification on the discrete groupoid `natDisc` (`ℕ`). -/
def natDiscHom (m n : ℕ) : OmegaTowerState :=
  if m = n then .pt else .empty

/-- Hom-state classification on the discrete `0`-sphere `boolDisc` (`S⁰`). -/
def boolDiscHom : Bool → Bool → OmegaTowerState
  | false, false => .pt
  | true, true => .pt
  | false, true => .empty
  | true, false => .empty

/-- Hom-state classification on the finite probe tower `chain d`. -/
def chainHom : ℕ → Bool → Bool → OmegaTowerState
  | 0, false, false => .pt
  | 0, false, true => .pt
  | 0, true, false => .empty
  | 0, true, true => .pt
  | _ + 1, false, false => .pt
  | _ + 1, false, true => .pt
  | _ + 1, true, false => .pt
  | d + 1, true, true => .chain d

/-- Hom-state classification on the rank-`ω` endomorphism environment `endo1`. -/
def endoHom : Option ℕ → Option ℕ → OmegaTowerState
  | none, none => .pt
  | none, some _ => .pt
  | some _, none => .pt
  | some d, some _ => .chain d

/-- Hom-state classification on the rank-`(ω + 1)` state `apex`. -/
def apexHom : Bool → Bool → OmegaTowerState
  | false, false => .pt
  | false, true => .pt
  | true, false => .natDisc
  | true, true => .endo1

/-- Unified hom-state transition `omegaHom` across `OmegaTowerState`. -/
def omegaHom : ∀ {s : OmegaTowerState}, omegaObj s → omegaObj s → OmegaTowerState
  | .pt, _, _ => .pt
  | .empty, x, _ => Empty.elim x
  | .natDisc, m, n => natDiscHom m n
  | .boolDisc, b₁, b₂ => boolDiscHom b₁ b₂
  | .chain d, b₁, b₂ => chainHom d b₁ b₂
  | .endo1, u, w => endoHom u w
  | .apex, b₁, b₂ => apexHom b₁ b₂

instance instSubsingletonNatDiscHom (m n : ℕ) :
    Subsingleton (omegaObj (natDiscHom m n)) := by
  unfold natDiscHom
  split_ifs
  · exact inferInstanceAs (Subsingleton Unit)
  · exact inferInstanceAs (Subsingleton Empty)

/-- Identity `1`-morphism in `natDisc`. -/
def natDiscId (m : ℕ) : omegaObj (natDiscHom m m) :=
  cast (congrArg omegaObj (if_pos rfl).symm) (() : Unit)

/-- Composition of `1`-morphisms in `natDisc`. -/
def natDiscComp {m n k : ℕ} (f : omegaObj (natDiscHom m n))
    (g : omegaObj (natDiscHom n k)) : omegaObj (natDiscHom m k) :=
  if hmn : m = n then
    if hnk : n = k then
      cast (congrArg omegaObj (if_pos (hmn.trans hnk)).symm) (() : Unit)
    else
      Empty.elim (cast (congrArg omegaObj (if_neg hnk)) g)
  else
    Empty.elim (cast (congrArg omegaObj (if_neg hmn)) f)

/-- Identity `1`-morphism in `boolDisc`. -/
def boolDiscId : ∀ b : Bool, omegaObj (boolDiscHom b b)
  | false => ()
  | true => ()

/-- Composition of `1`-morphisms in `boolDisc`. -/
def boolDiscComp : ∀ {x y z : Bool},
    omegaObj (boolDiscHom x y) → omegaObj (boolDiscHom y z) → omegaObj (boolDiscHom x z)
  | false, false, false, _, _ => ()
  | true, true, true, _, _ => ()
  | false, true, _, f, _ => Empty.elim f
  | true, false, _, f, _ => Empty.elim f
  | false, false, true, _, g => Empty.elim g
  | true, true, false, _, g => Empty.elim g

/-- Identity `1`-morphism in `chain d`. -/
def chainId : ∀ (d : ℕ) (b : Bool), omegaObj (chainHom d b b)
  | 0, false => ()
  | 0, true => ()
  | _ + 1, false => ()
  | _ + 1, true => true

/-- Composition of `1`-morphisms in `chain d`: at `d + 1`, `compMor v_{d+1} u_{d+1} = false` is the
non-trivial idempotent `e` (`false && false = false`) on `true`, while `idMor true = true`. -/
def chainComp : ∀ (d : ℕ) {x y z : Bool},
    omegaObj (chainHom d x y) → omegaObj (chainHom d y z) → omegaObj (chainHom d x z)
  | 0, false, false, false, _, _ => ()
  | 0, false, false, true, _, _ => ()
  | 0, false, true, true, _, _ => ()
  | 0, true, true, true, _, _ => ()
  | 0, true, false, _, f, _ => Empty.elim f
  | 0, false, true, false, _, g => Empty.elim g
  | _ + 1, false, _, false, _, _ => ()
  | _ + 1, false, _, true, _, _ => ()
  | _ + 1, true, _, false, _, _ => ()
  | _ + 1, true, false, true, _, _ => false
  | _ + 1, true, true, true, a, b => a && b

/-- Identity `1`-morphism in `endo1`. -/
def endoId : ∀ u : Option ℕ, omegaObj (endoHom u u)
  | none => ()
  | some _ => true

/-- Composition of `1`-morphisms in `endo1`. -/
def endoComp : ∀ {x y z : Option ℕ},
    omegaObj (endoHom x y) → omegaObj (endoHom y z) → omegaObj (endoHom x z)
  | none, _, none, _, _ => ()
  | none, _, some _, _, _ => ()
  | some _, _, none, _, _ => ()
  | some _, none, some _, _, _ => false
  | some _, some _, some _, a, b => a && b

/-- Monoid composition on `Option ℕ` (`Obj endo1`) used inside `apex` (`none` = strict unit). -/
def apexEndoMul : Option ℕ → Option ℕ → Option ℕ
  | none, b => b
  | a, none => a
  | some d, some _ => some d

/-- Identity `1`-morphism in `apex`. -/
def apexId : ∀ b : Bool, omegaObj (apexHom b b)
  | false => ()
  | true => none

/-- Composition of `1`-morphisms in `apex`: `compMor (d : true → false) apexArrow = some d`. -/
def apexComp : ∀ {x y z : Bool},
    omegaObj (apexHom x y) → omegaObj (apexHom y z) → omegaObj (apexHom x z)
  | false, _, false, _, _ => ()
  | false, _, true, _, _ => ()
  | true, false, false, d, _ => d
  | true, true, false, _, d => d
  | true, false, true, d, _ => some d
  | true, true, true, a, b => apexEndoMul a b

/-- Unified identity `1`-morphism `omegaId` across `OmegaTowerState`. -/
def omegaId : ∀ {s : OmegaTowerState} (x : omegaObj s), omegaObj (omegaHom x x)
  | .pt, () => ()
  | .empty, x => Empty.elim x
  | .natDisc, m => natDiscId m
  | .boolDisc, b => boolDiscId b
  | .chain d, b => chainId d b
  | .endo1, u => endoId u
  | .apex, b => apexId b

/-- Unified `1`-morphism composition `omegaComp` across `OmegaTowerState`. -/
def omegaComp : ∀ {s : OmegaTowerState} {x y z : omegaObj s},
    omegaObj (omegaHom x y) → omegaObj (omegaHom y z) → omegaObj (omegaHom x z)
  | .pt, _, _, _, _, _ => ()
  | .empty, x, _, _, _, _ => Empty.elim x
  | .natDisc, _, _, _, f, g => natDiscComp f g
  | .boolDisc, _, _, _, f, g => boolDiscComp f g
  | .chain d, _, _, _, f, g => chainComp d f g
  | .endo1, _, _, _, f, g => endoComp f g
  | .apex, _, _, _, f, g => apexComp f g

instance instGlobularInfSystem : GlobularInfSystem OmegaTowerState where
  Obj := omegaObj
  hom := omegaHom
  idMor := omegaId
  compMor := omegaComp
  id_comp_id {s} x := by
    cases s with
    | pt => rfl
    | empty => exact Empty.elim x
    | natDisc => exact (instSubsingletonNatDiscHom x x).elim _ _
    | boolDisc => cases x <;> rfl
    | chain d => cases d <;> cases x <;> rfl
    | endo1 => cases x <;> rfl
    | apex => cases x <;> rfl

/-- Exact ordinal rank assigned to each state in `OmegaTowerState`:
`0` on `pt`/`empty`/`natDisc`/`boolDisc`, `d + 1` on `chain d`, `ω` on `endo1`, and `ω + 1` on
`apex`. -/
def omegaRank : OmegaTowerState → Ordinal.{0}
  | .pt => 0
  | .empty => 0
  | .natDisc => 0
  | .boolDisc => 0
  | .chain d => ((d + 1 : ℕ) : Ordinal.{0})
  | .endo1 => Ordinal.omega0
  | .apex => Ordinal.omega0 + 1

instance instRankedInfCat : RankedInfCat OmegaTowerState where
  rank := omegaRank
  rank_zero_equiv {s} hs {x y} f := by
    cases s with
    | pt =>
      cases x
      cases y
      cases f
      exact IsEquiv.id (s := OmegaTowerState.pt) ()
    | empty => exact Empty.elim x
    | natDisc =>
      by_cases hxy : x = y
      · subst hxy
        rw [(instSubsingletonNatDiscHom x x).elim f (natDiscId x)]
        exact IsEquiv.id (s := OmegaTowerState.natDisc) x
      · exact Empty.elim (cast (congrArg omegaObj (if_neg hxy)) f)
    | boolDisc =>
      cases x <;> cases y
      · cases f
        exact IsEquiv.id (s := OmegaTowerState.boolDisc) false
      · exact Empty.elim f
      · exact Empty.elim f
      · cases f
        exact IsEquiv.id (s := OmegaTowerState.boolDisc) true
    | chain d =>
      have hpos : (0 : Ordinal.{0}) < ((d + 1 : ℕ) : Ordinal.{0}) := by
        rw [← Nat.cast_zero]
        exact Nat.cast_lt.mpr (Nat.succ_pos d)
      exact False.elim (hpos.ne' hs)
    | endo1 =>
      exact False.elim (Ordinal.omega0_ne_zero hs)
    | apex =>
      have hpos : (0 : Ordinal.{0}) < Ordinal.omega0 + 1 := by
        rw [Ordinal.add_one_eq_succ]
        exact lt_trans Ordinal.omega0_pos (Order.lt_succ Ordinal.omega0)
      exact False.elim (hpos.ne' hs)
  rank_hom_zero {s} hs x y := by
    cases s with
    | pt => rfl
    | empty => exact Empty.elim x
    | natDisc =>
      change omegaRank (natDiscHom x y) = 0
      by_cases hxy : (x : ℕ) = (y : ℕ)
      · rw [natDiscHom, if_pos hxy]
        rfl
      · rw [natDiscHom, if_neg hxy]
        rfl
    | boolDisc =>
      cases x <;> cases y <;> rfl
    | chain d =>
      have hpos : (0 : Ordinal.{0}) < ((d + 1 : ℕ) : Ordinal.{0}) := by
        rw [← Nat.cast_zero]
        exact Nat.cast_lt.mpr (Nat.succ_pos d)
      exact False.elim (hpos.ne' hs)
    | endo1 =>
      exact False.elim (Ordinal.omega0_ne_zero hs)
    | apex =>
      have hpos : (0 : Ordinal.{0}) < Ordinal.omega0 + 1 := by
        rw [Ordinal.add_one_eq_succ]
        exact lt_trans Ordinal.omega0_pos (Order.lt_succ Ordinal.omega0)
      exact False.elim (hpos.ne' hs)
  rank_hom_lt {s} hpos x y := by
    have h1_pos : (0 : Ordinal.{0}) < ((1 : ℕ) : Ordinal.{0}) := by
      rw [← Nat.cast_zero]
      exact Nat.cast_lt.mpr Nat.one_pos
    cases s with
    | pt => exact False.elim (lt_irrefl 0 hpos)
    | empty => exact Empty.elim x
    | natDisc => exact False.elim (lt_irrefl 0 hpos)
    | boolDisc => exact False.elim (lt_irrefl 0 hpos)
    | chain d =>
      cases d with
      | zero =>
        cases x <;> cases y <;> exact h1_pos
      | succ k =>
        have hk_pos : (0 : Ordinal.{0}) < ((k + 2 : ℕ) : Ordinal.{0}) := by
          rw [← Nat.cast_zero]
          exact Nat.cast_lt.mpr (Nat.succ_pos _)
        cases x <;> cases y
        · exact hk_pos
        · exact hk_pos
        · exact hk_pos
        · exact Nat.cast_lt.mpr (Nat.lt_succ_self (k + 1))
    | endo1 =>
      cases x <;> cases y
      · exact Ordinal.omega0_pos
      · exact Ordinal.omega0_pos
      · exact Ordinal.omega0_pos
      · exact Ordinal.nat_lt_omega0 _
    | apex =>
      have h0_lt : (0 : Ordinal.{0}) < Ordinal.omega0 + 1 := by
        rw [Ordinal.add_one_eq_succ]
        exact lt_trans Ordinal.omega0_pos (Order.lt_succ Ordinal.omega0)
      cases x <;> cases y
      · exact h0_lt
      · exact h0_lt
      · exact h0_lt
      · change Ordinal.omega0 < Ordinal.omega0 + 1
        rw [Ordinal.add_one_eq_succ]
        exact Order.lt_succ Ordinal.omega0

end OmegaTowerState

/-- Generating forward `1`-arrow `chainArrow d : false → true` inside `OmegaTowerState.chain d`. -/
def chainArrow (d : ℕ) :
    Obj (hom (s := OmegaTowerState.chain d) (false : Bool) (true : Bool)) :=
  match d with
  | 0 => ()
  | _ + 1 => ()

/-- Uniqueness of `1`-arrows `false → true` in `OmegaTowerState.chain d`. -/
theorem eq_chainArrow (d : ℕ)
    (u : Obj (hom (s := OmegaTowerState.chain d) (false : Bool) (true : Bool))) :
    u = chainArrow d := by
  cases d <;> cases u <;> rfl

/-- Exact lower bound on `chainArrow d`: `IsOrdinalInv d (chainArrow d)` holds for all `d : ℕ`. -/
theorem chainArrow_isOrdinalInv (d : ℕ) :
    IsOrdinalInv (d : Ordinal.{0}) (chainArrow d) := by
  induction d with
  | zero =>
    rw [Nat.cast_zero]
    exact isOrdinalInv_zero_of_any (chainArrow 0)
  | succ k ih =>
    rw [Nat.cast_succ, isOrdinalInv_add_one]
    refine ⟨(() : Unit), idMor (s := OmegaTowerState.pt) (), chainArrow k, ?_, ih⟩
    exact isOrdinalInv_id (s := OmegaTowerState.pt) (k : Ordinal.{0}) ()

/-- Exact upper bound on `chainArrow d`: `¬ IsOrdinalInv (d + 1) (chainArrow d)` for all `d : ℕ`.
-/
theorem chainArrow_not_isOrdinalInv_succ (d : ℕ) :
    ¬ IsOrdinalInv ((d + 1 : ℕ) : Ordinal.{0}) (chainArrow d) := by
  induction d with
  | zero =>
    rw [Nat.cast_succ, Nat.cast_zero, zero_add]
    have h1 : (1 : Ordinal.{0}) = (0 : Ordinal.{0}) + 1 := (zero_add 1).symm
    rw [h1, isOrdinalInv_add_one]
    rintro ⟨g, _, _, _, _⟩
    exact Empty.elim g
  | succ k ih =>
    rw [Nat.cast_succ (k + 1), isOrdinalInv_add_one]
    rintro ⟨_, _, ε, _, hε⟩
    rw [eq_chainArrow k ε] at hε
    exact ih hε

/-- No `chainArrow d` (`d : ℕ`) is an inductive equivalence (`¬ IsEquiv (chainArrow d)`). -/
theorem chainArrow_not_isEquiv (d : ℕ) :
    ¬ IsEquiv (chainArrow d) := fun hf ↦
  chainArrow_not_isOrdinalInv_succ d (hf.isOrdinalInv ((d + 1 : ℕ) : Ordinal.{0}))

/-- Split-idempotent `2`-retract witness in `OmegaTowerState.chain 1` (`rank = 2`):
`chainArrow 1 : false → true` and `v₁ = () : true → false` split the non-trivial idempotent
`e = false : true → true` (`compMor e e = e`) with `compMor (chainArrow 1) v₁ = idMor false` and
directed `2`-cell counit `chainArrow 0 : e ⇒ idMor true`, satisfying `IsOrdinalInv 1` while
failing `IsOrdinalInv 2` and `IsEquiv`. -/
theorem chainOne_split_retract_properties :
    let u₁ : Obj (hom (s := OmegaTowerState.chain 1) (false : Bool) (true : Bool)) := chainArrow 1
    let v₁ : Obj (hom (s := OmegaTowerState.chain 1) (true : Bool) (false : Bool)) := ()
    let e : Obj (hom (s := OmegaTowerState.chain 1) (true : Bool) (true : Bool)) := false
    compMor u₁ v₁ = idMor (s := OmegaTowerState.chain 1) (false : Bool) ∧
      compMor v₁ u₁ = e ∧
      compMor e e = e ∧
      e ≠ idMor (s := OmegaTowerState.chain 1) (true : Bool) ∧
      IsOrdinalInv 1 u₁ ∧
      ¬ IsOrdinalInv 2 u₁ ∧
      ¬ IsEquiv u₁ := by
  refine ⟨rfl, rfl, rfl, Bool.false_ne_true, ?_, ?_, chainArrow_not_isEquiv 1⟩
  · simpa using chainArrow_isOrdinalInv 1
  · simpa using chainArrow_not_isOrdinalInv_succ 1

/-- Directed counit `1`-morphism `endoCounit d : some d → none` inside `OmegaTowerState.endo1`. -/
def endoCounit (d : ℕ) :
    Obj (hom (s := OmegaTowerState.endo1) (some d) (none : Option ℕ)) :=
  ()

/-- Exact lower bound on `endoCounit d`: `IsOrdinalInv (d + 1) (endoCounit d)` holds. -/
theorem endoCounit_isOrdinalInv (d : ℕ) :
    IsOrdinalInv ((d + 1 : ℕ) : Ordinal.{0}) (endoCounit d) := by
  rw [Nat.cast_succ, isOrdinalInv_add_one]
  refine ⟨(() : Unit), chainArrow d, idMor (s := OmegaTowerState.pt) (),
    chainArrow_isOrdinalInv d, ?_⟩
  exact isOrdinalInv_id (s := OmegaTowerState.pt) (d : Ordinal.{0}) ()

/-- Exact upper bound on `endoCounit d`: `¬ IsOrdinalInv (d + 2) (endoCounit d)`. -/
theorem endoCounit_not_isOrdinalInv_succ (d : ℕ) :
    ¬ IsOrdinalInv ((d + 2 : ℕ) : Ordinal.{0}) (endoCounit d) := by
  rw [Nat.cast_succ (d + 1), isOrdinalInv_add_one]
  rintro ⟨_, η, _, hη, _⟩
  rw [eq_chainArrow d η] at hη
  exact chainArrow_not_isOrdinalInv_succ d hη

/-- On `OmegaTowerState.endo1` (`rank = ω`), Theorem 9A still guarantees `IsOmegaInv ↔ IsEquiv`. -/
theorem endo1_omegaInv_iff_isEquiv {x y : Obj OmegaTowerState.endo1}
    {f : Obj (hom x y)} :
    IsOmegaInv f ↔ IsEquiv f :=
  theorem9A_omega_completeness (s := OmegaTowerState.endo1) le_rfl

/-- Forward retract `1`-arrow `apexArrow : false → true` inside the rank-`(ω + 1)` state
`OmegaTowerState.apex`. -/
def apexArrow :
    Obj (hom (s := OmegaTowerState.apex) (false : Bool) (true : Bool)) :=
  ()

/-- **Sharpness Witness Part 1 (`apexArrow_isOmegaInv`):**
In `OmegaTowerState.apex` (`rank = ω + 1`), `apexArrow` is `n`-invertible for every `n : ℕ`
(`IsOmegaInv apexArrow`). -/
theorem apexArrow_isOmegaInv : IsOmegaInv apexArrow := by
  intro n
  have hsucc : IsOrdinalInv ((n + 1 : ℕ) : Ordinal.{0}) apexArrow := by
    rw [Nat.cast_succ, isOrdinalInv_add_one]
    refine ⟨(n : ℕ), idMor (s := OmegaTowerState.pt) (), endoCounit n,
      isOrdinalInv_id (s := OmegaTowerState.pt) (n : Ordinal.{0}) (), ?_⟩
    exact isOrdinalInv_anti (Nat.cast_le.mpr (Nat.le_succ n)) (endoCounit_isOrdinalInv n)
  exact isOrdinalInv_anti (Nat.cast_le.mpr (Nat.le_succ n)) hsucc

/-- **Sharpness Witness Part 2 (`apexArrow_not_isOrdinalInv_omega0_add_one`):**
`apexArrow` fails `(ω + 1)`-invertibility (`¬ IsOrdinalInv (Ordinal.omega0 + 1) apexArrow`). -/
theorem apexArrow_not_isOrdinalInv_omega0_add_one :
    ¬ IsOrdinalInv (Ordinal.omega0 + 1) apexArrow := by
  rw [isOrdinalInv_add_one]
  rintro ⟨d, _, ε, _, hε⟩
  let d' : ℕ := d
  have hε_eq : ε = endoCounit d' := rfl
  rw [hε_eq] at hε
  have hfin : IsOrdinalInv ((d' + 2 : ℕ) : Ordinal.{0}) (endoCounit d') :=
    isOrdinalInv_anti (le_of_lt (Ordinal.nat_lt_omega0 (d' + 2))) hε
  exact endoCounit_not_isOrdinalInv_succ d' hfin

/-- **Sharpness Witness Part 3 (`apexArrow_not_isEquiv`):**
`apexArrow` is **not** an inductive equivalence (`¬ IsEquiv apexArrow`), proving exact sharpness of
Theorem 9A's `rank s ≤ ω` hypothesis at `rank apex = ω + 1`. -/
theorem apexArrow_not_isEquiv : ¬ IsEquiv apexArrow := fun hf ↦
  apexArrow_not_isOrdinalInv_omega0_add_one (hf.isOrdinalInv (Ordinal.omega0 + 1))

/-- **Sharpness Witness Part 4 (`apexArrow_not_isCoindEquiv`):**
Because `OmegaTowerState` is a `RankedInfCat`, Proposition 1A (`ranked_coindEquiv_iff_isEquiv`)
forces `¬ IsCoindEquiv apexArrow` even though `IsOmegaInv apexArrow` holds. -/
theorem apexArrow_not_isCoindEquiv : ¬ IsCoindEquiv apexArrow := fun hf ↦
  apexArrow_not_isEquiv (ranked_coindEquiv_iff_isEquiv.mp hf)

/-- Two-state unranked globular system `CoindWalkState` modeling the gaunt walking coinductive
equivalence `E_coind` (`arXiv:2603.11005v2` Def. 5.14; `arXiv:2608.28355` Prop. 2.15), separating
`IsCoindEquiv` from `IsEquiv` outside `RankedInfCat`. -/
inductive CoindWalkState : Type
  | pt : CoindWalkState
  | loop : CoindWalkState
  deriving DecidableEq, Repr

namespace CoindWalkState

/-- Underlying `0`-cell type of `CoindWalkState`. -/
def walkObj : CoindWalkState → Type
  | .pt => Unit
  | .loop => Bool

/-- Hom-state transition of `CoindWalkState`: endomorphism states of `false` and `true` in `loop`
re-enter `loop` self-similarly. -/
def walkHom : ∀ {s : CoindWalkState}, walkObj s → walkObj s → CoindWalkState
  | .pt, _, _ => .pt
  | .loop, false, false => .loop
  | .loop, true, true => .loop
  | .loop, false, true => .pt
  | .loop, true, false => .pt

/-- Identity `1`-morphism in `CoindWalkState`. -/
def walkId : ∀ {s : CoindWalkState} (x : walkObj s), walkObj (walkHom x x)
  | .pt, () => ()
  | .loop, false => true
  | .loop, true => true

/-- Composition in `CoindWalkState`: reversing `false → true → false` or `true → false → true`
lands on `false ≠ idMor` inside `loop`, requiring an infinite coinductive tower of witnesses. -/
def walkComp : ∀ {s : CoindWalkState} {x y z : walkObj s},
    walkObj (walkHom x y) → walkObj (walkHom y z) → walkObj (walkHom x z)
  | .pt, _, _, _, _, _ => ()
  | .loop, false, false, false, a, b => a && b
  | .loop, true, true, true, a, b => a && b
  | .loop, false, true, false, _, _ => false
  | .loop, true, false, true, _, _ => false
  | .loop, false, _, true, _, _ => ()
  | .loop, true, _, false, _, _ => ()

instance instGlobularInfSystem : GlobularInfSystem CoindWalkState where
  Obj := walkObj
  hom := walkHom
  idMor := walkId
  compMor := walkComp
  id_comp_id {s} x := by
    cases s with
    | pt => rfl
    | loop => cases x <;> rfl

end CoindWalkState

/-- Tautological coinductive `1`-arrow `coindArrow : false → true` in `CoindWalkState.loop`. -/
def coindArrow :
    Obj (hom (s := CoindWalkState.loop) (false : Bool) (true : Bool)) :=
  ()

/-- Predicate selecting the forward pair `(false, true)` inside `CoindWalkState.loop`. -/
def isCoindForward : ∀ {t : CoindWalkState}, Obj t → Obj t → Prop
  | .pt, _, _ => False
  | .loop, u, w => u = false ∧ w = true

/-- `coindArrow` is a genuine coinductive equivalence (`IsCoindEquiv coindArrow`). -/
theorem coindArrow_isCoindEquiv : IsCoindEquiv coindArrow := by
  refine ⟨fun {t u w} _ ↦ isCoindForward (t := t) u w, ⟨rfl, rfl⟩, ?_⟩
  intro t u w _ hh
  cases t with
  | pt => exact False.elim hh
  | loop =>
    rcases hh with ⟨rfl, rfl⟩
    exact ⟨(() : Unit), (() : Unit), (() : Unit), ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- `coindArrow` is **not** an inductive equivalence (`¬ IsEquiv coindArrow`). -/
theorem coindArrow_not_isEquiv : ¬ IsEquiv coindArrow := by
  have hinv : ∀ {t : CoindWalkState} {u w : Obj t} (f : Obj (hom u w)),
      IsEquiv f → ¬ isCoindForward (t := t) u w := by
    intro t u w f hf
    induction hf with
    | @id s _ =>
      cases s with
      | pt => exact id
      | loop =>
        rintro ⟨rfl, htf⟩
        exact Bool.false_ne_true htf
    | @mk s _ _ _ _ _ _ _ _ ihη =>
      cases s with
      | pt => exact id
      | loop =>
        rintro ⟨rfl, rfl⟩
        exact ihη ⟨rfl, rfl⟩
  exact fun hf ↦ hinv coindArrow hf ⟨rfl, rfl⟩

/-! ## Section 4: Proposition 11A — Inductive Lali Split-Idempotent Ceiling `max K_x K_y + 2` -/

/-- A coalgebraic globular functor/simulation between `GlobularInfSystem` state spaces `S₁` and
`S₂`, witnessed by `Rel : S₁ → S₂ → Type (max u₁ u₂)` acting on `0`-cells and inductively on all
higher `hom`-states with zero transport casts. -/
structure GlobularSimulation (S₁ : Type u₁) (S₂ : Type u₂)
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] where
  /-- State correspondence witness type relating `s₁ : S₁` to `s₂ : S₂`. -/
  Rel : S₁ → S₂ → Type (max u₁ u₂)
  /-- Action on `0`-cells `Obj s₁ → Obj s₂`. -/
  mapObj : ∀ {s₁ : S₁} {s₂ : S₂}, Rel s₁ s₂ → Obj s₁ → Obj s₂
  /-- Recursive transition on `1`-morphism hom-states. -/
  mapHom : ∀ {s₁ : S₁} {s₂ : S₂} (φ : Rel s₁ s₂) (x y : Obj s₁),
    Rel (hom x y) (hom (mapObj φ x) (mapObj φ y))

/-- Equality-indexed state correspondence in `Type u` for `GlobularSimulation.id`. -/
inductive EqStateRel {S : Type u} : S → S → Type u
  | refl (s : S) : EqStateRel s s

/-- Identity `GlobularSimulation` on `S`. -/
def GlobularSimulation.id (S : Type u) [GlobularInfSystem S] :
    GlobularSimulation S S where
  Rel := EqStateRel
  mapObj := fun {_ _} φ x ↦
    match φ with
    | .refl _ => x
  mapHom := fun {_ _} φ x y ↦
    match φ with
    | .refl _ => .refl (hom x y)

/-- Composition `G.comp F` (`G ∘ F`) of two `GlobularSimulation`s on the same universe level. -/
abbrev GlobularSimulation.comp {S₁ S₂ S₃ : Type u}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] [GlobularInfSystem S₃]
    (G : GlobularSimulation S₂ S₃) (F : GlobularSimulation S₁ S₂) :
    GlobularSimulation S₁ S₃ where
  Rel s₁ s₃ := Σ s₂ : S₂, F.Rel s₁ s₂ × G.Rel s₂ s₃
  mapObj := fun {_ _} ⟨_, φF, φG⟩ x ↦ G.mapObj φG (F.mapObj φF x)
  mapHom := fun {_ _} ⟨_, φF, φG⟩ x y ↦
    ⟨hom (F.mapObj φF x) (F.mapObj φF y), F.mapHom φF x y,
      G.mapHom φG (F.mapObj φF x) (F.mapObj φF y)⟩

/-- A Lali (*left-adjoint-left-inverse*) split-idempotent retraction `l : aState ⇄ dState : r`
inside a `GlobularInfSystem S`, splitting the idempotent globular endofunctor `E = L ∘ R` on
`dState` with a directed counit `1`-morphism `counit x : E(x) → x` that is an inductive equivalence
on the retract image `L(u)`. -/
structure LaliRetraction {S : Type u} [GlobularInfSystem S] (aState dState : S) where
  /-- Left inclusion simulation `l : aState → dState`. -/
  L : GlobularSimulation S S
  /-- Right retraction simulation `r : dState → aState`. -/
  R : GlobularSimulation S S
  /-- State witness for `l : aState → dState`. -/
  relL : L.Rel aState dState
  /-- State witness for `r : dState → aState`. -/
  relR : R.Rel dState aState
  /-- Strict split-retraction law `r (l u) = u` on `0`-cells of `aState`. -/
  retract_left_inv : ∀ u : Obj aState, R.mapObj relR (L.mapObj relL u) = u
  /-- Directed Lali counit `1`-cell `ε_x : E(x) → x` (`E = l ∘ r`). -/
  counit : ∀ x : Obj dState, Obj (hom (L.mapObj relL (R.mapObj relR x)) x)
  /-- Lali unit/triangle invertibility: `counit (L u)` is an inductive equivalence on `L(u)`. -/
  counit_left_isEquiv : ∀ u : Obj aState,
    IsEquiv (retract_left_inv u ▸ counit (L.mapObj relL u))

namespace LaliRetraction

/-- Composite split-idempotent globular endofunctor `E := L.comp R` associated to `lali`. -/
abbrev endoSim {S : Type u} [GlobularInfSystem S] {aState dState : S}
    (lali : LaliRetraction aState dState) : GlobularSimulation S S :=
  lali.L.comp lali.R

/-- Canonical state witness `endoRel : lali.endoSim.Rel dState dState` for `E = L ∘ R`. -/
abbrev endoRel {S : Type u} [GlobularInfSystem S] {aState dState : S}
    (lali : LaliRetraction aState dState) : lali.endoSim.Rel dState dState :=
  ⟨aState, lali.relR, lali.relL⟩

/-- Action `E(x) = L(R(x))` of the split-idempotent endofunctor on `0`-cells of `dState`. -/
abbrev endoObj {S : Type u} [GlobularInfSystem S] {aState dState : S}
    (lali : LaliRetraction aState dState) (x : Obj dState) : Obj dState :=
  lali.endoSim.mapObj lali.endoRel x

/-- Strict idempotence `E(E(x)) = E(x)` on `0`-cells of `dState`. -/
@[simp]
theorem endoObj_idem {S : Type u} [GlobularInfSystem S] {aState dState : S}
    (lali : LaliRetraction aState dState) (x : Obj dState) :
    lali.endoObj (lali.endoObj x) = lali.endoObj x :=
  congrArg (lali.L.mapObj lali.relL) (lali.retract_left_inv (lali.R.mapObj lali.relR x))

end LaliRetraction

/-- Grounded higher cell boundaries `HomBoundary r t` at relative depth `r : ℕ` inside `t : S`.
Over `t = hom x y` (`x, y : Obj s`), `B : HomBoundary r (hom x y)` specifies parallel ambient
`(r + 1)`-cells `(Φ, Ψ)` grounded over `(x, y)` whose ambient `(r + 2)`-cells have type
`Obj (hom (homBoundarySrc B) (homBoundaryTgt B))`. -/
def HomBoundary {S : Type u} [GlobularInfSystem S] : ℕ → S → Type u
  | 0, t => Obj t × Obj t
  | r + 1, t => Σ p : Obj t × Obj t, HomBoundary r (hom p.1 p.2)

/-- Parent state hosting the tip boundary pair `(Φ, Ψ)` of `B : HomBoundary r t`. -/
def homBoundaryParent {S : Type u} [GlobularInfSystem S] :
    ∀ {r : ℕ} {t : S}, HomBoundary r t → S
  | 0, t, _ => t
  | _ + 1, _, ⟨p, B'⟩ => homBoundaryParent (t := hom p.1 p.2) B'

/-- Tip source cell `Φ : Obj (homBoundaryParent B)` of `B : HomBoundary r t`. -/
def homBoundarySrc {S : Type u} [GlobularInfSystem S] :
    ∀ {r : ℕ} {t : S} (B : HomBoundary r t), Obj (homBoundaryParent B)
  | 0, _, p => p.1
  | _ + 1, _, ⟨_, B'⟩ => homBoundarySrc B'

/-- Tip target cell `Ψ : Obj (homBoundaryParent B)` of `B : HomBoundary r t`. -/
def homBoundaryTgt {S : Type u} [GlobularInfSystem S] :
    ∀ {r : ℕ} {t : S} (B : HomBoundary r t), Obj (homBoundaryParent B)
  | 0, _, p => p.2
  | _ + 1, _, ⟨_, B'⟩ => homBoundaryTgt B'

/-- Action of `F : GlobularSimulation S₁ S₂` on grounded boundaries `HomBoundary r t₁`. -/
def mapHomBoundary {S₁ : Type u₁} {S₂ : Type u₂}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] (F : GlobularSimulation S₁ S₂) :
    ∀ {r : ℕ} {t₁ : S₁} {t₂ : S₂}, F.Rel t₁ t₂ → HomBoundary r t₁ → HomBoundary r t₂
  | 0, _, _, φ, (a, b) => (F.mapObj φ a, F.mapObj φ b)
  | _ + 1, _, _, φ, ⟨(a, b), B'⟩ =>
    ⟨(F.mapObj φ a, F.mapObj φ b), mapHomBoundary F (F.mapHom φ a b) B'⟩

/-- Cast-free action of `F : GlobularSimulation S₁ S₂` on higher cells bounded by
`B : HomBoundary r t₁` (ambient dimension `m = r + 2` when `t₁ = hom x y`). -/
def mapHomCell {S₁ : Type u₁} {S₂ : Type u₂}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] (F : GlobularSimulation S₁ S₂) :
    ∀ {r : ℕ} {t₁ : S₁} {t₂ : S₂} (φ : F.Rel t₁ t₂) (B : HomBoundary r t₁),
      Obj (hom (homBoundarySrc B) (homBoundaryTgt B)) →
        Obj (hom (homBoundarySrc (mapHomBoundary F φ B))
          (homBoundaryTgt (mapHomBoundary F φ B)))
  | 0, _, _, φ, (a, b), α => F.mapObj (F.mapHom φ a b) α
  | _ + 1, _, _, φ, ⟨(a, b), B'⟩, α => mapHomCell F (F.mapHom φ a b) B' α

/-- Coinductive contractibility (`≃ *`) of a state `t : S`: `Obj` is `Nonempty` and `Subsingleton`
at `t` and across all iterated `hom`-states. -/
def IsContractibleState {S : Type u} [GlobularInfSystem S] (t : S) : Prop :=
  ∃ P : S → Prop, P t ∧
    ∀ {q : S}, P q → Nonempty (Obj q) ∧ Subsingleton (Obj q) ∧ ∀ a b : Obj q, P (hom a b)

/-- Every `IsContractibleState t` has `Nonempty (Obj t)`. -/
theorem IsContractibleState.nonempty_obj {S : Type u} [GlobularInfSystem S] {t : S}
    (ht : IsContractibleState t) : Nonempty (Obj t) := by
  rcases ht with ⟨P, hPt, hstep⟩
  exact (hstep hPt).1

/-- Every `IsContractibleState t` has `Subsingleton (Obj t)`. -/
theorem IsContractibleState.subsingleton_obj {S : Type u} [GlobularInfSystem S] {t : S}
    (ht : IsContractibleState t) : Subsingleton (Obj t) := by
  rcases ht with ⟨P, hPt, hstep⟩
  exact (hstep hPt).2.1

/-- Contractibility is preserved under `hom a b`. -/
theorem IsContractibleState.hom_state {S : Type u} [GlobularInfSystem S] {t : S}
    (ht : IsContractibleState t) (a b : Obj t) : IsContractibleState (hom a b) := by
  rcases ht with ⟨P, hPt, hstep⟩
  exact ⟨P, (hstep hPt).2.2 a b, hstep⟩

/-- A state `t : S` is `(-1)`-truncated (`∈ {∅, *}`) if `Obj t` is `Subsingleton` and all of its
`hom`-states are contractible (`IsContractibleState`). -/
def IsMinusOneTruncated {S : Type u} [GlobularInfSystem S] (t : S) : Prop :=
  Subsingleton (Obj t) ∧ ∀ a b : Obj t, IsContractibleState (hom a b)

/-- Every contractible state is `(-1)`-truncated. -/
theorem IsContractibleState.isMinusOneTruncated {S : Type u} [GlobularInfSystem S] {t : S}
    (ht : IsContractibleState t) : IsMinusOneTruncated t :=
  ⟨ht.subsingleton_obj, ht.hom_state⟩

/-- In any `IsMinusOneTruncated q`, every `1`-morphism `α : Obj (hom u w)` is an inductive
equivalence (`IsEquiv α`). -/
theorem IsMinusOneTruncated.isEquiv_mor {S : Type u} [GlobularInfSystem S] {q : S}
    (hq : IsMinusOneTruncated q) {u w : Obj q} (α : Obj (hom u w)) :
    IsEquiv α := by
  obtain rfl : u = w := hq.1.elim u w
  rw [(hq.2 u u).subsingleton_obj.elim α (idMor u)]
  exact IsEquiv.id u

/-- For any `IsContractibleState q` and `B : HomBoundary r q`, `homBoundaryParent B` remains
`IsContractibleState`. -/
theorem IsContractibleState.homBoundaryParent_contractible {S : Type u} [GlobularInfSystem S] :
    ∀ {r : ℕ} {q : S}, IsContractibleState q → ∀ (B : HomBoundary r q),
      IsContractibleState (homBoundaryParent B)
  | 0, _, hq, _ => hq
  | _ + 1, _, hq, ⟨(a, b), B'⟩ => (hq.hom_state a b).homBoundaryParent_contractible B'

/-- For any `IsMinusOneTruncated q` and `B : HomBoundary r q`, `homBoundaryParent B` is
`IsMinusOneTruncated`. -/
theorem IsMinusOneTruncated.homBoundaryParent_minusOne {S : Type u} [GlobularInfSystem S] :
    ∀ {r : ℕ} {q : S}, IsMinusOneTruncated q → ∀ (B : HomBoundary r q),
      IsMinusOneTruncated (homBoundaryParent B)
  | 0, _, hq, _ => hq
  | _ + 1, _, hq, ⟨(a, b), B'⟩ =>
    ((hq.2 a b).homBoundaryParent_contractible B').isMinusOneTruncated

/-- Local hom cell-stabilization height `K : ℕ` (`(K, K)`-truncation) of a hom-state `t : S`:
at `K = 0`, all `1`-morphism hom-states `hom a b` of `t` are `(-1)`-truncated (`∈ {∅, *}`);
at `K + 1`, all `1`-morphism hom-states `hom a b` of `t` have cell height `K`. -/
def HasHomCellHeight {S : Type u} [GlobularInfSystem S] : ℕ → S → Prop
  | 0, t => ∀ a b : Obj t, IsMinusOneTruncated (hom a b)
  | K + 1, t => ∀ a b : Obj t, HasHomCellHeight K (hom a b)

/-- Any `(-1)`-truncated state already has `HasHomCellHeight 0`. -/
theorem IsMinusOneTruncated.hasHomCellHeight_zero {S : Type u} [GlobularInfSystem S] {t : S}
    (ht : IsMinusOneTruncated t) : HasHomCellHeight 0 t :=
  fun a b ↦ (ht.2 a b).isMinusOneTruncated

/-- Upward monotonicity of `HasHomCellHeight K t` in the height bound `K : ℕ`. -/
theorem HasHomCellHeight.mono {S : Type u} [GlobularInfSystem S] :
    ∀ {K₁ K₂ : ℕ} (_ : K₁ ≤ K₂) {t : S}, HasHomCellHeight K₁ t → HasHomCellHeight K₂ t
  | 0, 0, _, _, ht => ht
  | 0, _ + 1, _, _, ht => fun a b ↦
    HasHomCellHeight.mono (Nat.zero_le _) (ht a b).hasHomCellHeight_zero
  | _ + 1, 0, hle, _, _ => False.elim (Nat.not_succ_le_zero _ hle)
  | _ + 1, _ + 1, hle, _, ht => fun a b ↦
    HasHomCellHeight.mono (Nat.le_of_succ_le_succ hle) (ht a b)

/-- Core inductive lemma for Proposition 11A: if `HasHomCellHeight K t` holds and `K ≤ r`, then for
every `B : HomBoundary (r + 1) t` (ambient dimension `m = r + 3 > K + 2` when `t = hom x y`),
`homBoundaryParent B` is `(-1)`-truncated. -/
theorem HasHomCellHeight.homBoundaryParent_minusOne_of_le {S : Type u} [GlobularInfSystem S] :
    ∀ {K r : ℕ} (_ : K ≤ r) {t : S}, HasHomCellHeight K t →
      ∀ (B : HomBoundary (r + 1) t), IsMinusOneTruncated (homBoundaryParent B)
  | 0, _, _, _, ht, ⟨(a, b), B'⟩ => (ht a b).homBoundaryParent_minusOne B'
  | _ + 1, 0, hle, _, _, _ => False.elim (Nat.not_succ_le_zero _ hle)
  | _ + 1, _ + 1, hle, _, ht, ⟨(a, b), B'⟩ =>
    HasHomCellHeight.homBoundaryParent_minusOne_of_le (Nat.le_of_succ_le_succ hle) (ht a b) B'

/-- Helper: any function between `Nonempty` and `Subsingleton` types is `Function.Bijective`. -/
private theorem bijective_of_contractible_types {α : Type u₁} {β : Type u₂}
    [Nonempty α] [Subsingleton α] [Nonempty β] [Subsingleton β] (f : α → β) :
    Function.Bijective f :=
  ⟨fun a₁ a₂ _ ↦ Subsingleton.elim a₁ a₂,
    fun b ↦ let ⟨a⟩ := ‹Nonempty α›; ⟨a, Subsingleton.elim (f a) b⟩⟩

/-- **Proposition 11A Part 1 — Inductive Lali Split-Idempotent Stabilization Above
`max K_x K_y + 2` (`prop11A_lali_stabilization_above_ceiling`):**
Let `lali : LaliRetraction aState dState` split `E = L ∘ R` on `dState : S`, and suppose
`x, y : Obj dState` satisfy `HasHomCellHeight K_x (hom x y)` and
`HasHomCellHeight K_y (hom (E x) (E y))`. For every ambient cell dimension `m > max K_x K_y + 2`
(indexed as `m = r + 3` with `max K_x K_y ≤ r`, i.e., `B : HomBoundary (r + 1) (hom x y)`):
1. Both ambient `m`-cell hom-states (`hom Φ Ψ` and `hom (E Φ) (E Ψ)`) satisfy `IsContractibleState`,
2. Every ambient `m`-cell `α : Obj (hom Φ Ψ)` and `β : Obj (hom (E Φ) (E Ψ))` satisfies `IsEquiv`,
3. The map `mapHomCell lali.endoSim _ B` induced by `E` on ambient `m`-cells is
   `Function.Bijective`.
-/
theorem prop11A_lali_stabilization_above_ceiling {S : Type u} [GlobularInfSystem S]
    {aState dState : S} (lali : LaliRetraction aState dState)
    {x y : Obj dState} {K_x K_y r : ℕ}
    (hKx : HasHomCellHeight K_x (hom x y))
    (hKy : HasHomCellHeight K_y (hom (lali.endoObj x) (lali.endoObj y)))
    (hr : max K_x K_y ≤ r)
    (B : HomBoundary (r + 1) (hom x y)) :
    let φxy := lali.endoSim.mapHom lali.endoRel x y
    let EB := mapHomBoundary lali.endoSim φxy B
    IsContractibleState (hom (homBoundarySrc B) (homBoundaryTgt B)) ∧
      IsContractibleState (hom (homBoundarySrc EB) (homBoundaryTgt EB)) ∧
      (∀ α : Obj (hom (homBoundarySrc B) (homBoundaryTgt B)), IsEquiv α) ∧
      (∀ β : Obj (hom (homBoundarySrc EB) (homBoundaryTgt EB)), IsEquiv β) ∧
      Function.Bijective (mapHomCell lali.endoSim φxy B) := by
  intro φxy EB
  have hpar₁ : IsMinusOneTruncated (homBoundaryParent B) :=
    hKx.homBoundaryParent_minusOne_of_le (le_trans (le_max_left K_x K_y) hr) B
  have hpar₂ : IsMinusOneTruncated (homBoundaryParent EB) :=
    hKy.homBoundaryParent_minusOne_of_le (le_trans (le_max_right K_x K_y) hr) EB
  have hc₁ : IsContractibleState (hom (homBoundarySrc B) (homBoundaryTgt B)) :=
    hpar₁.2 (homBoundarySrc B) (homBoundaryTgt B)
  have hc₂ : IsContractibleState (hom (homBoundarySrc EB) (homBoundaryTgt EB)) :=
    hpar₂.2 (homBoundarySrc EB) (homBoundaryTgt EB)
  haveI : Nonempty (Obj (hom (homBoundarySrc B) (homBoundaryTgt B))) := hc₁.nonempty_obj
  haveI : Subsingleton (Obj (hom (homBoundarySrc B) (homBoundaryTgt B))) := hc₁.subsingleton_obj
  haveI : Nonempty (Obj (hom (homBoundarySrc EB) (homBoundaryTgt EB))) := hc₂.nonempty_obj
  haveI : Subsingleton (Obj (hom (homBoundarySrc EB) (homBoundaryTgt EB))) := hc₂.subsingleton_obj
  exact ⟨hc₁, hc₂, hpar₁.isEquiv_mor, hpar₂.isEquiv_mor,
    bijective_of_contractible_types (mapHomCell lali.endoSim φxy B)⟩

/-- Explicit `Equiv` promotion of `mapHomCell lali.endoSim` on ambient `m`-cells above
`max K_x K_y + 2`. -/
noncomputable def prop11A_lali_cellEquiv_above_ceiling {S : Type u} [GlobularInfSystem S]
    {aState dState : S} (lali : LaliRetraction aState dState)
    {x y : Obj dState} {K_x K_y r : ℕ}
    (hKx : HasHomCellHeight K_x (hom x y))
    (hKy : HasHomCellHeight K_y (hom (lali.endoObj x) (lali.endoObj y)))
    (hr : max K_x K_y ≤ r)
    (B : HomBoundary (r + 1) (hom x y)) :
    let φxy := lali.endoSim.mapHom lali.endoRel x y
    let EB := mapHomBoundary lali.endoSim φxy B
    Obj (hom (homBoundarySrc B) (homBoundaryTgt B)) ≃
      Obj (hom (homBoundarySrc EB) (homBoundaryTgt EB)) :=
  Equiv.ofBijective _ (prop11A_lali_stabilization_above_ceiling lali hKx hKy hr B).2.2.2.2

/-- Globular state space `JoinSuspState` realizing the iterated `2`-point sphere suspensions
`suspSphere K = Σ^K(S⁰)` (`K ≥ 0`) and the join cones `joinCone K = {a} ⋆ Σ^{K+1}(S⁰)` witnessing
exact sharpness of Proposition 11A at `m = K + 2` for every `K : ℕ`. -/
inductive JoinSuspState : Type
  | pt : JoinSuspState
  | empty : JoinSuspState
  | suspSphere : ℕ → JoinSuspState
  | joinCone : ℕ → JoinSuspState
  deriving DecidableEq, Repr

namespace JoinSuspState

/-- Underlying `0`-cell type of `JoinSuspState`. -/
def joinObj : JoinSuspState → Type
  | .pt => Unit
  | .empty => Empty
  | .suspSphere _ => Bool
  | .joinCone _ => Option Bool

/-- Hom-state of `suspSphere K = Σ^K(S⁰)` (`false = -`, `true = +`): upper-triangular `2 × 2`
suspension matrix with off-diagonal `.empty` at `K = 0` (`S⁰`) and `.suspSphere k` at `K = k + 1`.
-/
def suspSphereHom (K : ℕ) : Bool → Bool → JoinSuspState
  | false, false => .pt
  | true, true => .pt
  | true, false => .empty
  | false, true =>
    match K with
    | 0 => .empty
    | k + 1 => .suspSphere k

/-- Hom-state of `joinCone K = {a} ⋆ Σ^{K+1}(S⁰)` (`none = a`, `some false = -`,
`some true = +`): `a` is an initial cone point (`hom a w = .pt`) and `{-, +}` has off-diagonal
`hom (-, +) = suspSphere K = Σ^K(S⁰)`. -/
def joinConeHom (K : ℕ) : Option Bool → Option Bool → JoinSuspState
  | none, _ => .pt
  | some _, none => .empty
  | some false, some false => .pt
  | some true, some true => .pt
  | some true, some false => .empty
  | some false, some true => .suspSphere K

/-- Unified hom-state transition on `JoinSuspState`. -/
def joinHom : ∀ {s : JoinSuspState}, joinObj s → joinObj s → JoinSuspState
  | .pt, _, _ => .pt
  | .empty, x, _ => Empty.elim x
  | .suspSphere K, b₁, b₂ => suspSphereHom K b₁ b₂
  | .joinCone K, u, w => joinConeHom K u w

/-- Identity `1`-morphism on `suspSphere K`. -/
def suspSphereId (K : ℕ) : ∀ b : Bool, joinObj (suspSphereHom K b b)
  | false => ()
  | true => ()

/-- Composition of `1`-morphisms on `suspSphere K`. -/
def suspSphereComp (K : ℕ) : ∀ {x y z : Bool},
    joinObj (suspSphereHom K x y) → joinObj (suspSphereHom K y z) → joinObj (suspSphereHom K x z)
  | false, false, false, _, _ => ()
  | true, true, true, _, _ => ()
  | true, false, _, f, _ => Empty.elim f
  | false, true, false, _, g => Empty.elim g
  | true, true, false, _, g => Empty.elim g
  | false, false, true, _, g => g
  | false, true, true, f, _ => f

/-- Identity `1`-morphism on `joinCone K`. -/
def joinConeId (K : ℕ) : ∀ u : Option Bool, joinObj (joinConeHom K u u)
  | none => ()
  | some false => ()
  | some true => ()

/-- Composition of `1`-morphisms on `joinCone K`. -/
def joinConeComp (K : ℕ) : ∀ {x y z : Option Bool},
    joinObj (joinConeHom K x y) → joinObj (joinConeHom K y z) → joinObj (joinConeHom K x z)
  | none, _, _, _, _ => ()
  | some _, none, _, f, _ => Empty.elim f
  | some _, some _, none, _, g => Empty.elim g
  | some false, some false, some false, _, _ => ()
  | some true, some true, some true, _, _ => ()
  | some true, some false, some _, f, _ => Empty.elim f
  | some false, some true, some false, _, g => Empty.elim g
  | some true, some true, some false, _, g => Empty.elim g
  | some false, some false, some true, _, g => g
  | some false, some true, some true, f, _ => f

/-- Unified identity `1`-morphism on `JoinSuspState`. -/
def joinId : ∀ {s : JoinSuspState} (x : joinObj s), joinObj (joinHom x x)
  | .pt, () => ()
  | .empty, x => Empty.elim x
  | .suspSphere K, b => suspSphereId K b
  | .joinCone K, u => joinConeId K u

/-- Unified composition of `1`-morphisms on `JoinSuspState`. -/
def joinComp : ∀ {s : JoinSuspState} {x y z : joinObj s},
    joinObj (joinHom x y) → joinObj (joinHom y z) → joinObj (joinHom x z)
  | .pt, _, _, _, _, _ => ()
  | .empty, x, _, _, _, _ => Empty.elim x
  | .suspSphere K, _, _, _, f, g => suspSphereComp K f g
  | .joinCone K, _, _, _, f, g => joinConeComp K f g

instance instGlobularInfSystem : GlobularInfSystem JoinSuspState where
  Obj := joinObj
  hom := joinHom
  idMor := joinId
  compMor := joinComp
  id_comp_id {s} x := by
    cases s with
    | pt => rfl
    | empty => exact Empty.elim x
    | suspSphere _ => cases x <;> rfl
    | joinCone _ =>
      rcases x with _ | (_ | _) <;> rfl

/-- `JoinSuspState.pt` is `IsContractibleState`. -/
theorem isContractibleState_pt : IsContractibleState JoinSuspState.pt := by
  refine ⟨fun q ↦ q = .pt, rfl, ?_⟩
  rintro q rfl
  exact ⟨⟨()⟩, inferInstanceAs (Subsingleton Unit), fun _ _ ↦ rfl⟩

/-- `JoinSuspState.empty` is `IsMinusOneTruncated`. -/
theorem isMinusOneTruncated_empty : IsMinusOneTruncated JoinSuspState.empty :=
  ⟨inferInstanceAs (Subsingleton Empty), fun a _ ↦ Empty.elim a⟩

/-- `JoinSuspState.pt` is `IsMinusOneTruncated`. -/
theorem isMinusOneTruncated_pt : IsMinusOneTruncated JoinSuspState.pt :=
  isContractibleState_pt.isMinusOneTruncated

/-- Exact `(K, K)`-cell height of `suspSphere K = Σ^K(S⁰)`: `HasHomCellHeight K (.suspSphere K)`
holds for every `K : ℕ`. -/
theorem hasHomCellHeight_suspSphere (K : ℕ) :
    HasHomCellHeight K (JoinSuspState.suspSphere K) := by
  induction K with
  | zero =>
    intro b₁ b₂
    cases b₁ <;> cases b₂
    · exact isMinusOneTruncated_pt
    · exact isMinusOneTruncated_empty
    · exact isMinusOneTruncated_empty
    · exact isMinusOneTruncated_pt
  | succ k ih =>
    intro b₁ b₂
    cases b₁ <;> cases b₂
    · exact isMinusOneTruncated_pt.hasHomCellHeight_zero.mono (Nat.zero_le k)
    · exact ih
    · exact isMinusOneTruncated_empty.hasHomCellHeight_zero.mono (Nat.zero_le k)
    · exact isMinusOneTruncated_pt.hasHomCellHeight_zero.mono (Nat.zero_le k)

/-- Strict lower bound on `suspSphere (K + 1)`: `¬ HasHomCellHeight K (.suspSphere (K + 1))` for
every `K : ℕ` (since `S⁰` has two distinct points `false ≠ true`). -/
theorem not_hasHomCellHeight_suspSphere_succ (K : ℕ) :
    ¬ HasHomCellHeight K (JoinSuspState.suspSphere (K + 1)) := by
  induction K with
  | zero =>
    intro h0
    have hsub : Subsingleton (Obj (hom (s := JoinSuspState.suspSphere 1)
        (false : Bool) (true : Bool))) := (h0 false true).1
    exact Bool.false_ne_true (hsub.elim false true)
  | succ k ih =>
    intro hk
    exact ih (hk false true)

/-- Every hom-state `hom u w` in `joinCone K = {a} ⋆ Σ^{K+1}(S⁰)` satisfies
`HasHomCellHeight K (hom u w)`. -/
theorem hasHomCellHeight_joinCone_hom (K : ℕ) (u w : Obj (JoinSuspState.joinCone K)) :
    HasHomCellHeight K (hom u w) := by
  rcases u with _ | (_ | _) <;> rcases w with _ | (_ | _)
  · exact isMinusOneTruncated_pt.hasHomCellHeight_zero.mono (Nat.zero_le K)
  · exact isMinusOneTruncated_pt.hasHomCellHeight_zero.mono (Nat.zero_le K)
  · exact isMinusOneTruncated_pt.hasHomCellHeight_zero.mono (Nat.zero_le K)
  · exact isMinusOneTruncated_empty.hasHomCellHeight_zero.mono (Nat.zero_le K)
  · exact isMinusOneTruncated_pt.hasHomCellHeight_zero.mono (Nat.zero_le K)
  · exact hasHomCellHeight_suspSphere K
  · exact isMinusOneTruncated_empty.hasHomCellHeight_zero.mono (Nat.zero_le K)
  · exact isMinusOneTruncated_empty.hasHomCellHeight_zero.mono (Nat.zero_le K)
  · exact isMinusOneTruncated_pt.hasHomCellHeight_zero.mono (Nat.zero_le K)

/-- State correspondence witness for the initial-object inclusion `l : {a} (.pt) → joinCone K`. -/
inductive JoinIncRel (K : ℕ) : JoinSuspState → JoinSuspState → Type
  | base : JoinIncRel K .pt (.joinCone K)
  | pt : JoinIncRel K .pt .pt

/-- `0`-cell mapping of `joinLeftSim K` (`() ↦ none = a` at `.base`, `() ↦ ()` at `.pt`). -/
abbrev joinLeftObj (K : ℕ) :
    ∀ {s₁ s₂ : JoinSuspState}, JoinIncRel K s₁ s₂ → Obj s₁ → Obj s₂
  | _, _, .base, _ => none
  | _, _, .pt, _ => ()

/-- Hom-state relation mapping of `joinLeftSim K`. -/
def joinLeftHom (K : ℕ) :
    ∀ {s₁ s₂ : JoinSuspState} (φ : JoinIncRel K s₁ s₂) (x y : Obj s₁),
      JoinIncRel K (hom x y) (hom (joinLeftObj K φ x) (joinLeftObj K φ y))
  | _, _, .base, (), () => .pt
  | _, _, .pt, (), () => .pt

/-- Initial-object inclusion simulation `joinLeftSim K : .pt → .joinCone K` (`() ↦ none = a`). -/
def joinLeftSim (K : ℕ) : GlobularSimulation JoinSuspState JoinSuspState where
  Rel := JoinIncRel K
  mapObj := joinLeftObj K
  mapHom := joinLeftHom K

/-- Terminal collapse simulation `joinRightSim : s → .pt`. -/
def joinRightSim : GlobularSimulation JoinSuspState JoinSuspState where
  Rel _ s₂ := PLift (s₂ = .pt)
  mapObj := fun {_ _} ⟨h⟩ _ ↦ cast (congrArg joinObj h.symm) ()
  mapHom := fun {_ _} ⟨h⟩ _ _ ↦ by
    subst h
    exact ⟨rfl⟩

/-- Canonical Lali split-idempotent retraction `joinConeLali K : LaliRetraction .pt (.joinCone K)`
realizing `E = const_a` (`x ↦ none`) with directed counit `ε_x : a → x`. -/
def joinConeLali (K : ℕ) : LaliRetraction JoinSuspState.pt (JoinSuspState.joinCone K) where
  L := joinLeftSim K
  R := joinRightSim
  relL := .base
  relR := ⟨rfl⟩
  retract_left_inv u := by
    cases u
    rfl
  counit _ := ()
  counit_left_isEquiv u := by
    cases u
    exact IsEquiv.id (s := JoinSuspState.joinCone K) none

/-- Generating equator boundary `sharpSphereBoundary K : HomBoundary K (.suspSphere K)` (`m = K + 2`
over `(some false, some true)` in `joinCone K`), landing on parallel `S⁰` points `(false, true)`. -/
def sharpSphereBoundary : ∀ K : ℕ, HomBoundary K (JoinSuspState.suspSphere K)
  | 0 => (false, true)
  | k + 1 => ⟨(false, true), sharpSphereBoundary k⟩

/-- The ambient `(K + 2)`-cell state bounded by `sharpSphereBoundary K` is `.empty` (`∅`). -/
theorem sharpSphereBoundary_hom_eq_empty (K : ℕ) :
    hom (homBoundarySrc (sharpSphereBoundary K)) (homBoundaryTgt (sharpSphereBoundary K)) =
      JoinSuspState.empty := by
  induction K with
  | zero => rfl
  | succ k ih => exact ih

/-- For any `B : HomBoundary r .pt`, the tip hom-state `hom (homBoundarySrc B) (homBoundaryTgt B)`
is `.pt` (`Unit`). -/
theorem pt_homBoundary_hom_eq_pt :
    ∀ {r : ℕ} (B : HomBoundary r JoinSuspState.pt),
      hom (homBoundarySrc B) (homBoundaryTgt B) = JoinSuspState.pt
  | 0, ((), ()) => rfl
  | _ + 1, ⟨((), ()), B'⟩ => pt_homBoundary_hom_eq_pt B'

/-- Inhabited `(K + 3)`-cell boundary `aboveCeilingBoundary K` over `(some false, some true)` in
`joinCone K` (replacing the final `S⁰` pair `(false, true)` by `(false, false)` and stepping one
dimension higher), witnessing non-vacuous `Unit → Unit` stabilization at `m = K + 3`. -/
def aboveCeilingBoundary : ∀ K : ℕ, HomBoundary (K + 1) (JoinSuspState.suspSphere K)
  | 0 => ⟨(false, false), ((), ())⟩
  | k + 1 => ⟨(false, true), aboveCeilingBoundary k⟩

/-- The ambient `(K + 3)`-cell state bounded by `aboveCeilingBoundary K` is `.pt` (`Unit`). -/
theorem aboveCeilingBoundary_hom_eq_pt (K : ℕ) :
    hom (homBoundarySrc (aboveCeilingBoundary K)) (homBoundaryTgt (aboveCeilingBoundary K)) =
      JoinSuspState.pt := by
  induction K with
  | zero => rfl
  | succ k ih => exact ih

end JoinSuspState

/-- **Proposition 11A Part 2 — Exact Sharpness of `max K_x K_y + 2` for All `K : ℕ`
(`prop11A_ceiling_sharp_at_max_add_two`):**
On `JoinSuspState.joinCone K` (`{a} ⋆ Σ^{K+1}(S⁰)`), let `x = some false` (`-`), `y = some true`
(`+`), and `lali = joinConeLali K` (`E = const_a`). Then:
1. Both `hom x y` and `hom (E x) (E y)` satisfy `HasHomCellHeight K` (`max K K + 2 = K + 2`),
2. At ambient dimension `m = K + 2` (`B = sharpSphereBoundary K`), the source `(K + 2)`-cell space
   is `IsEmpty` whereas the retracted `(K + 2)`-cell space is `Nonempty`, so `mapHomCell` fails to
   be bijective (`¬ Function.Bijective`), while
3. At ambient dimension `m = K + 3` (`aboveCeilingBoundary K`), both spaces are inhabited and
   `mapHomCell` is `Function.Bijective`. -/
theorem prop11A_ceiling_sharp_at_max_add_two (K : ℕ) :
    let lali := JoinSuspState.joinConeLali K
    let x : Obj (JoinSuspState.joinCone K) := some false
    let y : Obj (JoinSuspState.joinCone K) := some true
    let φxy := lali.endoSim.mapHom lali.endoRel x y
    let B : HomBoundary K (hom x y) := JoinSuspState.sharpSphereBoundary K
    let EB := mapHomBoundary lali.endoSim φxy B
    HasHomCellHeight K (hom x y) ∧
      HasHomCellHeight K (hom (lali.endoObj x) (lali.endoObj y)) ∧
      max K K + 2 = K + 2 ∧
      IsEmpty (Obj (hom (homBoundarySrc B) (homBoundaryTgt B))) ∧
      Nonempty (Obj (hom (homBoundarySrc EB) (homBoundaryTgt EB))) ∧
      ¬ Function.Bijective (mapHomCell lali.endoSim φxy B) ∧
      Function.Bijective
        (mapHomCell lali.endoSim φxy (JoinSuspState.aboveCeilingBoundary K)) := by
  intro lali x y φxy B EB
  have hKx : HasHomCellHeight K (hom x y) :=
    JoinSuspState.hasHomCellHeight_joinCone_hom K x y
  have hKy : HasHomCellHeight K (hom (lali.endoObj x) (lali.endoObj y)) :=
    JoinSuspState.hasHomCellHeight_joinCone_hom K (lali.endoObj x) (lali.endoObj y)
  have hemp : IsEmpty (Obj (hom (homBoundarySrc B) (homBoundaryTgt B))) := by
    rw [JoinSuspState.sharpSphereBoundary_hom_eq_empty K]
    exact inferInstanceAs (IsEmpty Empty)
  have hnonemp : Nonempty (Obj (hom (homBoundarySrc EB) (homBoundaryTgt EB))) := by
    have hpt : hom (homBoundarySrc EB) (homBoundaryTgt EB) = JoinSuspState.pt :=
      JoinSuspState.pt_homBoundary_hom_eq_pt (r := K) EB
    rw [hpt]
    exact ⟨()⟩
  have hnot_bij : ¬ Function.Bijective (mapHomCell lali.endoSim φxy B) := by
    intro hbij
    rcases hnonemp with ⟨b₀⟩
    rcases hbij.2 b₀ with ⟨a₀, _⟩
    exact hemp.false a₀
  have hbij_succ : Function.Bijective
      (mapHomCell lali.endoSim φxy (JoinSuspState.aboveCeilingBoundary K)) :=
    (prop11A_lali_stabilization_above_ceiling lali hKx hKy (le_of_eq (max_self K))
      (JoinSuspState.aboveCeilingBoundary K)).2.2.2.2
  exact ⟨hKx, hKy, by rw [max_self], hemp, hnonemp, hnot_bij, hbij_succ⟩

/-! ## Section 5: Mandatory 4-Layer Lean 4 Definition Check Gate (`namespace Checks`) -/

namespace Checks

/-! ### Layer 1: Inhabitation (Non-Degeneracy of Formalized Carriers) -/

/-- Layer 1 witness: `OmegaTowerState` is `Nontrivial` (`.pt ≠ .apex`). -/
instance instNontrivialOmegaTowerState : Nontrivial OmegaTowerState :=
  ⟨⟨.pt, .apex, by decide⟩⟩

/-- Layer 1 witness: `Obj OmegaTowerState.boolDisc` (`S⁰`) is `Nontrivial`. -/
instance instNontrivialBoolDiscObj : Nontrivial (Obj OmegaTowerState.boolDisc) :=
  ⟨⟨false, true, Bool.false_ne_true⟩⟩

/-- Layer 1 witness: `Obj (OmegaTowerState.chain 1)` (split-idempotent `2`-retract) is `Nontrivial`.
-/
instance instNontrivialChainOneObj : Nontrivial (Obj (OmegaTowerState.chain 1)) :=
  ⟨⟨false, true, Bool.false_ne_true⟩⟩

/-- Layer 1 witness: `Obj OmegaTowerState.endo1` (`rank = ω`) is `Nontrivial` (`none ≠ some 0`). -/
instance instNontrivialEndo1Obj : Nontrivial (Obj OmegaTowerState.endo1) :=
  ⟨⟨none, some 0, fun h ↦ by cases h⟩⟩

/-- Layer 1 witness: `Obj OmegaTowerState.apex` (`rank = ω + 1`) is `Nontrivial`. -/
instance instNontrivialApexObj : Nontrivial (Obj OmegaTowerState.apex) :=
  ⟨⟨false, true, Bool.false_ne_true⟩⟩

/-- Layer 1 witness: `CoindWalkState` and `Obj CoindWalkState.loop` are `Nontrivial`. -/
instance instNontrivialCoindWalkState : Nontrivial CoindWalkState :=
  ⟨⟨.pt, .loop, by decide⟩⟩

/-- Layer 1 witness: `JoinSuspState` and `Obj (JoinSuspState.joinCone K)` are `Nontrivial`. -/
instance instNontrivialJoinConeObj (K : ℕ) :
    Nontrivial (Obj (JoinSuspState.joinCone K)) :=
  ⟨⟨some false, some true, fun h ↦ Bool.false_ne_true (Option.some.inj h)⟩⟩

/-- Explicit existential inhabitation tuple across all formalized carriers. -/
theorem layer1_carriers_nontrivial :
    (∃ s₁ s₂ : OmegaTowerState, s₁ ≠ s₂) ∧
      (∃ u w : Obj OmegaTowerState.endo1, u ≠ w) ∧
      (∃ c₁ c₂ : CoindWalkState, c₁ ≠ c₂) ∧
      (∀ K : ℕ, ∃ x y : Obj (JoinSuspState.joinCone K), x ≠ y) :=
  ⟨exists_pair_ne _, exists_pair_ne _, exists_pair_ne _, fun _ ↦ exists_pair_ne _⟩

/-! ### Layer 2: Bidirectional Separation of Core Predicates -/

/-- Layer 2 Witness A — Rank `0` (`boolDisc` = `S⁰`) vs. Rank `1` (`chain 0` = `[1]`):
on `boolDisc` (`rank = 0`), `IsOrdinalInv 0 ↔ IsEquiv`; on `chain 0` (`rank = 1`),
`IsOrdinalInv 0 (chainArrow 0)` holds whereas `¬ IsEquiv (chainArrow 0)` (and `IsOrdinalInv 1 ↔
IsEquiv`). -/
theorem layer2_sep_rank0_vs_rank1 :
    rank OmegaTowerState.boolDisc = 0 ∧
      (∀ (x y : Obj OmegaTowerState.boolDisc) (f : Obj (hom x y)),
        IsOrdinalInv 0 f ↔ IsEquiv f) ∧
      rank (OmegaTowerState.chain 0) = 1 ∧
      IsOrdinalInv 0 (chainArrow 0) ∧
      ¬ IsEquiv (chainArrow 0) ∧
      (∀ (x y : Obj (OmegaTowerState.chain 0)) (f : Obj (hom x y)),
        IsOrdinalInv 1 f ↔ IsEquiv f) := by
  have hr0 : rank OmegaTowerState.boolDisc = 0 := rfl
  have hr1 : rank (OmegaTowerState.chain 0) = 1 := by
    change (((0 + 1 : ℕ) : Ordinal.{0}) = 1)
    simp
  refine ⟨hr0, fun _ _ _ ↦ theorem9A_ordinal_rank_completeness (le_of_eq hr0),
    hr1, isOrdinalInv_zero_of_any (chainArrow 0), chainArrow_not_isEquiv 0,
    fun _ _ _ ↦ theorem9A_ordinal_rank_completeness (le_of_eq hr1)⟩

/-- Layer 2 Witness B — Rank `2` Non-Equivalence Split-Idempotent `2`-Retract (`chain 1`):
`chainArrow 1` splits idempotent `e = false` (`e ∘ e = e ≠ id₁`), satisfying `IsOrdinalInv 1` while
refuting `IsOrdinalInv 2` and `IsEquiv` (whereas `idMor false` satisfies `IsEquiv`). -/
theorem layer2_sep_split_idempotent_two_retract :
    rank (OmegaTowerState.chain 1) = 2 ∧
      IsEquiv (idMor (s := OmegaTowerState.chain 1) (false : Bool)) ∧
      IsOrdinalInv 1 (chainArrow 1) ∧
      ¬ IsOrdinalInv 2 (chainArrow 1) ∧
      ¬ IsEquiv (chainArrow 1) := by
  have hr2 : rank (OmegaTowerState.chain 1) = 2 := by
    change (((1 + 1 : ℕ) : Ordinal.{0}) = 2)
    norm_cast
  rcases chainOne_split_retract_properties with ⟨_, _, _, _, h1, hn2, hneq⟩
  exact ⟨hr2, IsEquiv.id (s := OmegaTowerState.chain 1) false, h1, hn2, hneq⟩

/-- Layer 2 Witness C — Rank `ω` (`endo1`) vs. Rank `ω + 1` (`apex`):
on `endo1` (`rank = ω`), `IsOmegaInv ↔ IsEquiv` holds globally; on `apex` (`rank = ω + 1`),
`IsOmegaInv apexArrow` holds while `¬ IsEquiv apexArrow` and `¬ IsCoindEquiv apexArrow`. -/
theorem layer2_sep_rank_omega_vs_omega_add_one :
    rank OmegaTowerState.endo1 = Ordinal.omega0 ∧
      (∀ (x y : Obj OmegaTowerState.endo1) (f : Obj (hom x y)),
        IsOmegaInv f ↔ IsEquiv f) ∧
      rank OmegaTowerState.apex = Ordinal.omega0 + 1 ∧
      IsOmegaInv apexArrow ∧
      ¬ IsEquiv apexArrow ∧
      ¬ IsCoindEquiv apexArrow :=
  ⟨rfl, fun _ _ _ ↦ endo1_omegaInv_iff_isEquiv, rfl,
    apexArrow_isOmegaInv, apexArrow_not_isEquiv, apexArrow_not_isCoindEquiv⟩

/-- Layer 2 Witness D — Bidirectional separation of `IsCoindEquiv` vs. `IsEquiv`:
`idMor false` in `CoindWalkState.loop` satisfies `IsEquiv`, whereas `coindArrow` satisfies
`IsCoindEquiv coindArrow ∧ ¬ IsEquiv coindArrow`. -/
theorem layer2_sep_coindEquiv_vs_isEquiv :
    IsEquiv (idMor (s := CoindWalkState.loop) (false : Bool)) ∧
      IsCoindEquiv coindArrow ∧
      ¬ IsEquiv coindArrow :=
  ⟨IsEquiv.id (s := CoindWalkState.loop) false, coindArrow_isCoindEquiv, coindArrow_not_isEquiv⟩

/-- Layer 2 Witness E — Bidirectional separation of `HasHomCellHeight K` & Proposition 11A ceiling:
for every `K : ℕ`, `HasHomCellHeight K (.suspSphere K)` holds while
`¬ HasHomCellHeight K (.suspSphere (K + 1))`, and on `joinCone K` the Lali map fails bijectivity at
`m = K + 2` (`sharpSphereBoundary K`) while succeeding at `m = K + 3` (`aboveCeilingBoundary K`). -/
theorem layer2_sep_cellHeight_and_prop11A (K : ℕ) :
    HasHomCellHeight K (JoinSuspState.suspSphere K) ∧
      ¬ HasHomCellHeight K (JoinSuspState.suspSphere (K + 1)) ∧
      ¬ Function.Bijective (mapHomCell (JoinSuspState.joinConeLali K).endoSim
        ((JoinSuspState.joinConeLali K).endoSim.mapHom (JoinSuspState.joinConeLali K).endoRel
          (some false) (some true))
        (JoinSuspState.sharpSphereBoundary K)) ∧
      Function.Bijective (mapHomCell (JoinSuspState.joinConeLali K).endoSim
        ((JoinSuspState.joinConeLali K).endoSim.mapHom (JoinSuspState.joinConeLali K).endoRel
          (some false) (some true))
        (JoinSuspState.aboveCeilingBoundary K)) := by
  rcases prop11A_ceiling_sharp_at_max_add_two K with ⟨_, _, _, _, _, hnot, hbij⟩
  exact ⟨JoinSuspState.hasHomCellHeight_suspSphere K,
    JoinSuspState.not_hasHomCellHeight_suspSphere_succ K, hnot, hbij⟩

/-! ### Layer 3: Projection to Stock Mathlib Classes & Derived Sanity Lemmas -/

/-- Layer 3 projection sanity 1: stock Mathlib `LinearOrder Ordinal.{0}`, `WellFoundedLT
Ordinal.{0}`, and strict ordinal rank chain `0 < 1 < 2 < ω < ω + 1` realized by `OmegaTowerState`.
-/
theorem layer3_ordinal_rank_strict_chain :
    rank OmegaTowerState.boolDisc < rank (OmegaTowerState.chain 0) ∧
      rank (OmegaTowerState.chain 0) < rank (OmegaTowerState.chain 1) ∧
      (∀ d : ℕ, rank (OmegaTowerState.chain d) < rank OmegaTowerState.endo1) ∧
      rank OmegaTowerState.endo1 < rank OmegaTowerState.apex := by
  refine ⟨?_, ?_, fun d ↦ Ordinal.nat_lt_omega0 (d + 1), ?_⟩
  · change (0 : Ordinal.{0}) < ((1 : ℕ) : Ordinal.{0})
    rw [← Nat.cast_zero]
    exact Nat.cast_lt.mpr Nat.one_pos
  · change ((1 : ℕ) : Ordinal.{0}) < ((2 : ℕ) : Ordinal.{0})
    exact Nat.cast_lt.mpr (by decide)
  · change Ordinal.omega0 < Ordinal.omega0 + 1
    rw [Ordinal.add_one_eq_succ]
    exact Order.lt_succ Ordinal.omega0

/-- Layer 3 derived sanity 2: associativity of `GlobularSimulation.comp` on `0`-cells. -/
theorem layer3_globularSimulation_comp_assoc {S₁ S₂ S₃ S₄ : Type u}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂]
    [GlobularInfSystem S₃] [GlobularInfSystem S₄]
    (H : GlobularSimulation S₃ S₄) (G : GlobularSimulation S₂ S₃) (F : GlobularSimulation S₁ S₂)
    {s₁ : S₁} {s₂ : S₂} {s₃ : S₃} {s₄ : S₄}
    (φF : F.Rel s₁ s₂) (φG : G.Rel s₂ s₃) (φH : H.Rel s₃ s₄) (x : Obj s₁) :
    ((H.comp G).comp F).mapObj ⟨s₂, φF, ⟨s₃, φG, φH⟩⟩ x =
      (H.comp (G.comp F)).mapObj ⟨s₃, ⟨s₂, φF, φG⟩, φH⟩ x :=
  rfl

/-- Layer 3 derived sanity 3 — Complete Strict 4-Step Equivalence Separation Ladder:
`IsEquiv ⊊ IsCoindEquiv ⊊ IsOmegaInv ⊊ (∀ d, ...) ⊊ IsOrdinalInv 1 ⊊ IsOrdinalInv 0`, uniting
every forward implication with an explicit kernel-verified counterexample to its converse. -/
theorem strict_four_tier_equivalence_separation :
    -- Forward implication chain across arbitrary `GlobularInfSystem`s:
    (∀ {S : Type} [GlobularInfSystem S] {s : S} {x y : Obj s} (f : Obj (hom x y)),
      (IsEquiv f → IsCoindEquiv f) ∧
        (IsCoindEquiv f → IsOmegaInv f) ∧
        (∀ d : ℕ, IsOmegaInv f → IsOrdinalInv ((d + 1 : ℕ) : Ordinal.{0}) f) ∧
        (∀ d : ℕ, IsOrdinalInv ((d + 1 : ℕ) : Ordinal.{0}) f →
          IsOrdinalInv (d : Ordinal.{0}) f)) ∧
    -- Strict counterexamples refuting every converse:
    (IsCoindEquiv coindArrow ∧ ¬ IsEquiv coindArrow) ∧
    (IsOmegaInv apexArrow ∧ ¬ IsCoindEquiv apexArrow) ∧
    (∀ d : ℕ, IsOrdinalInv (d : Ordinal.{0}) (chainArrow d) ∧
      ¬ IsOrdinalInv ((d + 1 : ℕ) : Ordinal.{0}) (chainArrow d)) := by
  refine ⟨fun f ↦ ⟨IsEquiv.isCoindEquiv, IsCoindEquiv.isOmegaInv,
    fun d hf ↦ hf (d + 1),
    fun d hf ↦ isOrdinalInv_anti (Nat.cast_le.mpr (Nat.le_succ d)) hf⟩,
    ⟨coindArrow_isCoindEquiv, coindArrow_not_isEquiv⟩,
    ⟨apexArrow_isOmegaInv, apexArrow_not_isCoindEquiv⟩,
    fun d ↦ ⟨chainArrow_isOrdinalInv d, chainArrow_not_isOrdinalInv_succ d⟩⟩

/-! ### Layer 4: Kernel Axiom Gate (`#guard_msgs in #print axioms`) -/

section KernelAxiomGate

set_option linter.hashCommand false

/-- info: 'HomotopyCRM.isOmegaInv_iff_isOrdinalInv_omega0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.isOmegaInv_iff_isOrdinalInv_omega0

/-- info: 'HomotopyCRM.theorem9A_ordinal_rank_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theorem9A_ordinal_rank_completeness

/-- info: 'HomotopyCRM.ranked_coindEquiv_iff_isEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.ranked_coindEquiv_iff_isEquiv

/-- info: 'HomotopyCRM.theorem9A_omega_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theorem9A_omega_completeness

/-- info: 'HomotopyCRM.orw_question558_stabilizes_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.orw_question558_stabilizes_at_zero

/-- info: 'HomotopyCRM.apexArrow_isOmegaInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.apexArrow_isOmegaInv

/-- info: 'HomotopyCRM.apexArrow_not_isEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.apexArrow_not_isEquiv

/-- info: 'HomotopyCRM.apexArrow_not_isCoindEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.apexArrow_not_isCoindEquiv

/-- info: 'HomotopyCRM.prop11A_lali_stabilization_above_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.prop11A_lali_stabilization_above_ceiling

/-- info: 'HomotopyCRM.prop11A_ceiling_sharp_at_max_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.prop11A_ceiling_sharp_at_max_add_two

/-- info: 'HomotopyCRM.Checks.layer1_carriers_nontrivial' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer1_carriers_nontrivial

/-- info: 'HomotopyCRM.Checks.layer2_sep_rank0_vs_rank1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_rank0_vs_rank1

/-- info: 'HomotopyCRM.Checks.layer2_sep_split_idempotent_two_retract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_split_idempotent_two_retract

/-- info: 'HomotopyCRM.Checks.layer2_sep_rank_omega_vs_omega_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_rank_omega_vs_omega_add_one

/-- info: 'HomotopyCRM.Checks.layer2_sep_coindEquiv_vs_isEquiv' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_coindEquiv_vs_isEquiv

/-- info: 'HomotopyCRM.Checks.layer2_sep_cellHeight_and_prop11A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_cellHeight_and_prop11A

/-- info: 'HomotopyCRM.Checks.layer3_ordinal_rank_strict_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer3_ordinal_rank_strict_chain

/-- info: 'HomotopyCRM.Checks.strict_four_tier_equivalence_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.strict_four_tier_equivalence_separation

end KernelAxiomGate

end Checks

end HomotopyCRM
