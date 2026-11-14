/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HomotopyCRM Formalization Team
-/
import HomotopyCRM.OrdinalRankCompleteness
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Relation
import Mathlib.Order.BoundedOrder.Basic

/-!
# Postnikov Completeness Dichotomy, Absorbing Monoids, and the Step-Product Phantom (`MSG_018`)

This module formalizes **Theorems 12B, 12C, and 12D** (negative resolution of `Conjecture C1` /
`TODO-05`) inside the `HomotopyCRM` library along the verified strict 4-tier reflective
localization ladder
`Cat^L_(∞,∞) ⊊ Cat^ω_(∞,∞) ⊊ Cat^coind_(∞,∞) ⊊ Cat^R_(∞,∞) := lim_κ Cat_(∞,n)`
(Ozornova–Rovelli–Walde `arXiv:2603.11005v2`, `arXiv:2608.28355`, `arXiv:2610.38698`;
Gepner–Heine `arXiv:2603.09903`).

## Main Results

1. **Globular Functors, Object Equivalence, Gauntness, & `n`-Truncation:**
   - Defines `ObjEquiv`, `ObjEquivRel` (`Equivalence`), `IsObjGaunt`, `IsHereditarilyGaunt`,
     `IsNTruncated` (upward monotone via `IsNTruncated.mono`), strict `GlobularFunctor` (preserving
     `IsEquiv`, `ObjEquiv`, and `ObjEquivRel`), and binary products `GlobularInfSystem (S₁ × S₂)`.

2. **Theorem 12B & Theorem 12C — `[1]`-Classifier SCC Trapping & `1`-Acyclic Completeness:**
   - Models `1`-cell reachability preorder `Reach1` (`x ≼₁ y`) and strongly connected components
     `SameSCC1`.
   - Constructs the principal upper-set functor `upperSetClassifier s x`
     (`GlobularFunctor S StepState`), into `[1] = StepState.factor (.monoid 1)`, proving
     **`theorem12B_classifier_scc_trapping`** and **`theorem12B_tower_trapped_in_single_scc`**.
   - Defines `IsOneAcyclic` and proves **`theorem12C_antisymmetric_postnikov_completeness`**: under
     `IsOneAcyclic`, every Postnikov-compatible object sequence collapses to a single equivalence
     class (and single object under `IsObjGaunt`).

3. **Inductive Gaunt Absorbing-Monoid Tower (`AbsorbingLaliMonoid`, `ℳ_k`, `𝒜_k`):**
   - Models `FactorState` (`.pt`, `.empty`, `.iso`, `.monoid k`), strict commutative absorbing
     monoid multiplication `mulFunctor` on `StepState × StepState → StepState`, stock Mathlib
     `CommMonoid` / `SemilatticeInf` / `OrderBot` on `AbsorbingMonoidCarrier k`, concrete
     `LaliRetraction` (`monoidLali`), hereditary gauntness (`isHereditarilyGaunt_monoid`), exact
     truncation dimension `k + 1` (`isNTruncated_monoid`, `not_isNTruncated_monoid_pred`), and
     universal truncation collapse **`absorbingMonoid_collapse_le`** at all `n ≤ k`.

4. **Theorem 12D — Rank-`ω` Gaunt Step-Product Phantom `StepProductQ` (`Q`):**
   - Defines `StepState.qFull` (`Obj = ℕ`, `hom m r = ∏_{j < min m r} ℳ_{j+1}`), proving
     `RankedInfCat StepState` (`rank .qFull = ω`, `rank (hom m r) = min m r < ω`), invoking
     `theorem9A_omega_completeness` and `orw_question558_stabilizes_at_zero`
     (**`stepProductQ_omega_completeness`**), proving hereditary gauntness, finite local hom
     cardinality `2 ^ min m r`, coordinate projections `prFunctor`, and slice inclusions
     `sliceFunctor`.
   - Proves model-independent **`theorem12D_stepProductQ_phantom_not_realized`** for *every*
     `PostnikovReflectionSystem StepState.qFull` and constructs **`stepProductPostnikovSystem`**,
     completing the negative resolution **`conjecture_c1_disproof_summary`**.

5. **Mandatory 4-Layer Definition Check Gate (`namespace Checks`):**
   - Verifies Inhabitation (Layer 1), Bidirectional Separation across all predicates (Layer 2),
     stock Mathlib projections and derived boundary theorems (Layer 3), and the
     `#guard_msgs in #print axioms` Kernel Axiom Gate (Layer 4).
-/

namespace HomotopyCRM

open GlobularInfSystem RankedInfCat

universe u u₁ u₂ v

/-! ## Section 1: Globular Functors, Object Equivalence, Gauntness, & `n`-Truncation -/

/-- Object equivalence `ObjEquiv x y` in a `GlobularInfSystem S`: existence of an inductively
invertible `1`-morphism `f : Obj (hom x y)` (`IsEquiv f`). -/
def ObjEquiv {S : Type u} [GlobularInfSystem S] {s : S} (x y : Obj s) : Prop :=
  ∃ f : Obj (hom x y), IsEquiv f

/-- Reflexivity of `ObjEquiv` via `idMor x`. -/
theorem ObjEquiv.refl {S : Type u} [GlobularInfSystem S] {s : S} (x : Obj s) :
    ObjEquiv x x :=
  ⟨idMor x, IsEquiv.id x⟩

/-- Symmetry of `IsEquiv` witnessing the inverse `1`-cell `g : Obj (hom y x)`. -/
theorem IsEquiv.exists_inv {S : Type u} [GlobularInfSystem S] {s : S} {x y : Obj s}
    {f : Obj (hom x y)} (hf : IsEquiv f) :
    ∃ g : Obj (hom y x), IsEquiv g := by
  cases hf with
  | id => exact ⟨idMor x, IsEquiv.id x⟩
  | mk _ g η ε hη hε => exact ⟨g, IsEquiv.mk g f ε η hε hη⟩

/-- Symmetry of `ObjEquiv`. -/
theorem ObjEquiv.symm {S : Type u} [GlobularInfSystem S] {s : S} {x y : Obj s}
    (h : ObjEquiv x y) : ObjEquiv y x :=
  let ⟨_, hf⟩ := h
  hf.exists_inv

/-- Equivalence closure `ObjEquivRel` of `ObjEquiv` (`Relation.ReflTransGen ObjEquiv`). -/
def ObjEquivRel {S : Type u} [GlobularInfSystem S] {s : S} (x y : Obj s) : Prop :=
  Relation.ReflTransGen ObjEquiv x y

/-- Every single-step `ObjEquiv x y` induces `ObjEquivRel x y`. -/
theorem ObjEquiv.to_objEquivRel {S : Type u} [GlobularInfSystem S] {s : S} {x y : Obj s}
    (h : ObjEquiv x y) : ObjEquivRel x y :=
  Relation.ReflTransGen.single h

/-- Reflexivity of `ObjEquivRel`. -/
theorem ObjEquivRel.refl {S : Type u} [GlobularInfSystem S] {s : S} (x : Obj s) :
    ObjEquivRel x x :=
  Relation.ReflTransGen.refl

/-- Symmetry of `ObjEquivRel`. -/
theorem ObjEquivRel.symm {S : Type u} [GlobularInfSystem S] {s : S} {x y : Obj s}
    (h : ObjEquivRel x y) : ObjEquivRel y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hbc.symm) ih

/-- Transitivity of `ObjEquivRel`. -/
theorem ObjEquivRel.trans {S : Type u} [GlobularInfSystem S] {s : S} {x y z : Obj s}
    (h₁ : ObjEquivRel x y) (h₂ : ObjEquivRel y z) : ObjEquivRel x z :=
  Relation.ReflTransGen.trans h₁ h₂

/-- `ObjEquivRel` is a genuine `Equivalence` on `Obj s`. -/
theorem objEquivRel_equivalence {S : Type u} [GlobularInfSystem S] (s : S) :
    Equivalence (@ObjEquivRel S _ s) where
  refl := ObjEquivRel.refl
  symm := @ObjEquivRel.symm S _ s
  trans := @ObjEquivRel.trans S _ s

/-- Transitivity of `ReachableFrom`. -/
theorem ReachableFrom.trans {S : Type u} [GlobularInfSystem S] {s t q : S}
    (h₁ : ReachableFrom s t) (h₂ : ReachableFrom t q) : ReachableFrom s q := by
  induction h₂ with
  | refl => exact h₁
  | step _ x y ih => exact ReachableFrom.step ih x y

/-- Head-decomposition lemma for `ReachableFrom`: either `t = s` or `t` is reachable from some
`1`-hom state `hom x y`. -/
theorem ReachableFrom.cases_head {S : Type u} [GlobularInfSystem S] {s t : S}
    (h : ReachableFrom s t) :
    t = s ∨ ∃ x y : Obj s, ReachableFrom (hom x y) t := by
  induction h with
  | refl => exact Or.inl rfl
  | @step q _ a b ih =>
    rcases ih with rfl | ⟨x, y, hxy⟩
    · exact Or.inr ⟨a, b, ReachableFrom.refl⟩
    · exact Or.inr ⟨x, y, ReachableFrom.step hxy a b⟩

/-- A state `s : S` is object-gaunt (`IsObjGaunt s`) if object equivalence forces strict
equality `x = y` on `0`-cells. -/
def IsObjGaunt {S : Type u} [GlobularInfSystem S] (s : S) : Prop :=
  ∀ ⦃x y : Obj s⦄, ObjEquiv x y → x = y

/-- Under `IsObjGaunt s`, the transitive equivalence closure `ObjEquivRel x y` collapses to strict
equality `x = y`. -/
theorem IsObjGaunt.objEquivRel_eq {S : Type u} [GlobularInfSystem S] {s : S}
    (hs : IsObjGaunt s) {x y : Obj s} :
    ObjEquivRel x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (hs hbc)
  · rintro rfl
    exact ObjEquivRel.refl _

/-- Hereditary gauntness (`IsHereditarilyGaunt s`): `IsObjGaunt` holds on `s` and every nested
`hom`-state `ReachableFrom s t`. -/
def IsHereditarilyGaunt {S : Type u} [GlobularInfSystem S] (s : S) : Prop :=
  ∀ ⦃t : S⦄, ReachableFrom s t → IsObjGaunt t

/-- Hereditary gauntness restricts to `IsObjGaunt s`. -/
theorem IsHereditarilyGaunt.isObjGaunt {S : Type u} [GlobularInfSystem S] {s : S}
    (hs : IsHereditarilyGaunt s) : IsObjGaunt s :=
  hs ReachableFrom.refl

/-- Hereditary gauntness descends to every `hom x y`. -/
theorem IsHereditarilyGaunt.hom {S : Type u} [GlobularInfSystem S] {s : S}
    (hs : IsHereditarilyGaunt s) (x y : Obj s) : IsHereditarilyGaunt (hom x y) :=
  fun _ ht ↦ hs (ReachableFrom.trans (ReachableFrom.step ReachableFrom.refl x y) ht)

/-- Constructing `IsHereditarilyGaunt s` from `IsObjGaunt s` and `IsHereditarilyGaunt (hom x y)`. -/
theorem isHereditarilyGaunt_of_hom {S : Type u} [GlobularInfSystem S] {s : S}
    (hs : IsObjGaunt s) (hh : ∀ x y : Obj s, IsHereditarilyGaunt (hom x y)) :
    IsHereditarilyGaunt s := by
  intro t ht
  rcases ht.cases_head with rfl | ⟨x, y, hxy⟩
  · exact hs
  · exact hh x y hxy

/-- Local `(∞, n)`-truncation predicate `IsNTruncated n s`:
- `n = 0`: `(∞, 0)`-groupoidal (anima), meaning every `1`-morphism in every reachable `hom`-state
  from `s` is an inductive equivalence `IsEquiv`.
- `n + 1`: every `hom x y` is `IsNTruncated n`. -/
def IsNTruncated {S : Type u} [GlobularInfSystem S] : ℕ → S → Prop
  | 0, s => ∀ ⦃t : S⦄, ReachableFrom s t → ∀ ⦃x y : Obj t⦄ (f : Obj (hom x y)), IsEquiv f
  | n + 1, s => ∀ x y : Obj s, IsNTruncated n (hom x y)

/-- `IsNTruncated 0 s` makes every `1`-morphism of `s` an `IsEquiv`. -/
theorem IsNTruncated.isEquiv_of_zero {S : Type u} [GlobularInfSystem S] {s : S}
    (hs : IsNTruncated 0 s) {x y : Obj s} (f : Obj (hom x y)) : IsEquiv f :=
  hs ReachableFrom.refl f

/-- `IsNTruncated 0 s` automatically yields `IsNTruncated 1 s`. -/
theorem IsNTruncated.zero_to_one {S : Type u} [GlobularInfSystem S] {s : S}
    (hs : IsNTruncated 0 s) : IsNTruncated 1 s :=
  fun x y _ ht _ _ f ↦
    hs (ReachableFrom.trans (ReachableFrom.step ReachableFrom.refl x y) ht) f

/-- Upward monotonicity of `IsNTruncated` in the categorical dimension `n : ℕ`. -/
theorem IsNTruncated.mono {S : Type u} [GlobularInfSystem S] :
    ∀ {m n : ℕ} (_ : m ≤ n) {s : S}, IsNTruncated m s → IsNTruncated n s
  | 0, 0, _, _, hs => hs
  | 0, _ + 1, _, _, hs => fun x y ↦
    IsNTruncated.mono (Nat.zero_le _) (hs.zero_to_one x y)
  | _ + 1, 0, hle, _, _ => False.elim (Nat.not_succ_le_zero _ hle)
  | _ + 1, _ + 1, hle, _, hs => fun x y ↦
    IsNTruncated.mono (Nat.le_of_succ_le_succ hle) (hs x y)

/-- Every `IsMinusOneTruncated` state is reachable-invariant and therefore `IsNTruncated 0`. -/
theorem IsMinusOneTruncated.reachable_minusOne {S : Type u} [GlobularInfSystem S] {s t : S}
    (hs : IsMinusOneTruncated s) (ht : ReachableFrom s t) : IsMinusOneTruncated t := by
  induction ht with
  | refl => exact hs
  | step _ x y ih => exact (ih.2 x y).isMinusOneTruncated

/-- Every `IsMinusOneTruncated` state satisfies `IsNTruncated 0`. -/
theorem IsMinusOneTruncated.isNTruncated_zero {S : Type u} [GlobularInfSystem S] {s : S}
    (hs : IsMinusOneTruncated s) : IsNTruncated 0 s :=
  fun _ ht _ _ f ↦ (hs.reachable_minusOne ht).isEquiv_mor f

/-- Every `IsContractibleState` satisfies `IsNTruncated 0`. -/
theorem IsContractibleState.isNTruncated_zero {S : Type u} [GlobularInfSystem S] {s : S}
    (hs : IsContractibleState s) : IsNTruncated 0 s :=
  hs.isMinusOneTruncated.isNTruncated_zero

/-- Action of a `GlobularSimulation` on `1`-morphisms `Obj (hom x y)`. -/
abbrev GlobularSimulation.mapMor {S₁ : Type u₁} {S₂ : Type u₂}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂]
    (F : GlobularSimulation S₁ S₂) {s₁ : S₁} {s₂ : S₂} (φ : F.Rel s₁ s₂)
    {x y : Obj s₁} (f : Obj (hom x y)) :
    Obj (hom (F.mapObj φ x) (F.mapObj φ y)) :=
  F.mapObj (F.mapHom φ x y) f

/-- Strict globular `(∞,∞)`-functor extending `GlobularSimulation` with identity and composition
preservation at every state correspondence witness `φ : Rel s₁ s₂`. -/
structure GlobularFunctor (S₁ : Type u₁) (S₂ : Type u₂)
    [GlobularInfSystem S₁] [GlobularInfSystem S₂]
    extends GlobularSimulation S₁ S₂ where
  /-- Strict preservation of `idMor`. -/
  map_id : ∀ {s₁ : S₁} {s₂ : S₂} (φ : Rel s₁ s₂) (x : Obj s₁),
    toGlobularSimulation.mapMor φ (idMor x) = idMor (mapObj φ x)
  /-- Strict preservation of `compMor`. -/
  map_comp : ∀ {s₁ : S₁} {s₂ : S₂} (φ : Rel s₁ s₂) {x y z : Obj s₁}
    (f : Obj (hom x y)) (g : Obj (hom y z)),
    toGlobularSimulation.mapMor φ (compMor f g) =
      compMor (toGlobularSimulation.mapMor φ f) (toGlobularSimulation.mapMor φ g)

namespace GlobularFunctor

/-- Helper transporting `IsEquiv` along endpoint equalities on parallel cells. -/
private theorem isEquiv_congr_endpoints {S : Type u} [GlobularInfSystem S] {s : S}
    {a₁ a₂ b₁ b₂ : Obj s} (ha : a₁ = a₂) (hb : b₁ = b₂)
    (α : Obj (hom a₁ b₁)) (hα : IsEquiv α) :
    IsEquiv (hb ▸ ha ▸ α) := by
  subst ha hb
  exact hα

/-- Helper constructing a witness `1`-cell of `hom a b` from an equality `a = b`. -/
private def cellOfEq {S : Type u} [GlobularInfSystem S] {s : S}
    {a b : Obj s} (h : a = b) : Obj (hom a b) :=
  cast (congrArg (fun u ↦ Obj (hom u b)) h.symm) (idMor b)

/-- Helper proving `IsEquiv (cellOfEq h)` for any equality `h : a = b`. -/
private theorem isEquiv_cellOfEq {S : Type u} [GlobularInfSystem S] {s : S}
    {a b : Obj s} (h : a = b) : IsEquiv (cellOfEq h) := by
  subst h
  exact IsEquiv.id _

/-- Identity `GlobularFunctor` on `S`. -/
def id (S : Type u) [GlobularInfSystem S] : GlobularFunctor S S where
  toGlobularSimulation := GlobularSimulation.id S
  map_id := fun {_ _} φ x ↦ by
    cases φ
    rfl
  map_comp := fun {_ _} φ _ _ _ f g ↦ by
    cases φ
    rfl

/-- Composition `G.comp F` of two `GlobularFunctor`s in the same universe `Type u`. -/
def comp {S₁ S₂ S₃ : Type u}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] [GlobularInfSystem S₃]
    (G : GlobularFunctor S₂ S₃) (F : GlobularFunctor S₁ S₂) :
    GlobularFunctor S₁ S₃ where
  toGlobularSimulation := G.toGlobularSimulation.comp F.toGlobularSimulation
  map_id := fun {_ _} ⟨_, φF, φG⟩ x ↦ by
    change G.mapMor φG (F.mapMor φF (idMor x)) = idMor (G.mapObj φG (F.mapObj φF x))
    rw [F.map_id φF x, G.map_id φG (F.mapObj φF x)]
  map_comp := fun {_ _} ⟨_, φF, φG⟩ _ _ _ f g ↦ by
    change G.mapMor φG (F.mapMor φF (compMor f g)) =
      compMor (G.mapMor φG (F.mapMor φF f)) (G.mapMor φG (F.mapMor φF g))
    rw [F.map_comp φF f g, G.map_comp φG]

/-- Mixed-universe left composition `G.compLeftZero F` when `S₁, S₂ : Type 0` and `S₃ : Type v`.
-/
def compLeftZero {S₁ S₂ : Type} {S₃ : Type v}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] [GlobularInfSystem S₃]
    (G : GlobularFunctor S₂ S₃) (F : GlobularFunctor S₁ S₂) :
    GlobularFunctor S₁ S₃ where
  Rel s₁ s₃ := Σ s₂ : S₂, F.Rel s₁ s₂ × G.Rel s₂ s₃
  mapObj := fun {_ _} ⟨_, φF, φG⟩ x ↦ G.mapObj φG (F.mapObj φF x)
  mapHom := fun {_ _} ⟨_, φF, φG⟩ x y ↦
    ⟨hom (F.mapObj φF x) (F.mapObj φF y), F.mapHom φF x y,
      G.mapHom φG (F.mapObj φF x) (F.mapObj φF y)⟩
  map_id := fun {_ _} ⟨_, φF, φG⟩ x ↦ by
    change G.mapMor φG (F.mapMor φF (idMor x)) = idMor (G.mapObj φG (F.mapObj φF x))
    rw [F.map_id φF x, G.map_id φG (F.mapObj φF x)]
  map_comp := fun {_ _} ⟨_, φF, φG⟩ _ _ _ f g ↦ by
    change G.mapMor φG (F.mapMor φF (compMor f g)) =
      compMor (G.mapMor φG (F.mapMor φF f)) (G.mapMor φG (F.mapMor φF g))
    rw [F.map_comp φF f g, G.map_comp φG]

/-- Every `GlobularFunctor` preserves `IsEquiv`. -/
theorem map_isEquiv {S₁ : Type u₁} {S₂ : Type u₂}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] (F : GlobularFunctor S₁ S₂)
    {s₁ : S₁} {x y : Obj s₁} {f : Obj (hom x y)} (hf : IsEquiv f) :
    ∀ {s₂ : S₂} (φ : F.Rel s₁ s₂), IsEquiv (F.mapMor φ f) := by
  induction hf with
  | @id s₁ x =>
    intro s₂ φ
    rw [F.map_id φ x]
    exact IsEquiv.id _
  | @mk s₁ x y f g η ε _ _ ihη ihε =>
    intro s₂ φ
    let η0 : Obj (hom (F.mapMor φ (compMor f g)) (F.mapMor φ (idMor x))) :=
      F.mapMor (F.mapHom φ x x) η
    let ε0 : Obj (hom (F.mapMor φ (compMor g f)) (F.mapMor φ (idMor y))) :=
      F.mapMor (F.mapHom φ y y) ε
    let η1 := F.map_id φ x ▸ F.map_comp φ f g ▸ η0
    let ε1 := F.map_id φ y ▸ F.map_comp φ g f ▸ ε0
    have hη' : IsEquiv η1 :=
      isEquiv_congr_endpoints (F.map_comp φ f g) (F.map_id φ x) η0 (ihη (F.mapHom φ x x))
    have hε' : IsEquiv ε1 :=
      isEquiv_congr_endpoints (F.map_comp φ g f) (F.map_id φ y) ε0 (ihε (F.mapHom φ y y))
    exact IsEquiv.mk (F.mapMor φ f) (F.mapMor φ g) η1 ε1 hη' hε'

/-- Every `GlobularFunctor` preserves `ObjEquiv`. -/
theorem map_objEquiv {S₁ : Type u₁} {S₂ : Type u₂}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] (F : GlobularFunctor S₁ S₂)
    {s₁ : S₁} {s₂ : S₂} (φ : F.Rel s₁ s₂) {x y : Obj s₁} (h : ObjEquiv x y) :
    ObjEquiv (F.mapObj φ x) (F.mapObj φ y) :=
  let ⟨f, hf⟩ := h
  ⟨F.mapMor φ f, F.map_isEquiv hf φ⟩

/-- Every `GlobularFunctor` preserves `ObjEquivRel`. -/
theorem map_objEquivRel {S₁ : Type u₁} {S₂ : Type u₂}
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] (F : GlobularFunctor S₁ S₂)
    {s₁ : S₁} {s₂ : S₂} (φ : F.Rel s₁ s₂) {x y : Obj s₁} (h : ObjEquivRel x y) :
    ObjEquivRel (F.mapObj φ x) (F.mapObj φ y) := by
  induction h with
  | refl => exact ObjEquivRel.refl _
  | tail _ hbc ih => exact ObjEquivRel.trans ih (F.map_objEquiv φ hbc).to_objEquivRel

end GlobularFunctor

/-- Binary product `GlobularInfSystem (S₁ × S₂)` on state spaces in the same universe. -/
instance instGlobularInfSystemProd (S₁ S₂ : Type u)
    [GlobularInfSystem S₁] [GlobularInfSystem S₂] :
    GlobularInfSystem (S₁ × S₂) where
  Obj p := Obj p.1 × Obj p.2
  hom x y := (hom x.1 y.1, hom x.2 y.2)
  idMor x := (idMor x.1, idMor x.2)
  compMor f g := (compMor f.1 g.1, compMor f.2 g.2)
  id_comp_id x := Prod.ext (id_comp_id x.1) (id_comp_id x.2)

/-! ## Section 2: `FactorState`, `StepState`, & Part (a) — `[1]`-Classifier SCC Trapping
(Theorems 12B & 12C) -/

/-- Factor state space hosting `.pt` (`*`), `.empty` (`∅`), `.iso` (walking isomorphism `J`),
and the inductive gaunt commutative absorbing monoids `.monoid k` (`ℳ_k` for `k ≥ 1`, `*` for
`k = 0`). -/
inductive FactorState : Type
  | pt : FactorState
  | empty : FactorState
  | iso : FactorState
  | monoid : ℕ → FactorState
  deriving DecidableEq, Repr

namespace FactorState

/-- Underlying `0`-cell type of each `FactorState`. -/
def obj : FactorState → Type
  | .pt => Unit
  | .empty => Empty
  | .iso => Bool
  | .monoid 0 => Unit
  | .monoid (_ + 1) => Bool

/-- Hom-state classification on `FactorState`. -/
def hom : ∀ {s : FactorState}, obj s → obj s → FactorState
  | .pt, _, _ => .pt
  | .empty, x, _ => Empty.elim x
  | .iso, _, _ => .pt
  | .monoid 0, _, _ => .pt
  | .monoid 1, false, false => .pt
  | .monoid 1, false, true => .pt
  | .monoid 1, true, false => .empty
  | .monoid 1, true, true => .pt
  | .monoid (_ + 2), false, false => .pt
  | .monoid (_ + 2), false, true => .pt
  | .monoid (_ + 2), true, false => .pt
  | .monoid (k + 2), true, true => .monoid (k + 1)

/-- Identity `1`-morphism on `FactorState`. -/
def idMor : ∀ {s : FactorState} (x : obj s), obj (hom x x)
  | .pt, () => ()
  | .empty, x => Empty.elim x
  | .iso, _ => ()
  | .monoid 0, () => ()
  | .monoid 1, false => ()
  | .monoid 1, true => ()
  | .monoid (_ + 2), false => ()
  | .monoid (_ + 2), true => true

/-- Diagrammatic `1`-morphism composition on `FactorState`:
in `.monoid (k + 2)`, `compMor (true → false) (false → true) = false` (`e_{k+1}`) and
`compMor (true → true) (true → true) = a && b`. -/
def compMor : ∀ {s : FactorState} {x y z : obj s},
    obj (hom x y) → obj (hom y z) → obj (hom x z)
  | .pt, _, _, _, _, _ => ()
  | .empty, x, _, _, _, _ => Empty.elim x
  | .iso, _, _, _, _, _ => ()
  | .monoid 0, _, _, _, _, _ => ()
  | .monoid 1, false, false, false, _, _ => ()
  | .monoid 1, false, false, true, _, _ => ()
  | .monoid 1, false, true, true, _, _ => ()
  | .monoid 1, true, true, true, _, _ => ()
  | .monoid 1, true, false, _, f, _ => Empty.elim f
  | .monoid 1, false, true, false, _, g => Empty.elim g
  | .monoid 1, true, true, false, _, g => Empty.elim g
  | .monoid (_ + 2), false, _, false, _, _ => ()
  | .monoid (_ + 2), false, _, true, _, _ => ()
  | .monoid (_ + 2), true, _, false, _, _ => ()
  | .monoid (_ + 2), true, false, true, _, _ => false
  | .monoid (_ + 2), true, true, true, a, b => a && b

/-- Strict `id_comp_id` law across `FactorState`. -/
theorem id_comp_id : ∀ {s : FactorState} (x : obj s),
    compMor (idMor x) (idMor x) = idMor x
  | .pt, () => rfl
  | .empty, x => Empty.elim x
  | .iso, false => rfl
  | .iso, true => rfl
  | .monoid 0, () => rfl
  | .monoid 1, false => rfl
  | .monoid 1, true => rfl
  | .monoid (_ + 2), false => rfl
  | .monoid (_ + 2), true => rfl

/-- Strict associativity of `FactorState.compMor`. -/
theorem compMor_assoc : ∀ {s : FactorState} {w x y z : obj s}
    (f : obj (hom w x)) (g : obj (hom x y)) (h : obj (hom y z)),
    compMor (compMor f g) h = compMor f (compMor g h)
  | .pt, _, _, _, _, _, _, _ => rfl
  | .empty, w, _, _, _, _, _, _ => Empty.elim w
  | .iso, _, _, _, _, _, _, _ => rfl
  | .monoid 0, _, _, _, _, _, _, _ => rfl
  | .monoid 1, false, false, false, false, _, _, _ => rfl
  | .monoid 1, false, false, false, true, _, _, _ => rfl
  | .monoid 1, false, false, true, true, _, _, _ => rfl
  | .monoid 1, false, true, true, true, _, _, _ => rfl
  | .monoid 1, true, true, true, true, _, _, _ => rfl
  | .monoid 1, true, false, _, _, f, _, _ => Empty.elim f
  | .monoid 1, false, true, false, _, _, g, _ => Empty.elim g
  | .monoid 1, true, true, false, _, _, g, _ => Empty.elim g
  | .monoid 1, false, false, true, false, _, _, h => Empty.elim h
  | .monoid 1, false, true, true, false, _, _, h => Empty.elim h
  | .monoid 1, true, true, true, false, _, _, h => Empty.elim h
  | .monoid (_ + 2), false, _, _, false, _, _, _ => rfl
  | .monoid (_ + 2), false, _, _, true, _, _, _ => rfl
  | .monoid (_ + 2), true, _, _, false, _, _, _ => rfl
  | .monoid (_ + 2), true, false, false, true, _, _, _ => rfl
  | .monoid (_ + 2), true, false, true, true, _, _, _ => rfl
  | .monoid (_ + 2), true, true, false, true, _, _, _ => by simp [compMor]
  | .monoid (_ + 2), true, true, true, true, f, g, h => Bool.and_assoc f g h

/-- Strict left identity of `FactorState.compMor`. -/
theorem idMor_compMor : ∀ {s : FactorState} {x y : obj s} (f : obj (hom x y)),
    compMor (idMor x) f = f
  | .pt, (), (), () => rfl
  | .empty, x, _, _ => Empty.elim x
  | .iso, false, false, () => rfl
  | .iso, false, true, () => rfl
  | .iso, true, false, () => rfl
  | .iso, true, true, () => rfl
  | .monoid 0, (), (), () => rfl
  | .monoid 1, false, false, () => rfl
  | .monoid 1, false, true, () => rfl
  | .monoid 1, true, false, f => Empty.elim f
  | .monoid 1, true, true, () => rfl
  | .monoid (_ + 2), false, false, () => rfl
  | .monoid (_ + 2), false, true, () => rfl
  | .monoid (_ + 2), true, false, () => rfl
  | .monoid (_ + 2), true, true, f => Bool.true_and f

/-- Strict right identity of `FactorState.compMor`. -/
theorem compMor_idMor : ∀ {s : FactorState} {x y : obj s} (f : obj (hom x y)),
    compMor f (idMor y) = f
  | .pt, (), (), () => rfl
  | .empty, x, _, _ => Empty.elim x
  | .iso, false, false, () => rfl
  | .iso, false, true, () => rfl
  | .iso, true, false, () => rfl
  | .iso, true, true, () => rfl
  | .monoid 0, (), (), () => rfl
  | .monoid 1, false, false, () => rfl
  | .monoid 1, false, true, () => rfl
  | .monoid 1, true, false, f => Empty.elim f
  | .monoid 1, true, true, () => rfl
  | .monoid (_ + 2), false, false, () => rfl
  | .monoid (_ + 2), false, true, () => rfl
  | .monoid (_ + 2), true, false, () => rfl
  | .monoid (_ + 2), true, true, f => Bool.and_true f

/-- Finite ordinal rank (`ℕ`) of each `FactorState`: `0` on `.pt`, `.empty`, `.iso`, `.monoid 0`,
and `k` on `.monoid k`. -/
def natRank : FactorState → ℕ
  | .pt => 0
  | .empty => 0
  | .iso => 0
  | .monoid k => k

end FactorState

/-- Restricted-tail family `ℕ → FactorState` that equals `.pt` from some index `N` onward,
modeling infinite products whose tails are contractible (`∏_{j ≥ N} * ≃ *`). -/
abbrev EventuallyPtFamily : Type :=
  { f : ℕ → FactorState // ∃ N : ℕ, ∀ j ≥ N, f j = .pt }

/-- Hom-state factor at coordinate `j : ℕ` between `e^{(m)}` and `e^{(r)}` inside `StepProductQ`:
equals `.monoid (j + 1)` when `j < min m r` and `.pt` when `min m r ≤ j`. -/
def qHomAt (m r j : ℕ) : FactorState :=
  FactorState.hom (s := .monoid (j + 2)) (decide (j < m)) (decide (j < r))

/-- Tail contractibility of `qHomAt m r`: for all `j ≥ min m r`, `qHomAt m r j = .pt`. -/
theorem qHomAt_eq_pt_of_le {m r j : ℕ} (hj : min m r ≤ j) :
    qHomAt m r j = .pt := by
  unfold qHomAt
  rcases min_le_iff.mp hj with hmj | hrj
  · have h₁ : decide (j < m) = false := decide_eq_false (Nat.not_lt.mpr hmj)
    rw [h₁]
    cases decide (j < r) <;> rfl
  · have h₂ : decide (j < r) = false := decide_eq_false (Nat.not_lt.mpr hrj)
    rw [h₂]
    cases decide (j < m) <;> rfl

/-- When `j < min m r`, `qHomAt m r j = .monoid (j + 1)`. -/
theorem qHomAt_eq_monoid_of_lt {m r j : ℕ} (hj : j < min m r) :
    qHomAt m r j = .monoid (j + 1) := by
  unfold qHomAt
  have h₁ : decide (j < m) = true := decide_eq_true (lt_of_lt_of_le hj (min_le_left m r))
  have h₂ : decide (j < r) = true := decide_eq_true (lt_of_lt_of_le hj (min_le_right m r))
  rw [h₁, h₂]
  rfl

/-- Restricted-tail `EventuallyPtFamily` representing `hom_Q(e^{(m)}, e^{(r)})`. -/
def qHomFamily (m r : ℕ) : EventuallyPtFamily :=
  ⟨qHomAt m r, min m r, fun _ hj ↦ qHomAt_eq_pt_of_le hj⟩

/-- Helper reducing `FactorState.hom` to `.pt` when the ambient state equals `.pt`. -/
private theorem factor_hom_eq_pt_of_eq {s : FactorState} (h : s = .pt)
    (x y : FactorState.obj s) : FactorState.hom x y = .pt := by
  subst h
  rfl

/-- Restricted-tail `EventuallyPtFamily` for `hom` inside `.prod f`. -/
def prodHomFamily (f : EventuallyPtFamily)
    (x y : ∀ j : ℕ, FactorState.obj (f.val j)) : EventuallyPtFamily :=
  ⟨fun j ↦ FactorState.hom (x j) (y j),
    let ⟨N, hN⟩ := f.prop
    ⟨N, fun j hj ↦ factor_hom_eq_pt_of_eq (hN j hj) (x j) (y j)⟩⟩

/-- Unified state space `StepState` hosting finite factors (`.factor`), restricted-tail products
(`.prod`), finite `d`-truncation stages (`.qTrunc d`), and the rank-`ω` step-product
counterexample `StepProductQ` (`.qFull`). -/
inductive StepState : Type
  | factor : FactorState → StepState
  | prod : EventuallyPtFamily → StepState
  | qTrunc : ℕ → StepState
  | qFull : StepState

namespace StepState

/-- Underlying `0`-cell type of `StepState`. -/
def stepObj : StepState → Type
  | .factor s => FactorState.obj s
  | .prod f => ∀ j : ℕ, FactorState.obj (f.val j)
  | .qTrunc 0 => Unit
  | .qTrunc (d + 1) => Fin (d + 1)
  | .qFull => ℕ

/-- Hom-state transition on `StepState`. -/
def stepHom : ∀ {s : StepState}, stepObj s → stepObj s → StepState
  | .factor _, x, y => .factor (FactorState.hom x y)
  | .prod f, x, y => .prod (prodHomFamily f x y)
  | .qTrunc 0, _, _ => .factor .pt
  | .qTrunc (_ + 1), a, b => .prod (qHomFamily a.val b.val)
  | .qFull, m, r => .prod (qHomFamily m r)

/-- Identity `1`-morphism on `StepState`. -/
def stepId : ∀ {s : StepState} (x : stepObj s), stepObj (stepHom x x)
  | .factor _, x => FactorState.idMor x
  | .prod _, x => fun j ↦ FactorState.idMor (x j)
  | .qTrunc 0, () => ()
  | .qTrunc (_ + 1), a => fun j ↦ FactorState.idMor (s := .monoid (j + 2)) (decide (j < a.val))
  | .qFull, m => fun j ↦ FactorState.idMor (s := .monoid (j + 2)) (decide (j < m))

/-- Diagrammatic `1`-morphism composition on `StepState`. -/
def stepComp : ∀ {s : StepState} {x y z : stepObj s},
    stepObj (stepHom x y) → stepObj (stepHom y z) → stepObj (stepHom x z)
  | .factor _, _, _, _, f, g => FactorState.compMor f g
  | .prod _, _, _, _, f, g => fun j ↦ FactorState.compMor (f j) (g j)
  | .qTrunc 0, _, _, _, _, _ => ()
  | .qTrunc (_ + 1), _, _, _, f, g =>
      fun j ↦ FactorState.compMor (s := .monoid (j + 2)) (f j) (g j)
  | .qFull, _, _, _, f, g =>
      fun j ↦ FactorState.compMor (s := .monoid (j + 2)) (f j) (g j)

instance instGlobularInfSystem : GlobularInfSystem StepState where
  Obj := stepObj
  hom := stepHom
  idMor := stepId
  compMor := stepComp
  id_comp_id {s} x := by
    cases s with
    | factor _ => exact FactorState.id_comp_id x
    | prod _ =>
      funext j
      exact FactorState.id_comp_id (x j)
    | qTrunc d =>
      cases d with
      | zero => rfl
      | succ d' =>
        funext j
        exact FactorState.id_comp_id (s := .monoid (j + 2)) (decide (j < x.val))
    | qFull =>
      funext j
      exact FactorState.id_comp_id (s := .monoid (j + 2)) (decide (j < x))

/-- Strict associativity of `compMor` on `StepState`. -/
theorem stepComp_assoc : ∀ {s : StepState} {w x y z : Obj s}
    (f : Obj (hom w x)) (g : Obj (hom x y)) (h : Obj (hom y z)),
    compMor (compMor f g) h = compMor f (compMor g h)
  | .factor _, _, _, _, _, f, g, h => FactorState.compMor_assoc f g h
  | .prod _, _, _, _, _, f, g, h => funext fun j ↦ FactorState.compMor_assoc (f j) (g j) (h j)
  | .qTrunc 0, _, _, _, _, _, _, _ => rfl
  | .qTrunc (_ + 1), _, _, _, _, f, g, h =>
      funext fun j ↦ FactorState.compMor_assoc (s := .monoid (j + 2)) (f j) (g j) (h j)
  | .qFull, _, _, _, _, f, g, h =>
      funext fun j ↦ FactorState.compMor_assoc (s := .monoid (j + 2)) (f j) (g j) (h j)

/-- Strict left identity of `compMor` on `StepState`. -/
theorem stepId_comp : ∀ {s : StepState} {x y : Obj s} (f : Obj (hom x y)),
    compMor (idMor x) f = f
  | .factor _, _, _, f => FactorState.idMor_compMor f
  | .prod _, _, _, f => funext fun j ↦ FactorState.idMor_compMor (f j)
  | .qTrunc 0, (), (), () => rfl
  | .qTrunc (_ + 1), _, _, f =>
      funext fun j ↦ FactorState.idMor_compMor (s := .monoid (j + 2)) (f j)
  | .qFull, _, _, f =>
      funext fun j ↦ FactorState.idMor_compMor (s := .monoid (j + 2)) (f j)

/-- Strict right identity of `compMor` on `StepState`. -/
theorem stepComp_id : ∀ {s : StepState} {x y : Obj s} (f : Obj (hom x y)),
    compMor f (idMor y) = f
  | .factor _, _, _, f => FactorState.compMor_idMor f
  | .prod _, _, _, f => funext fun j ↦ FactorState.compMor_idMor (f j)
  | .qTrunc 0, (), (), () => rfl
  | .qTrunc (_ + 1), _, _, f =>
      funext fun j ↦ FactorState.compMor_idMor (s := .monoid (j + 2)) (f j)
  | .qFull, _, _, f =>
      funext fun j ↦ FactorState.compMor_idMor (s := .monoid (j + 2)) (f j)

end StepState

/-- Contractibility of `StepState.factor .pt`. -/
theorem isContractibleState_pt : IsContractibleState (StepState.factor .pt) := by
  refine ⟨fun q ↦ q = StepState.factor .pt, rfl, ?_⟩
  rintro q rfl
  exact ⟨⟨()⟩, inferInstanceAs (Subsingleton Unit), fun _ _ ↦ rfl⟩

/-- `(-1)`-truncation of `StepState.factor .empty`. -/
theorem isMinusOneTruncated_empty : IsMinusOneTruncated (StepState.factor .empty) :=
  ⟨inferInstanceAs (Subsingleton Empty), fun a _ ↦ Empty.elim a⟩

/-- `(-1)`-truncation of `StepState.factor .pt`. -/
theorem isMinusOneTruncated_pt : IsMinusOneTruncated (StepState.factor .pt) :=
  isContractibleState_pt.isMinusOneTruncated

/-- `StepState.factor .pt` is `0`-truncated. -/
theorem isNTruncated_pt : IsNTruncated 0 (StepState.factor .pt) :=
  isContractibleState_pt.isNTruncated_zero

/-- `StepState.factor .empty` is `0`-truncated. -/
theorem isNTruncated_empty : IsNTruncated 0 (StepState.factor .empty) :=
  isMinusOneTruncated_empty.isNTruncated_zero

/-- `StepState.factor (.monoid 0)` is `0`-truncated. -/
theorem isNTruncated_monoid_zero : IsNTruncated 0 (StepState.factor (.monoid 0)) := by
  intro t ht
  have ht' : t = StepState.factor (.monoid 0) ∨ t = StepState.factor .pt := by
    induction ht with
    | refl => exact Or.inl rfl
    | @step q _ x y ih =>
      rcases ih with rfl | rfl <;> exact Or.inr rfl
  rcases ht' with rfl | rfl
  · intro x y f
    cases x; cases y; cases f
    exact IsEquiv.id _
  · intro x y f
    exact isNTruncated_pt.isEquiv_of_zero f

/-- `1`-cell reachability preorder `Reach1 x y` (`x ≼₁ y` iff `Nonempty (Obj (hom x y))`). -/
def Reach1 {S : Type u} [GlobularInfSystem S] {s : S} (x y : Obj s) : Prop :=
  Nonempty (Obj (hom x y))

/-- Reflexivity of `Reach1` via `idMor`. -/
theorem Reach1.refl {S : Type u} [GlobularInfSystem S] {s : S} (x : Obj s) :
    Reach1 x x :=
  ⟨idMor x⟩

/-- Transitivity of `Reach1` via `compMor`. -/
theorem Reach1.trans {S : Type u} [GlobularInfSystem S] {s : S} {x y z : Obj s}
    (hxy : Reach1 x y) (hyz : Reach1 y z) : Reach1 x z :=
  ⟨compMor hxy.some hyz.some⟩

/-- Stock Mathlib `Preorder` instance on `Obj s` induced by `Reach1`. -/
def reach1Preorder {S : Type u} [GlobularInfSystem S] (s : S) : Preorder (Obj s) where
  le := Reach1
  le_refl := Reach1.refl
  le_trans := @Reach1.trans S _ s

/-- `Reach1 x y` coincides with the reflexive-transitive closure of single `1`-morphisms. -/
theorem reach1_iff_reflTransGen {S : Type u} [GlobularInfSystem S] {s : S} {x y : Obj s} :
    Reach1 x y ↔ Relation.ReflTransGen (fun a b : Obj s ↦ Nonempty (Obj (hom a b))) x y := by
  constructor
  · intro h
    exact Relation.ReflTransGen.single h
  · intro h
    induction h with
    | refl => exact Reach1.refl _
    | tail _ hbc ih => exact ih.trans hbc

/-- Mutual `1`-cell reachability (`SameSCC1 x y`: `x` and `y` lie in the same strongly connected
component under `Reach1`). -/
def SameSCC1 {S : Type u} [GlobularInfSystem S] {s : S} (x y : Obj s) : Prop :=
  Reach1 x y ∧ Reach1 y x

/-- `SameSCC1` is an `Equivalence` on `Obj s`. -/
theorem sameSCC1_equivalence {S : Type u} [GlobularInfSystem S] (s : S) :
    Equivalence (@SameSCC1 S _ s) where
  refl x := ⟨Reach1.refl x, Reach1.refl x⟩
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- Walking arrow `[1] = StepState.factor (.monoid 1)` is `1`-truncated (`IsNTruncated 1`). -/
theorem isNTruncated_monoid_one : IsNTruncated 1 (StepState.factor (.monoid 1)) := by
  intro x y
  cases x <;> cases y
  · exact isNTruncated_pt
  · exact isNTruncated_pt
  · exact isNTruncated_empty
  · exact isNTruncated_pt

/-- Walking arrow `[1] = StepState.factor (.monoid 1)` is object-gaunt (`IsObjGaunt`). -/
theorem isObjGaunt_monoid_one : IsObjGaunt (StepState.factor (.monoid 1)) := by
  intro x y h
  cases x <;> cases y
  · rfl
  · rcases h.symm with ⟨g, _⟩
    exact Empty.elim g
  · rcases h with ⟨f, _⟩
    exact Empty.elim f
  · rfl

/-- `[1]`-classifier state correspondence `UpperSetRel s x` for `upperSetClassifier s x`. -/
inductive UpperSetRel {S : Type u} [GlobularInfSystem S] (s : S) (x : Obj s) :
    S → StepState → Type u
  | top : UpperSetRel s x s (StepState.factor (.monoid 1))
  | toPt (t : S) : UpperSetRel s x t (StepState.factor .pt)
  | toEmpty (t : S) (he : IsEmpty (Obj t)) : UpperSetRel s x t (StepState.factor .empty)

/-- Classical indicator `upperSetBool x z` (`decide (x ≼₁ z)`). -/
noncomputable def upperSetBool {S : Type u} [GlobularInfSystem S] {s : S}
    (x z : Obj s) : Bool :=
  @decide (Reach1 x z) (Classical.propDecidable _)

private theorem upperSetBool_eq_true {S : Type u} [GlobularInfSystem S] {s : S}
    {x z : Obj s} (h : Reach1 x z) : upperSetBool x z = true :=
  @decide_eq_true (Reach1 x z) (Classical.propDecidable _) h

private theorem upperSetBool_eq_false {S : Type u} [GlobularInfSystem S] {s : S}
    {x z : Obj s} (h : ¬ Reach1 x z) : upperSetBool x z = false :=
  @decide_eq_false (Reach1 x z) (Classical.propDecidable _) h

private noncomputable def upperSetMapObj {S : Type u} [GlobularInfSystem S]
    (s : S) (x : Obj s) :
    ∀ {s₁ : S} {s₂ : StepState}, UpperSetRel s x s₁ s₂ → Obj s₁ → Obj s₂
  | _, _, .top, z => upperSetBool x z
  | _, _, .toPt _, _ => ()
  | _, _, .toEmpty _ he, z => False.elim (he.false z)

private noncomputable def upperSetMapHom {S : Type u} [GlobularInfSystem S]
    (s : S) (x : Obj s) :
    ∀ {s₁ : S} {s₂ : StepState} (φ : UpperSetRel s x s₁ s₂) (a b : Obj s₁),
      UpperSetRel s x (hom a b)
        (hom (upperSetMapObj s x φ a) (upperSetMapObj s x φ b))
  | _, _, .top, a, b => by
    by_cases hxa : Reach1 x a
    · by_cases hxb : Reach1 x b
      · change UpperSetRel s x (hom a b)
          (hom (s := StepState.factor (.monoid 1)) (upperSetBool x a) (upperSetBool x b))
        rw [upperSetBool_eq_true hxa, upperSetBool_eq_true hxb]
        exact UpperSetRel.toPt (hom a b)
      · change UpperSetRel s x (hom a b)
          (hom (s := StepState.factor (.monoid 1)) (upperSetBool x a) (upperSetBool x b))
        rw [upperSetBool_eq_true hxa, upperSetBool_eq_false hxb]
        exact UpperSetRel.toEmpty (hom a b) ⟨fun f ↦ hxb (hxa.trans ⟨f⟩)⟩
    · by_cases hxb : Reach1 x b
      · change UpperSetRel s x (hom a b)
          (hom (s := StepState.factor (.monoid 1)) (upperSetBool x a) (upperSetBool x b))
        rw [upperSetBool_eq_false hxa, upperSetBool_eq_true hxb]
        exact UpperSetRel.toPt (hom a b)
      · change UpperSetRel s x (hom a b)
          (hom (s := StepState.factor (.monoid 1)) (upperSetBool x a) (upperSetBool x b))
        rw [upperSetBool_eq_false hxa, upperSetBool_eq_false hxb]
        exact UpperSetRel.toPt (hom a b)
  | _, _, .toPt _, _, _ => UpperSetRel.toPt (hom _ _)
  | _, _, .toEmpty _ he, a, _ => False.elim (he.false a)

private theorem upperSetMapId {S : Type u} [GlobularInfSystem S]
    (s : S) (x : Obj s) :
    ∀ {s₁ : S} {s₂ : StepState} (φ : UpperSetRel s x s₁ s₂) (z : Obj s₁),
      upperSetMapObj s x (upperSetMapHom s x φ z z) (idMor z) =
        idMor (upperSetMapObj s x φ z)
  | _, _, .top, z => by
    have hsub : Subsingleton (Obj (hom (s := StepState.factor (.monoid 1))
        (upperSetBool x z) (upperSetBool x z))) := by
      cases upperSetBool x z <;> exact inferInstanceAs (Subsingleton Unit)
    exact hsub.elim _ _
  | _, _, .toPt _, _ => rfl
  | _, _, .toEmpty _ he, z => False.elim (he.false z)

private theorem upperSetMapComp {S : Type u} [GlobularInfSystem S]
    (s : S) (x : Obj s) :
    ∀ {s₁ : S} {s₂ : StepState} (φ : UpperSetRel s x s₁ s₂) {a b c : Obj s₁}
      (f : Obj (hom a b)) (g : Obj (hom b c)),
      upperSetMapObj s x (upperSetMapHom s x φ a c) (compMor f g) =
        compMor (upperSetMapObj s x (upperSetMapHom s x φ a b) f)
          (upperSetMapObj s x (upperSetMapHom s x φ b c) g)
  | _, _, .top, a, _, c, _, _ => by
    have hsub : Subsingleton (Obj (hom (s := StepState.factor (.monoid 1))
        (upperSetBool x a) (upperSetBool x c))) := by
      cases upperSetBool x a <;> cases upperSetBool x c <;>
        first
        | exact inferInstanceAs (Subsingleton Unit)
        | exact inferInstanceAs (Subsingleton Empty)
    exact hsub.elim _ _
  | _, _, .toPt _, _, _, _, _, _ => rfl
  | _, _, .toEmpty _ he, a, _, _, _, _ => False.elim (he.false a)

/-- Principal upper-set classifier functor `χ_x : S → [1]` (`z ↦ decide (x ≼₁ z)`), mapping
`s` to `StepState.factor (.monoid 1)`. -/
noncomputable def upperSetClassifier {S : Type u} [GlobularInfSystem S]
    (s : S) (x : Obj s) : GlobularFunctor S StepState where
  Rel := UpperSetRel s x
  mapObj := upperSetMapObj s x
  mapHom := upperSetMapHom s x
  map_id := upperSetMapId s x
  map_comp := upperSetMapComp s x

/-- Evaluation of `upperSetClassifier s x` on `0`-cells of `s`. -/
theorem upperSetClassifier_mapObj_top {S : Type u} [GlobularInfSystem S]
    (s : S) (x z : Obj s) :
    (upperSetClassifier s x).mapObj UpperSetRel.top z = upperSetBool x z :=
  rfl

/-- Evaluation of `upperSetClassifier s x` at the basepoint `x`: returns `true`. -/
theorem upperSetClassifier_self {S : Type u} [GlobularInfSystem S]
    (s : S) (x : Obj s) :
    (upperSetClassifier s x).mapObj UpperSetRel.top x = true :=
  upperSetBool_eq_true (Reach1.refl x)

/-- Universal factorization witness for `TruncReflection`. -/
structure TruncFactor {S : Type u} [GlobularInfSystem S] (s : S)
    {Target : Type u₁} [GlobularInfSystem Target] (targetState : Target)
    (unit : GlobularFunctor S Target) (unitRel : unit.Rel s targetState)
    {D : Type v} [GlobularInfSystem D] (d : D)
    (F : GlobularFunctor S D) (φ : F.Rel s d) where
  /-- Factored functor `Target → D`. -/
  Fbar : GlobularFunctor Target D
  /-- State correspondence witness `targetState ↦ d`. -/
  ψ : Fbar.Rel targetState d
  /-- Commutativity up to `ObjEquivRel` on `0`-cells. -/
  commutes : ∀ x : Obj s, ObjEquivRel (Fbar.mapObj ψ (unit.mapObj unitRel x)) (F.mapObj φ x)

/-- Universal `n`-truncation reflection `ℓ_n : s → Target` (`IsNTruncated n Target`) factoring
every `n`-truncated target `D : Type v` up to `ObjEquivRel`. -/
structure TruncReflection (n : ℕ) {S : Type u} [GlobularInfSystem S] (s : S) where
  /-- Target state space hosting the reflection state. -/
  Target : Type u₁
  /-- `GlobularInfSystem` instance on `Target`. -/
  [instTarget : GlobularInfSystem Target]
  /-- Reflected `n`-truncated state `ℓ_n(s) : Target`. -/
  targetState : Target
  /-- Proof that `targetState` is `n`-truncated. -/
  isTruncated : IsNTruncated n targetState
  /-- Reflection unit functor `ℓ_n : S → Target`. -/
  unit : GlobularFunctor S Target
  /-- State correspondence witness for `s ↦ targetState`. -/
  unitRel : unit.Rel s targetState
  /-- Universal factorization through `unit` for every `n`-truncated target `d : D`. -/
  factor : ∀ {D : Type v} [GlobularInfSystem D] {d : D},
    IsNTruncated n d → ∀ (F : GlobularFunctor S D) (φ : F.Rel s d),
    TruncFactor s targetState unit unitRel d F φ

attribute [instance] TruncReflection.instTarget

/-- Postnikov tower of universal `(n + 1)`-truncation reflections (`n : ℕ`, truncation level
`n + 1`) over `s : S` equipped with compatible bonding functors `bond n : Target_{n+1} → Target_n`.
-/
structure PostnikovReflectionSystem {S : Type u} [GlobularInfSystem S] (s : S) where
  /-- Universal `(n + 1)`-truncation reflection at stage `n : ℕ`. -/
  level : ∀ n : ℕ, TruncReflection.{u, u₁, v} (n + 1) s
  /-- Bonding functor from stage `n + 1` (`π_{\le n+2}`) to stage `n` (`π_{\le n+1}`). -/
  bond : ∀ n : ℕ, GlobularFunctor (level (n + 1)).Target (level n).Target
  /-- State correspondence witness for `bond n`. -/
  bondRel : ∀ n : ℕ, (bond n).Rel (level (n + 1)).targetState (level n).targetState
  /-- Compatibility of `bond n` with the reflection units up to `ObjEquivRel`. -/
  bond_compat : ∀ (n : ℕ) (x : Obj s),
    ObjEquivRel
      ((bond n).mapObj (bondRel n) ((level (n + 1)).unit.mapObj (level (n + 1)).unitRel x))
      ((level n).unit.mapObj (level n).unitRel x)

/-- Compatibility of an object sequence `x : ℕ → Obj s` in `PostnikovReflectionSystem` via
bonding transitions equals single-level equivalence `ℓ_{n+1}(x_{n+1}) ~ ℓ_{n+1}(x_n)`. -/
theorem PostnikovReflectionSystem.bond_compat_iff {S : Type u} [GlobularInfSystem S] {s : S}
    (P : PostnikovReflectionSystem.{u, u₁, v} s) (x : ℕ → Obj s) (n : ℕ) :
    ObjEquivRel
        ((P.bond n).mapObj (P.bondRel n)
          ((P.level (n + 1)).unit.mapObj (P.level (n + 1)).unitRel (x (n + 1))))
        ((P.level n).unit.mapObj (P.level n).unitRel (x n)) ↔
      ObjEquivRel
        ((P.level n).unit.mapObj (P.level n).unitRel (x (n + 1)))
        ((P.level n).unit.mapObj (P.level n).unitRel (x n)) := by
  have hc := P.bond_compat n (x (n + 1))
  exact ⟨fun h ↦ hc.symm.trans h, fun h ↦ hc.trans h⟩

/-- **Theorem 12B(1) — `[1]`-Classifier SCC Trapping (`theorem12B_classifier_scc_trapping`):**
For every `1 ≤ n` and every universal `n`-truncation reflection `R : TruncReflection n s`,
equivalence of reflected objects `ObjEquivRel (ℓ_n x) (ℓ_n y)` forces `x` and `y` to lie in the
same `1`-cell strongly connected component (`SameSCC1 x y`). -/
theorem theorem12B_classifier_scc_trapping {S : Type u} [GlobularInfSystem S] {s : S}
    {n : ℕ} (hn : 1 ≤ n) (R : TruncReflection.{u, u₁, 0} n s) {x y : Obj s}
    (hxy : ObjEquivRel (R.unit.mapObj R.unitRel x) (R.unit.mapObj R.unitRel y)) :
    SameSCC1 x y := by
  have reach_of_equiv : ∀ a b : Obj s,
      ObjEquivRel (R.unit.mapObj R.unitRel a) (R.unit.mapObj R.unitRel b) → Reach1 a b := by
    intro a b hab
    have htrunc : IsNTruncated n (StepState.factor (.monoid 1)) :=
      isNTruncated_monoid_one.mono hn
    rcases R.factor htrunc (upperSetClassifier s a) UpperSetRel.top with ⟨Fbar, ψ, hcomm⟩
    have h1 : ObjEquivRel
        (Fbar.mapObj ψ (R.unit.mapObj R.unitRel a))
        (Fbar.mapObj ψ (R.unit.mapObj R.unitRel b)) :=
      Fbar.map_objEquivRel ψ hab
    have h2 : ObjEquivRel
        ((upperSetClassifier s a).mapObj UpperSetRel.top a)
        ((upperSetClassifier s a).mapObj UpperSetRel.top b) :=
      (hcomm a).symm.trans (h1.trans (hcomm b))
    have heq :
        ((upperSetClassifier s a).mapObj UpperSetRel.top a) =
        ((upperSetClassifier s a).mapObj UpperSetRel.top b) :=
      isObjGaunt_monoid_one.objEquivRel_eq.mp h2
    rw [upperSetClassifier_self, upperSetClassifier_mapObj_top] at heq
    exact @of_decide_eq_true (Reach1 a b) (Classical.propDecidable _) heq.symm
  exact ⟨reach_of_equiv x y hxy, reach_of_equiv y x hxy.symm⟩

/-- **Theorem 12B(1) Tower Corollary (`theorem12B_tower_trapped_in_single_scc`):**
Every Postnikov-compatible object sequence `x : ℕ → Obj s` in a `PostnikovReflectionSystem s` is
trapped inside a single `1`-cell strongly connected component (`∀ n, SameSCC1 (x n) (x 0)`). -/
theorem theorem12B_tower_trapped_in_single_scc {S : Type u} [GlobularInfSystem S] {s : S}
    (P : PostnikovReflectionSystem.{u, u₁, 0} s) (x : ℕ → Obj s)
    (hcompat : ∀ n : ℕ, ObjEquivRel
      ((P.level n).unit.mapObj (P.level n).unitRel (x (n + 1)))
      ((P.level n).unit.mapObj (P.level n).unitRel (x n))) :
    ∀ n : ℕ, SameSCC1 (x n) (x 0) := by
  intro n
  induction n with
  | zero => exact (sameSCC1_equivalence s).refl (x 0)
  | succ k ih =>
    have hscc : SameSCC1 (x (k + 1)) (x k) :=
      theorem12B_classifier_scc_trapping (Nat.le_add_left 1 k) (P.level k) (hcompat k)
    exact (sameSCC1_equivalence s).trans hscc ih

/-- Bonding-formulation corollary of `theorem12B_tower_trapped_in_single_scc`. -/
theorem theorem12B_bond_tower_trapped_in_single_scc {S : Type u} [GlobularInfSystem S] {s : S}
    (P : PostnikovReflectionSystem.{u, u₁, 0} s) (x : ℕ → Obj s)
    (hcompat : ∀ n : ℕ, ObjEquivRel
      ((P.bond n).mapObj (P.bondRel n)
        ((P.level (n + 1)).unit.mapObj (P.level (n + 1)).unitRel (x (n + 1))))
      ((P.level n).unit.mapObj (P.level n).unitRel (x n))) :
    ∀ n : ℕ, SameSCC1 (x n) (x 0) :=
  theorem12B_tower_trapped_in_single_scc P x
    (fun n ↦ (P.bond_compat_iff x n).mp (hcompat n))

/-- `1`-acyclic state (`IsOneAcyclic s`): mutual `1`-cell reachability `x ≼₁ y ∧ y ≼₁ x` forces
object equivalence `ObjEquivRel x y`. -/
def IsOneAcyclic {S : Type u} [GlobularInfSystem S] (s : S) : Prop :=
  ∀ ⦃x y : Obj s⦄, Reach1 x y → Reach1 y x → ObjEquivRel x y

/-- **Theorem 12C(3) — Antisymmetric Postnikov Completeness
(`theorem12C_antisymmetric_postnikov_completeness`):**
If `IsOneAcyclic s` holds, then every Postnikov-compatible object sequence `x : ℕ → Obj s`
satisfies `∀ n, ObjEquivRel (x n) (x 0)` (and `∀ n, x n = x 0` whenever `IsObjGaunt s`). -/
theorem theorem12C_antisymmetric_postnikov_completeness {S : Type u} [GlobularInfSystem S]
    {s : S} (hacyc : IsOneAcyclic s) (P : PostnikovReflectionSystem.{u, u₁, 0} s)
    (x : ℕ → Obj s)
    (hcompat : ∀ n : ℕ, ObjEquivRel
      ((P.level n).unit.mapObj (P.level n).unitRel (x (n + 1)))
      ((P.level n).unit.mapObj (P.level n).unitRel (x n))) :
    (∀ n : ℕ, ObjEquivRel (x n) (x 0)) ∧
      (IsObjGaunt s → ∀ n : ℕ, x n = x 0) := by
  have h1 : ∀ n : ℕ, ObjEquivRel (x n) (x 0) := fun n ↦
    let h := theorem12B_tower_trapped_in_single_scc P x hcompat n
    hacyc h.1 h.2
  exact ⟨h1, fun hg n ↦ hg.objEquivRel_eq.mp (h1 n)⟩

/-! ## Section 3: Part (b) — Inductive Gaunt Absorbing-Monoid Tower (`AbsorbingLaliMonoid`,
`ℳ_k`, `𝒜_k`) -/

/-- The inductive gaunt commutative absorbing monoid `𝒜_k := ℳ_{k+1}` (`k ≥ 1`, and `ℳ_1 = [1]` at
`k = 0`) modeled inside `StepState`. -/
abbrev AbsorbingLaliMonoid (k : ℕ) : StepState :=
  StepState.factor (.monoid (k + 1))

/-- Canonical forward `1`-morphism `false → true` (`e_{k+1} → 1_{k+1}`) inside
`AbsorbingLaliMonoid k`. -/
def monoidFwdArrow (k : ℕ) :
    Obj (hom (s := AbsorbingLaliMonoid k) (false : Bool) (true : Bool)) :=
  match k with
  | 0 => ()
  | _ + 1 => ()

/-- Canonical reverse `1`-morphism `true → false` (`1_{k+2} → e_{k+2}`) inside
`StepState.factor (.monoid (k + 2))`. -/
def monoidRevArrow (k : ℕ) :
    Obj (hom (s := StepState.factor (.monoid (k + 2))) (true : Bool) (false : Bool)) :=
  ()

/-- Stock Mathlib-compatible carrier wrapper for `Obj (StepState.factor (.monoid k))` supporting
`CommMonoid`, `SemilatticeInf`, and `OrderBot`. -/
structure AbsorbingMonoidCarrier (k : ℕ) : Type where
  /-- Underlying `0`-cell in `StepState.factor (.monoid k)`. -/
  val : Obj (StepState.factor (.monoid k))

/-- Extensionality for `AbsorbingMonoidCarrier k`. -/
@[ext]
theorem AbsorbingMonoidCarrier.ext {k : ℕ} {a b : AbsorbingMonoidCarrier k}
    (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

/-- `DecidableEq` instance on `AbsorbingMonoidCarrier k`. -/
instance instDecidableEqAbsorbingMonoidCarrier (k : ℕ) :
    DecidableEq (AbsorbingMonoidCarrier k) :=
  match k with
  | 0 => fun a b ↦ isTrue (by rcases a with ⟨⟨⟩⟩; rcases b with ⟨⟨⟩⟩; rfl)
  | _ + 1 => fun ⟨va⟩ ⟨vb⟩ ↦
    match Bool.decEq va vb with
    | isTrue h => isTrue (by cases h; rfl)
    | isFalse h => isFalse fun hab ↦ h (congrArg AbsorbingMonoidCarrier.val hab)

/-- Stock `CommMonoid` instance on `AbsorbingMonoidCarrier k` (`1_k = true`, `m_k = Bool.and` for
`k ≥ 1`, and `Unit` for `k = 0`). -/
instance instCommMonoidAbsorbingMonoidCarrier (k : ℕ) :
    CommMonoid (AbsorbingMonoidCarrier k) where
  mul a b :=
    match k with
    | 0 => ⟨()⟩
    | _ + 1 => ⟨a.val && b.val⟩
  one :=
    match k with
    | 0 => ⟨()⟩
    | _ + 1 => ⟨true⟩
  mul_assoc a b c := by
    cases k with
    | zero => exact AbsorbingMonoidCarrier.ext rfl
    | succ _ => exact AbsorbingMonoidCarrier.ext (Bool.and_assoc a.val b.val c.val)
  one_mul a := by
    cases k with
    | zero => exact AbsorbingMonoidCarrier.ext rfl
    | succ _ => exact AbsorbingMonoidCarrier.ext (Bool.true_and a.val)
  mul_one a := by
    cases k with
    | zero => exact AbsorbingMonoidCarrier.ext rfl
    | succ _ => exact AbsorbingMonoidCarrier.ext (Bool.and_true a.val)
  mul_comm a b := by
    cases k with
    | zero => exact AbsorbingMonoidCarrier.ext rfl
    | succ _ => exact AbsorbingMonoidCarrier.ext (Bool.and_comm a.val b.val)

/-- Stock `SemilatticeInf` instance on `AbsorbingMonoidCarrier k` whose infimum coincides with
the absorbing monoid multiplication `(· * ·)`. -/
instance instSemilatticeInfAbsorbingMonoidCarrier (k : ℕ) :
    SemilatticeInf (AbsorbingMonoidCarrier k) :=
  match k with
  | 0 =>
    { le := fun _ _ ↦ True
      inf := fun a b ↦ a * b
      le_refl := fun _ ↦ trivial
      le_trans := fun _ _ _ _ _ ↦ trivial
      le_antisymm := fun a b _ _ ↦ by rcases a with ⟨⟨⟩⟩; rcases b with ⟨⟨⟩⟩; rfl
      inf_le_left := fun _ _ ↦ trivial
      inf_le_right := fun _ _ ↦ trivial
      le_inf := fun _ _ _ _ _ ↦ trivial }
  | _ + 1 =>
    { le := fun a b ↦ LE.le (α := Bool) a.val b.val
      inf := fun a b ↦ a * b
      le_refl := fun _ ↦ le_rfl (α := Bool)
      le_trans := fun _ _ _ hab hbc ↦ le_trans (α := Bool) hab hbc
      le_antisymm := fun _ _ hab hba ↦
        AbsorbingMonoidCarrier.ext (le_antisymm (α := Bool) hab hba)
      inf_le_left := fun a b ↦ by
        change LE.le (α := Bool) (a.val && b.val) a.val
        cases (a.val : Bool) <;> cases (b.val : Bool) <;> decide
      inf_le_right := fun a b ↦ by
        change LE.le (α := Bool) (a.val && b.val) b.val
        cases (a.val : Bool) <;> cases (b.val : Bool) <;> decide
      le_inf := fun ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hac ↦ by
        dsimp only at hab hac ⊢
        rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;>
          first
          | exact le_rfl (α := Bool)
          | exact Bool.false_le _
          | exact absurd hab (by decide : ¬ LE.le (α := Bool) true false)
          | exact absurd hac (by decide : ¬ LE.le (α := Bool) true false) }

/-- Stock `OrderBot` instance on `AbsorbingMonoidCarrier k` with absorbing bottom element
`⊥ = ⟨false⟩` (`e_k`) for `k ≥ 1` and `⟨()⟩` for `k = 0`. -/
instance instOrderBotAbsorbingMonoidCarrier (k : ℕ) :
    OrderBot (AbsorbingMonoidCarrier k) :=
  match k with
  | 0 =>
    { bot := ⟨()⟩
      bot_le := fun _ ↦ trivial }
  | _ + 1 =>
    { bot := ⟨false⟩
      bot_le := fun a ↦ Bool.false_le a.val }

/-- State correspondence relation for the commutative absorbing multiplication functor
`mulFunctor : StepState × StepState → StepState`. -/
inductive MulRel : StepState × StepState → StepState → Type
  | monoid (k : ℕ) : MulRel (StepState.factor (.monoid k), StepState.factor (.monoid k))
      (StepState.factor (.monoid k))
  | toPt (s₁ s₂ : StepState) : MulRel (s₁, s₂) (StepState.factor .pt)
  | emptyL (s₂ : StepState) : MulRel (StepState.factor .empty, s₂) (StepState.factor .empty)
  | emptyR (s₁ : StepState) : MulRel (s₁, StepState.factor .empty) (StepState.factor .empty)

private def mulMapObj :
    ∀ {s₁ : StepState × StepState} {s₂ : StepState}, MulRel s₁ s₂ → Obj s₁ → Obj s₂
  | _, _, .monoid 0, _ => ()
  | _, _, .monoid (_ + 1), p => p.1 && p.2
  | _, _, .toPt _ _, _ => ()
  | _, _, .emptyL _, p => Empty.elim p.1
  | _, _, .emptyR _, p => Empty.elim p.2

private def mulMapHom :
    ∀ {s₁ : StepState × StepState} {s₂ : StepState} (φ : MulRel s₁ s₂) (x y : Obj s₁),
      MulRel (hom x y) (hom (mulMapObj φ x) (mulMapObj φ y))
  | _, _, .monoid 0, _, _ => .toPt _ _
  | _, _, .monoid 1, (false, _), (false, _) => .toPt _ _
  | _, _, .monoid 1, (false, _), (true, false) => .toPt _ _
  | _, _, .monoid 1, (false, _), (true, true) => .toPt _ _
  | _, _, .monoid 1, (true, false), (false, _) => .toPt _ _
  | _, _, .monoid 1, (true, false), (true, false) => .toPt _ _
  | _, _, .monoid 1, (true, false), (true, true) => .toPt _ _
  | _, _, .monoid 1, (true, true), (false, _) => .emptyL _
  | _, _, .monoid 1, (true, true), (true, false) => .emptyR _
  | _, _, .monoid 1, (true, true), (true, true) => .toPt _ _
  | _, _, .monoid (k + 2), (false, _), (false, _) => .toPt _ _
  | _, _, .monoid (k + 2), (false, _), (true, false) => .toPt _ _
  | _, _, .monoid (k + 2), (false, _), (true, true) => .toPt _ _
  | _, _, .monoid (k + 2), (true, false), (false, _) => .toPt _ _
  | _, _, .monoid (k + 2), (true, false), (true, false) => .toPt _ _
  | _, _, .monoid (k + 2), (true, false), (true, true) => .toPt _ _
  | _, _, .monoid (k + 2), (true, true), (false, _) => .toPt _ _
  | _, _, .monoid (k + 2), (true, true), (true, false) => .toPt _ _
  | _, _, .monoid (k + 2), (true, true), (true, true) => .monoid (k + 1)
  | _, _, .toPt _ _, _, _ => .toPt _ _
  | _, _, .emptyL _, x, _ => Empty.elim x.1
  | _, _, .emptyR _, x, _ => Empty.elim x.2

private theorem mulMapId :
    ∀ {s₁ : StepState × StepState} {s₂ : StepState} (φ : MulRel s₁ s₂) (x : Obj s₁),
      mulMapObj (mulMapHom φ x x) (idMor x) = idMor (mulMapObj φ x)
  | _, _, .monoid 0, _ => rfl
  | _, _, .monoid 1, (false, false) => rfl
  | _, _, .monoid 1, (false, true) => rfl
  | _, _, .monoid 1, (true, false) => rfl
  | _, _, .monoid 1, (true, true) => rfl
  | _, _, .monoid (_ + 2), (false, false) => rfl
  | _, _, .monoid (_ + 2), (false, true) => rfl
  | _, _, .monoid (_ + 2), (true, false) => rfl
  | _, _, .monoid (k + 2), (true, true) => by cases k <;> rfl
  | _, _, .toPt _ _, _ => rfl
  | _, _, .emptyL _, x => Empty.elim x.1
  | _, _, .emptyR _, x => Empty.elim x.2

private theorem mulMapComp :
    ∀ {s₁ : StepState × StepState} {s₂ : StepState} (φ : MulRel s₁ s₂)
      {x y z : Obj s₁} (f : Obj (hom x y)) (g : Obj (hom y z)),
      mulMapObj (mulMapHom φ x z) (compMor f g) =
        compMor (mulMapObj (mulMapHom φ x y) f) (mulMapObj (mulMapHom φ y z) g)
  | _, _, .monoid 0, _, _, _, _, _ => rfl
  | _, _, .monoid 1, (a₁, a₂), (b₁, b₂), (c₁, c₂), f, g => by
    cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> cases c₁ <;> cases c₂
    all_goals
      first
      | exact Empty.elim f.1
      | exact Empty.elim f.2
      | exact Empty.elim g.1
      | exact Empty.elim g.2
      | rfl
  | _, _, .monoid (k + 2), (a₁, a₂), (b₁, b₂), (c₁, c₂), f, g => by
    cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> cases c₁ <;> cases c₂
    all_goals
      first
      | rfl
      | (rcases f with ⟨f₁, f₂⟩; rcases g with ⟨g₁, g₂⟩
         cases k <;> cases f₁ <;> cases f₂ <;> cases g₁ <;> cases g₂ <;> rfl)
  | _, _, .toPt _ _, _, _, _, _, _ => rfl
  | _, _, .emptyL _, x, _, _, _, _ => Empty.elim x.1
  | _, _, .emptyR _, x, _, _, _, _ => Empty.elim x.2

/-- Higher globular commutative absorbing monoid multiplication functor
`mulFunctor : GlobularFunctor (StepState × StepState) StepState` realizing `m_k` on
`(.monoid k, .monoid k) ↦ .monoid k` across all `0`-cells and higher cells. -/
def mulFunctor : GlobularFunctor (StepState × StepState) StepState where
  Rel := MulRel
  mapObj := mulMapObj
  mapHom := mulMapHom
  map_id := mulMapId
  map_comp := mulMapComp

/-- Strict associativity, commutativity, unit `1_k = true`, and absorbing element `e_k = false` on
`0`-cells for `mulFunctor` on `.monoid (k + 1)`. -/
theorem mulFunctor_monoid_laws (k : ℕ) (a b c : Obj (StepState.factor (.monoid (k + 1)))) :
    let φ : mulFunctor.Rel
        (StepState.factor (.monoid (k + 1)), StepState.factor (.monoid (k + 1)))
        (StepState.factor (.monoid (k + 1))) := MulRel.monoid (k + 1)
    let mul0 (u v : Obj (StepState.factor (.monoid (k + 1)))) :=
      mulFunctor.mapObj φ (u, v)
    (mul0 (mul0 a b) c = mul0 a (mul0 b c)) ∧
      (mul0 a b = mul0 b a) ∧
      (mul0 true a = a) ∧
      (mul0 a true = a) ∧
      (mul0 false a = false) ∧
      (mul0 a false = false) :=
  ⟨Bool.and_assoc a b c, Bool.and_comm a b, Bool.true_and a, Bool.and_true a,
    Bool.false_and a, Bool.and_false a⟩

/-- Higher-cell strict absorption of `e_{k+2} = false` and unit `1_{k+2} = true` inside
`.monoid (k + 2)` under both diagrammatic composition and `mulFunctor`. -/
theorem monoid_succ_higher_absorption (k : ℕ)
    (α : Obj (hom (s := StepState.factor (.monoid (k + 2))) (true : Bool) (true : Bool))) :
    let φ1 : mulFunctor.Rel
        (StepState.factor (.monoid (k + 1)), StepState.factor (.monoid (k + 1)))
        (StepState.factor (.monoid (k + 1))) := MulRel.monoid (k + 1)
    let mul1 (u v : Obj (StepState.factor (.monoid (k + 1)))) :=
      mulFunctor.mapObj φ1 (u, v)
    let f_k :
        Obj (hom (s := StepState.factor (.monoid (k + 2))) (false : Bool) (true : Bool)) := ()
    let g_k :
        Obj (hom (s := StepState.factor (.monoid (k + 2))) (true : Bool) (false : Bool)) := ()
    let zero1 :
        Obj (hom (s := StepState.factor (.monoid (k + 2))) (true : Bool) (true : Bool)) := false
    compMor g_k f_k = (false : Bool) ∧
      compMor f_k g_k = idMor (s := StepState.factor (.monoid (k + 2))) false ∧
      compMor α zero1 = zero1 ∧
      compMor zero1 α = zero1 ∧
      mul1 (false : Bool) α = (false : Bool) ∧
      mul1 α (false : Bool) = (false : Bool) ∧
      mul1 (true : Bool) α = α :=
  ⟨rfl, rfl, Bool.and_false α, Bool.false_and α,
    Bool.false_and α, Bool.and_false α, Bool.true_and α⟩

/-- State correspondence witness for the basepoint inclusion
`.factor .pt → .factor (.monoid (k + 1))`. -/
inductive MonoidIncRel (k : ℕ) : StepState → StepState → Type
  | base : MonoidIncRel k (StepState.factor .pt) (StepState.factor (.monoid (k + 1)))
  | pt : MonoidIncRel k (StepState.factor .pt) (StepState.factor .pt)

/-- `0`-cell mapping of the basepoint inclusion `() ↦ false` (`e_{k+1}`) into `.monoid (k + 1)`.
-/
abbrev monoidLeftObj (k : ℕ) :
    ∀ {s₁ s₂ : StepState}, MonoidIncRel k s₁ s₂ → Obj s₁ → Obj s₂
  | _, _, .base, _ => false
  | _, _, .pt, _ => ()

private def monoidLeftHom :
    ∀ (k : ℕ) {s₁ s₂ : StepState} (φ : MonoidIncRel k s₁ s₂) (x y : Obj s₁),
      MonoidIncRel k (hom x y) (hom (monoidLeftObj k φ x) (monoidLeftObj k φ y))
  | 0, _, _, .base, (), () => .pt
  | _ + 1, _, _, .base, (), () => .pt
  | _, _, _, .pt, (), () => .pt

/-- Left inclusion simulation `.factor .pt → .factor (.monoid (k + 1))` sending `() ↦ false`
(`e_{k+1}`). -/
def monoidLeftSim (k : ℕ) : GlobularSimulation StepState StepState where
  Rel := MonoidIncRel k
  mapObj := monoidLeftObj k
  mapHom := monoidLeftHom k

/-- State correspondence witness for terminal collapse `s → .factor .pt`. -/
inductive TerminalRel : StepState → StepState → Type
  | toPt (s : StepState) : TerminalRel s (StepState.factor .pt)

private def stepTerminalObj :
    ∀ {s₁ s₂ : StepState}, TerminalRel s₁ s₂ → Obj s₁ → Obj s₂
  | _, _, .toPt _, _ => ()

private def stepTerminalHom :
    ∀ {s₁ s₂ : StepState} (φ : TerminalRel s₁ s₂) (x y : Obj s₁),
      TerminalRel (hom x y) (hom (stepTerminalObj φ x) (stepTerminalObj φ y))
  | _, _, .toPt _, x, y => .toPt (hom x y)

/-- Terminal collapse simulation `s → .factor .pt`. -/
def stepTerminalSim : GlobularSimulation StepState StepState where
  Rel := TerminalRel
  mapObj := stepTerminalObj
  mapHom := stepTerminalHom

/-- Concrete `LaliRetraction` exhibiting `{e_{k+1}}` (`StepState.factor .pt`) as a Lali retract
of `AbsorbingLaliMonoid k` (`StepState.factor (.monoid (k + 1))`). -/
def monoidLali (k : ℕ) :
    LaliRetraction (StepState.factor .pt) (AbsorbingLaliMonoid k) where
  L := monoidLeftSim k
  R := stepTerminalSim
  relL := MonoidIncRel.base
  relR := TerminalRel.toPt _
  retract_left_inv u := by
    cases u
    rfl
  counit x := by
    cases k <;> cases (x : Bool) <;> exact ()
  counit_left_isEquiv u := by
    cases u
    cases k with
    | zero => exact IsEquiv.id (s := StepState.factor (.monoid 1)) false
    | succ n => exact IsEquiv.id (s := StepState.factor (.monoid (n + 2))) false

/-- Every `StepState.factor .pt` is hereditarily gaunt. -/
theorem isHereditarilyGaunt_pt : IsHereditarilyGaunt (StepState.factor .pt) := by
  intro t ht
  have hpt : t = StepState.factor .pt := by
    induction ht with
    | refl => rfl
    | @step q _ x y ih => subst ih; rfl
  subst hpt
  intro x y _
  cases x; cases y; rfl

/-- Every `StepState.factor .empty` is hereditarily gaunt. -/
theorem isHereditarilyGaunt_empty : IsHereditarilyGaunt (StepState.factor .empty) := by
  intro t ht
  have hemp : t = StepState.factor .empty := by
    induction ht with
    | refl => rfl
    | @step q _ x _ ih => subst ih; exact Empty.elim x
  subst hemp
  intro x _ _
  exact Empty.elim x

/-- Joint inductive proof of `¬ ObjEquiv false true` and `IsHereditarilyGaunt` on
`AbsorbingLaliMonoid k = .factor (.monoid (k + 1))`. -/
private theorem monoid_succ_gaunt_aux (k : ℕ) :
    ¬ ObjEquiv (s := AbsorbingLaliMonoid k) false true ∧
      IsHereditarilyGaunt (AbsorbingLaliMonoid k) := by
  induction k with
  | zero =>
    have hnot : ¬ ObjEquiv (s := AbsorbingLaliMonoid 0) false true := by
      rintro ⟨_, hf⟩
      rcases hf.exists_inv with ⟨g, _⟩
      exact Empty.elim g
    have hg : IsObjGaunt (AbsorbingLaliMonoid 0) := by
      intro x y hxy
      cases x <;> cases y
      · rfl
      · exact False.elim (hnot hxy)
      · exact False.elim (hnot hxy.symm)
      · rfl
    refine ⟨hnot, isHereditarilyGaunt_of_hom hg fun x y ↦ ?_⟩
    cases x <;> cases y
    · exact isHereditarilyGaunt_pt
    · exact isHereditarilyGaunt_pt
    · exact isHereditarilyGaunt_empty
    · exact isHereditarilyGaunt_pt
  | succ k ih =>
    have hnot : ¬ ObjEquiv (s := AbsorbingLaliMonoid (k + 1)) false true := by
      rintro ⟨_, hf⟩
      cases hf with
      | mk _ _ _ ε _ hε => exact ih.1 ⟨ε, hε⟩
    have hg : IsObjGaunt (AbsorbingLaliMonoid (k + 1)) := by
      intro x y hxy
      cases x <;> cases y
      · rfl
      · exact False.elim (hnot hxy)
      · exact False.elim (hnot hxy.symm)
      · rfl
    refine ⟨hnot, isHereditarilyGaunt_of_hom hg fun x y ↦ ?_⟩
    cases x <;> cases y
    · exact isHereditarilyGaunt_pt
    · exact isHereditarilyGaunt_pt
    · exact isHereditarilyGaunt_pt
    · exact ih.2

/-- Basepoint `0_k = false` and unit `1_k = true` are non-equivalent in
`AbsorbingLaliMonoid k = .factor (.monoid (k + 1))`. -/
theorem not_objEquiv_monoid_succ (k : ℕ) :
    ¬ ObjEquiv (s := AbsorbingLaliMonoid k) false true :=
  (monoid_succ_gaunt_aux k).1

/-- Every `StepState.factor (.monoid k)` is hereditarily gaunt (`IsHereditarilyGaunt`). -/
theorem isHereditarilyGaunt_monoid (k : ℕ) :
    IsHereditarilyGaunt (StepState.factor (.monoid k)) := by
  cases k with
  | zero =>
    refine isHereditarilyGaunt_of_hom (fun x y _ ↦ ?_) fun _ _ ↦ isHereditarilyGaunt_pt
    cases x; cases y; rfl
  | succ k' =>
    exact (monoid_succ_gaunt_aux k').2

/-- Basepoint hom-state `hom false false` inside `AbsorbingLaliMonoid k` is contractible. -/
theorem isContractibleState_calA_baseHom (k : ℕ) :
    IsContractibleState (hom (s := AbsorbingLaliMonoid k) (false : Bool) (false : Bool)) := by
  cases k <;> exact isContractibleState_pt

/-- Exact upper truncation dimension of `.monoid k`: `IsNTruncated k (.factor (.monoid k))`. -/
theorem isNTruncated_monoid (k : ℕ) :
    IsNTruncated k (StepState.factor (.monoid k)) := by
  induction k with
  | zero => exact isNTruncated_monoid_zero
  | succ k ih =>
    intro x y
    cases k with
    | zero =>
      cases x <;> cases y
      · exact isNTruncated_pt
      · exact isNTruncated_pt
      · exact isNTruncated_empty
      · exact isNTruncated_pt
    | succ k' =>
      cases x <;> cases y
      · exact isNTruncated_pt.mono (Nat.zero_le (k' + 1))
      · exact isNTruncated_pt.mono (Nat.zero_le (k' + 1))
      · exact isNTruncated_pt.mono (Nat.zero_le (k' + 1))
      · exact ih

/-- Exact lower truncation bound on `AbsorbingLaliMonoid k = .factor (.monoid (k + 1))`:
`¬ IsNTruncated k (.factor (.monoid (k + 1)))`. -/
theorem not_isNTruncated_monoid_pred (k : ℕ) :
    ¬ IsNTruncated k (AbsorbingLaliMonoid k) := by
  induction k with
  | zero =>
    intro h0
    exact not_objEquiv_monoid_succ 0 ⟨monoidFwdArrow 0, h0.isEquiv_of_zero (monoidFwdArrow 0)⟩
  | succ k ih =>
    intro hk
    exact ih (hk true true)

/-- Core inductive truncation-collapse theorem for `AbsorbingLaliMonoid k` at any target
dimension `n ≤ k` (`1 ≤ k`): every `GlobularFunctor` from `AbsorbingLaliMonoid k` into an
`n`-truncated state `d : D` collapses `monoidFwdArrow k` to an equivalence and forces
`ObjEquiv (F false) (F true)`. -/
theorem absorbingMonoid_collapse_le :
    ∀ {k n : ℕ}, 1 ≤ k → n ≤ k →
      ∀ {D : Type v} [GlobularInfSystem D] {d : D}, IsNTruncated n d →
        ∀ (F : GlobularFunctor StepState D) (φ : F.Rel (AbsorbingLaliMonoid k) d),
          IsEquiv (F.mapMor φ (monoidFwdArrow k)) ∧
            ObjEquiv (F.mapObj φ false) (F.mapObj φ true) := by
  intro k n hk hn
  induction n generalizing k with
  | zero =>
    intro D _ d hd F φ
    have heq : IsEquiv (F.mapMor φ (monoidFwdArrow k)) := hd.isEquiv_of_zero _
    exact ⟨heq, ⟨F.mapMor φ (monoidFwdArrow k), heq⟩⟩
  | succ m ih =>
    intro D _ d hd F φ
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    let f : Obj (hom (s := AbsorbingLaliMonoid (k' + 1)) (false : Bool) (true : Bool)) :=
      monoidFwdArrow (k' + 1)
    let g : Obj (hom (s := AbsorbingLaliMonoid (k' + 1)) (true : Bool) (false : Bool)) :=
      monoidRevArrow k'
    have hfg : compMor (F.mapMor φ f) (F.mapMor φ g) = idMor (F.mapObj φ false) :=
      (F.map_comp φ f g).symm.trans (F.map_id φ false)
    let η := GlobularFunctor.cellOfEq hfg
    have hη : IsEquiv η := GlobularFunctor.isEquiv_cellOfEq hfg
    let εraw := F.mapMor (F.mapHom φ (true : Bool) (true : Bool)) (monoidFwdArrow k')
    have hεraw : IsEquiv εraw := by
      cases m with
      | zero =>
        exact (hd (F.mapObj φ true) (F.mapObj φ true)).isEquiv_of_zero εraw
      | succ m' =>
        have hk' : 1 ≤ k' := by omega
        have hm' : m' + 1 ≤ k' := by omega
        exact (ih hk' hm' (hd (F.mapObj φ true) (F.mapObj φ true)) F
          (F.mapHom φ (true : Bool) (true : Bool))).1
    have hgf1 : F.mapObj (F.mapHom φ (true : Bool) (true : Bool)) (false : Bool) =
        compMor (F.mapMor φ g) (F.mapMor φ f) :=
      F.map_comp φ g f
    have hgf2 : F.mapObj (F.mapHom φ (true : Bool) (true : Bool)) (true : Bool) =
        idMor (F.mapObj φ true) :=
      F.map_id φ true
    let ε := hgf2 ▸ hgf1 ▸ εraw
    have hε : IsEquiv ε :=
      GlobularFunctor.isEquiv_congr_endpoints hgf1 hgf2 εraw hεraw
    have hf_eq : IsEquiv (F.mapMor φ f) :=
      IsEquiv.mk (F.mapMor φ f) (F.mapMor φ g) η ε hη hε
    exact ⟨hf_eq, ⟨F.mapMor φ f, hf_eq⟩⟩

/-! ## Section 4: Part (c) — Restricted-Tail Step-Product `StepProductQ` & Theorem 12D -/

/-- Canonical minimal tail cutoff `ptCutoff f` for an `EventuallyPtFamily`. -/
private noncomputable def ptCutoff (f : EventuallyPtFamily) : ℕ := by
  classical
  exact Nat.find f.prop

private theorem ptCutoff_spec (f : EventuallyPtFamily) (j : ℕ) (hj : ptCutoff f ≤ j) :
    f.val j = .pt := by
  classical
  exact Nat.find_spec f.prop j hj

private theorem ptCutoff_min (f : EventuallyPtFamily) {N : ℕ}
    (hN : ∀ j ≥ N, f.val j = .pt) : ptCutoff f ≤ N := by
  classical
  exact Nat.find_min' f.prop hN

/-- Canonical finite natural-number rank `prodNatRank f` of an `EventuallyPtFamily`. -/
noncomputable def prodNatRank (f : EventuallyPtFamily) : ℕ :=
  (Finset.range (ptCutoff f)).sup (fun j ↦ FactorState.natRank (f.val j))

/-- `prodNatRank f` is invariant under replacing `ptCutoff f` with any tail bound `N`. -/
theorem prodNatRank_eq_sup_of_bound (f : EventuallyPtFamily) {N : ℕ}
    (hN : ∀ j ≥ N, f.val j = .pt) :
    prodNatRank f = (Finset.range N).sup (fun j ↦ FactorState.natRank (f.val j)) := by
  have hle : ptCutoff f ≤ N := ptCutoff_min f hN
  apply le_antisymm
  · exact Finset.sup_le fun j hj ↦
      Finset.le_sup (f := fun i ↦ FactorState.natRank (f.val i))
        (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hle))
  · refine Finset.sup_le fun j hj ↦ ?_
    by_cases hlt : j < ptCutoff f
    · exact Finset.le_sup (f := fun i ↦ FactorState.natRank (f.val i)) (Finset.mem_range.mpr hlt)
    · have hpt : f.val j = .pt := ptCutoff_spec f j (Nat.le_of_not_gt hlt)
      simp [hpt, FactorState.natRank]

/-- Every coordinate `j` of `f` has `natRank (f.val j) ≤ prodNatRank f`. -/
theorem natRank_le_prodNatRank (f : EventuallyPtFamily) (j : ℕ) :
    FactorState.natRank (f.val j) ≤ prodNatRank f := by
  by_cases hj : j < ptCutoff f
  · exact Finset.le_sup (f := fun i ↦ FactorState.natRank (f.val i)) (Finset.mem_range.mpr hj)
  · have hpt : f.val j = .pt := ptCutoff_spec f j (Nat.le_of_not_gt hj)
    simp [hpt, FactorState.natRank]

/-- Computing `prodNatRank (qHomFamily m r) = min m r`. -/
theorem prodNatRank_qHomFamily (m r : ℕ) :
    prodNatRank (qHomFamily m r) = min m r := by
  rw [prodNatRank_eq_sup_of_bound (qHomFamily m r) (N := min m r)
    (fun _ hj ↦ qHomAt_eq_pt_of_le hj)]
  cases hmin : min m r with
  | zero => simp
  | succ k =>
    apply le_antisymm
    · refine Finset.sup_le fun j hj ↦ ?_
      have hjlt : j < min m r := hmin ▸ Finset.mem_range.mp hj
      rw [show (qHomFamily m r).val j = qHomAt m r j from rfl, qHomAt_eq_monoid_of_lt hjlt]
      simp only [FactorState.natRank]
      omega
    · have hk_lt : k < min m r := by omega
      have hsup := Finset.le_sup (f := fun j ↦ FactorState.natRank ((qHomFamily m r).val j))
        (Finset.mem_range.mpr (by omega : k < k + 1))
      dsimp only at hsup
      rw [show (qHomFamily m r).val k = qHomAt m r k from rfl, qHomAt_eq_monoid_of_lt hk_lt]
        at hsup
      exact hsup

/-- Any rank-`0` `FactorState` has `.pt` hom-states everywhere. -/
theorem factor_rank_zero_hom_eq_pt {s : FactorState} (hs : s.natRank = 0)
    (x y : FactorState.obj s) :
    FactorState.hom x y = .pt := by
  cases s with
  | pt => rfl
  | empty => exact Empty.elim x
  | iso => rfl
  | monoid k =>
    cases k with
    | zero => rfl
    | succ k' => exact False.elim (Nat.succ_ne_zero k' hs)

/-- Any rank-`0` `FactorState` has `Subsingleton` `1`-morphism spaces. -/
theorem factor_rank_zero_hom_subsingleton {s : FactorState} (hs : s.natRank = 0)
    (x y : FactorState.obj s) :
    Subsingleton (FactorState.obj (FactorState.hom x y)) := by
  rw [factor_rank_zero_hom_eq_pt hs x y]
  exact inferInstanceAs (Subsingleton Unit)

/-- Finite natural-number rank on non-`qFull` states of `StepState`. -/
noncomputable def stepNatRank : StepState → ℕ
  | .factor s => s.natRank
  | .prod f => prodNatRank f
  | .qTrunc d => d
  | .qFull => 0

/-- Transfinite `Ordinal.{0}` rank on `StepState` (`Ordinal.omega0` on `.qFull`). -/
noncomputable def stepRank : StepState → Ordinal.{0}
  | .qFull => Ordinal.omega0
  | s => (stepNatRank s : Ordinal.{0})

/-- Helper proving strict rank descent on `FactorState.hom` whenever `0 < fs.natRank`. -/
private theorem factor_hom_natRank_lt : ∀ {fs : FactorState},
    0 < fs.natRank → ∀ (x y : fs.obj), (FactorState.hom x y).natRank < fs.natRank
  | .pt, h, _, _ => absurd h (lt_irrefl 0)
  | .empty, h, x, _ => Empty.elim x
  | .iso, h, _, _ => absurd h (lt_irrefl 0)
  | .monoid 0, h, _, _ => absurd h (lt_irrefl 0)
  | .monoid 1, _, x, y => by cases x <;> cases y <;> decide
  | .monoid (_ + 2), _, x, y => by
    cases x <;> cases y
    · exact Nat.succ_pos _
    · exact Nat.succ_pos _
    · exact Nat.succ_pos _
    · exact Nat.lt_succ_self _

/-- `RankedInfCat StepState` instance calibrating `StepProductQ` (`rank .qFull = ω`,
`rank (hom m r) = min m r < ω`) for Theorem 9A & ORW Question 5.58. -/
noncomputable instance instRankedInfCatStepState : RankedInfCat StepState where
  rank := stepRank
  rank_zero_equiv {s} hs {x y} f := by
    cases s with
    | factor fs =>
      cases fs with
      | pt => cases x; cases y; cases f; exact IsEquiv.id _
      | empty => exact Empty.elim x
      | iso =>
        have hx : compMor f (() : Obj (hom y x)) = idMor x := rfl
        have hy : compMor (() : Obj (hom y x)) f = idMor y := rfl
        exact IsEquiv.mk f () (GlobularFunctor.cellOfEq hx) (GlobularFunctor.cellOfEq hy)
          (GlobularFunctor.isEquiv_cellOfEq hx) (GlobularFunctor.isEquiv_cellOfEq hy)
      | monoid k =>
        cases k with
        | zero => cases x; cases y; cases f; exact IsEquiv.id _
        | succ k' =>
          have hpos : (0 : Ordinal.{0}) < ((k' + 1 : ℕ) : Ordinal.{0}) := by
            exact_mod_cast Nat.succ_pos k'
          exact False.elim (hpos.ne' hs)
    | prod pf =>
      have hpr0 : prodNatRank pf = 0 := Nat.cast_eq_zero.mp hs
      have hcoord0 : ∀ j : ℕ, FactorState.natRank (pf.val j) = 0 := fun j ↦
        Nat.eq_zero_of_le_zero (hpr0 ▸ natRank_le_prodNatRank pf j)
      have hsubxx : Subsingleton (Obj (hom (s := StepState.prod pf) x x)) :=
        ⟨fun a b ↦ funext fun j ↦
          (factor_rank_zero_hom_subsingleton (hcoord0 j) (x j) (x j)).elim (a j) (b j)⟩
      have hsubyy : Subsingleton (Obj (hom (s := StepState.prod pf) y y)) :=
        ⟨fun a b ↦ funext fun j ↦
          (factor_rank_zero_hom_subsingleton (hcoord0 j) (y j) (y j)).elim (a j) (b j)⟩
      let g : Obj (hom (s := StepState.prod pf) y x) := fun j ↦
        cast (congrArg FactorState.obj (factor_rank_zero_hom_eq_pt (hcoord0 j) (y j) (x j)).symm) ()
      have hfg : compMor f g = idMor x := hsubxx.elim _ _
      have hgf : compMor g f = idMor y := hsubyy.elim _ _
      exact IsEquiv.mk f g (GlobularFunctor.cellOfEq hfg) (GlobularFunctor.cellOfEq hgf)
        (GlobularFunctor.isEquiv_cellOfEq hfg) (GlobularFunctor.isEquiv_cellOfEq hgf)
    | qTrunc d =>
      cases d with
      | zero => cases x; cases y; cases f; exact IsEquiv.id _
      | succ d' =>
        have hpos : (0 : Ordinal.{0}) < ((d' + 1 : ℕ) : Ordinal.{0}) := by
          exact_mod_cast Nat.succ_pos d'
        exact False.elim (hpos.ne' hs)
    | qFull => exact False.elim (Ordinal.omega0_ne_zero hs)
  rank_hom_zero {s} hs x y := by
    cases s with
    | factor fs =>
      cases fs with
      | pt => rfl
      | empty => exact Empty.elim x
      | iso => rfl
      | monoid k =>
        cases k with
        | zero => rfl
        | succ k' =>
          have hpos : (0 : Ordinal.{0}) < ((k' + 1 : ℕ) : Ordinal.{0}) := by
            exact_mod_cast Nat.succ_pos k'
          exact False.elim (hpos.ne' hs)
    | prod pf =>
      have hpr0 : prodNatRank pf = 0 := Nat.cast_eq_zero.mp hs
      have hcoord0 : ∀ j : ℕ, FactorState.natRank (pf.val j) = 0 := fun j ↦
        Nat.eq_zero_of_le_zero (hpr0 ▸ natRank_le_prodNatRank pf j)
      change ((prodNatRank (prodHomFamily pf x y) : ℕ) : Ordinal.{0}) = 0
      rw [Nat.cast_eq_zero]
      apply Nat.eq_zero_of_le_zero
      refine Finset.sup_le fun j _ ↦ ?_
      change FactorState.natRank (FactorState.hom (x j) (y j)) ≤ 0
      rw [factor_rank_zero_hom_eq_pt (hcoord0 j) (x j) (y j)]
      exact le_rfl
    | qTrunc d =>
      cases d with
      | zero => rfl
      | succ d' =>
        have hpos : (0 : Ordinal.{0}) < ((d' + 1 : ℕ) : Ordinal.{0}) := by
          exact_mod_cast Nat.succ_pos d'
        exact False.elim (hpos.ne' hs)
    | qFull => exact False.elim (Ordinal.omega0_ne_zero hs)
  rank_hom_lt {s} hpos x y := by
    cases s with
    | factor fs =>
      have hposNat : 0 < fs.natRank := Nat.pos_of_ne_zero fun h0 ↦
        absurd (show stepRank (StepState.factor fs) = 0 by
          simp [stepRank, stepNatRank, h0]) hpos.ne'
      change ((FactorState.natRank (FactorState.hom x y) : ℕ) : Ordinal.{0}) <
        ((fs.natRank : ℕ) : Ordinal.{0})
      exact Nat.cast_lt.mpr (factor_hom_natRank_lt hposNat x y)
    | prod pf =>
      have hposNat : 0 < prodNatRank pf := Nat.pos_of_ne_zero fun h0 ↦
        absurd (show stepRank (StepState.prod pf) = 0 by
          simp [stepRank, stepNatRank, h0]) hpos.ne'
      change ((prodNatRank (prodHomFamily pf x y) : ℕ) : Ordinal.{0}) <
        ((prodNatRank pf : ℕ) : Ordinal.{0})
      apply Nat.cast_lt.mpr
      refine (Finset.sup_lt_iff hposNat).2 fun j _ ↦ ?_
      change FactorState.natRank (FactorState.hom (x j) (y j)) < prodNatRank pf
      have hjle := natRank_le_prodNatRank pf j
      by_cases hj0 : FactorState.natRank (pf.val j) = 0
      · rw [factor_rank_zero_hom_eq_pt hj0 (x j) (y j)]
        exact hposNat
      · exact lt_of_lt_of_le
          (factor_hom_natRank_lt (Nat.pos_of_ne_zero hj0) (x j) (y j)) hjle
    | qTrunc d =>
      cases d with
      | zero => exact False.elim (lt_irrefl 0 hpos)
      | succ d' =>
        change ((prodNatRank (qHomFamily x.val y.val) : ℕ) : Ordinal.{0}) <
          ((d' + 1 : ℕ) : Ordinal.{0})
        apply Nat.cast_lt.mpr
        rw [prodNatRank_qHomFamily]
        exact lt_of_le_of_lt (min_le_left x.val y.val) x.isLt
    | qFull =>
      change ((prodNatRank (qHomFamily x y) : ℕ) : Ordinal.{0}) < Ordinal.omega0
      rw [prodNatRank_qHomFamily]
      exact Ordinal.nat_lt_omega0 (min x y)

/-- Exact hom-state rank in `StepProductQ`: `rank (hom (s := .qFull) m r) = min m r ≤ max m r < ω`.
-/
theorem stepProductQ_rank_hom (m r : ℕ) :
    rank (hom (s := StepState.qFull) m r) = ((min m r : ℕ) : Ordinal.{0}) ∧
      rank (hom (s := StepState.qFull) m r) ≤ ((max m r : ℕ) : Ordinal.{0}) ∧
      ((max m r : ℕ) : Ordinal.{0}) < Ordinal.omega0 := by
  have hrank : rank (hom (s := StepState.qFull) m r) = ((min m r : ℕ) : Ordinal.{0}) := by
    change ((prodNatRank (qHomFamily m r) : ℕ) : Ordinal.{0}) = ((min m r : ℕ) : Ordinal.{0})
    rw [prodNatRank_qHomFamily]
  refine ⟨hrank, ?_, Ordinal.nat_lt_omega0 (max m r)⟩
  rw [hrank]
  exact Nat.cast_le.mpr (le_trans (min_le_left m r) (le_max_left m r))

/-- **Theorem 9A & ORW Question 5.58 on `StepProductQ` (`stepProductQ_omega_completeness`):**
Because `rank StepState.qFull = ω`, `IsOmegaInv f ↔ IsEquiv f` holds on `StepProductQ` and across
every reachable higher `k`-cell hom-state, stabilizing at stage `α = 0`. -/
theorem stepProductQ_omega_completeness :
    rank StepState.qFull = Ordinal.omega0 ∧
      (∀ (m r : ℕ),
        {f : Obj (hom (s := StepState.qFull) m r) | IsOmegaInv f} =
          {f : Obj (hom (s := StepState.qFull) m r) | IsEquiv f}) ∧
      (∀ {t : StepState}, ReachableFrom StepState.qFull t → ∀ (u w : Obj t),
        {f : Obj (hom u w) | IsOmegaInv f} = {f : Obj (hom u w) | IsEquiv f}) :=
  ⟨rfl, orw_question558_stabilizes_at_zero (s := StepState.qFull) le_rfl⟩

/-- Coordinate projection state correspondence `PrRel j` for `prFunctor j`. -/
inductive PrRel (j : ℕ) : StepState → StepState → Type
  | top : PrRel j StepState.qFull (StepState.factor (.monoid (j + 2)))
  | prod (f : EventuallyPtFamily) : PrRel j (StepState.prod f) (StepState.factor (f.val j))

private def prMapObj (j : ℕ) : ∀ {s₁ s₂ : StepState}, PrRel j s₁ s₂ → Obj s₁ → Obj s₂
  | _, _, .top, x => decide (j < x)
  | _, _, .prod _, x => x j

private def prMapHom (j : ℕ) :
    ∀ {s₁ s₂ : StepState} (φ : PrRel j s₁ s₂) (x y : Obj s₁),
      PrRel j (hom x y) (hom (prMapObj j φ x) (prMapObj j φ y))
  | _, _, .top, x, y => .prod (qHomFamily x y)
  | _, _, .prod f, x, y => .prod (prodHomFamily f x y)

/-- Coordinate projection functor `prFunctor j : StepState.qFull → .factor (.monoid (j + 2))`
mapping `e^{(m)} ↦ decide (j < m)` and restricting naturally to `x ↦ x j` on `.prod`. -/
def prFunctor (j : ℕ) : GlobularFunctor StepState StepState where
  Rel := PrRel j
  mapObj := prMapObj j
  mapHom := prMapHom j
  map_id := fun {_ _} φ x ↦ by
    cases φ <;> rfl
  map_comp := fun {_ _} φ {_ _ _} _ _ ↦ by
    cases φ <;> rfl

/-- Coordinatewise `n`-truncation criterion for restricted-tail products `.prod f`. -/
theorem isNTruncated_prod {n : ℕ} {f : EventuallyPtFamily}
    (hf : ∀ j : ℕ, IsNTruncated n (StepState.factor (f.val j))) :
    IsNTruncated n (StepState.prod f) := by
  induction n generalizing f with
  | zero =>
    have hcoord0 : ∀ j : ℕ, FactorState.natRank (f.val j) = 0 := by
      intro j
      rcases hfs : f.val j with _ | _ | _ | k
      · rfl
      · rfl
      · rfl
      · cases k with
        | zero => rfl
        | succ k' =>
          exfalso
          have hbad : IsNTruncated 0 (StepState.factor (.monoid (k' + 1))) := by
            have := hf j
            rwa [hfs] at this
          exact not_objEquiv_monoid_succ k'
            ⟨monoidFwdArrow k', hbad.isEquiv_of_zero (monoidFwdArrow k')⟩
    have hrank0 : rank (StepState.prod f) = 0 := by
      change ((prodNatRank f : ℕ) : Ordinal.{0}) = 0
      rw [Nat.cast_eq_zero]
      apply Nat.eq_zero_of_le_zero
      refine Finset.sup_le fun j _ ↦ ?_
      rw [hcoord0 j]
    intro t ht u w f0
    have htr0 : rank t = 0 := le_antisymm (le_trans ht.rank_le (le_of_eq hrank0)) (zero_le _)
    exact rank_zero_equiv htr0 f0
  | succ k ih =>
    intro x y
    exact ih fun j ↦ hf j (x j) (y j)

/-- Exact finite local hom-dimension of `StepProductQ`: `IsNTruncated (min m r) (hom m r)`. -/
theorem isNTruncated_qFull_hom_min (m r : ℕ) :
    IsNTruncated (min m r) (hom (s := StepState.qFull) m r) := by
  refine isNTruncated_prod fun j ↦ ?_
  by_cases hj : j < min m r
  · rw [show (qHomFamily m r).val j = qHomAt m r j from rfl, qHomAt_eq_monoid_of_lt hj]
    exact (isNTruncated_monoid (j + 1)).mono hj
  · rw [show (qHomFamily m r).val j = qHomAt m r j from rfl,
      qHomAt_eq_pt_of_le (Nat.le_of_not_gt hj)]
    exact isNTruncated_pt.mono (Nat.zero_le _)

/-- Upper-bound finite local hom-dimension `IsNTruncated (max m r) (hom m r)` in `StepProductQ`.
-/
theorem isNTruncated_qFull_hom_max (m r : ℕ) :
    IsNTruncated (max m r) (hom (s := StepState.qFull) m r) :=
  (isNTruncated_qFull_hom_min m r).mono (le_trans (min_le_left m r) (le_max_left m r))

/-- Every state reachable from `.prod f` is `.prod g` with coordinatewise `ReachableFrom`. -/
private theorem prod_reachable_factor (f : EventuallyPtFamily) {t : StepState}
    (ht : ReachableFrom (StepState.prod f) t) :
    ∃ (g : EventuallyPtFamily) (_ : t = StepState.prod g),
      ∀ j : ℕ, ReachableFrom (StepState.factor (f.val j)) (StepState.factor (g.val j)) := by
  induction ht with
  | refl => exact ⟨f, rfl, fun _ ↦ ReachableFrom.refl⟩
  | @step q _ x y ih =>
    rcases ih with ⟨g, rfl, hfg⟩
    exact ⟨prodHomFamily g x y, rfl, fun j ↦ ReachableFrom.step (hfg j) (x j) (y j)⟩

/-- Coordinatewise hereditary gauntness of restricted-tail products `.prod f`. -/
theorem isHereditarilyGaunt_prod {f : EventuallyPtFamily}
    (hf : ∀ j : ℕ, IsHereditarilyGaunt (StepState.factor (f.val j))) :
    IsHereditarilyGaunt (StepState.prod f) := by
  intro t ht
  rcases prod_reachable_factor f ht with ⟨g, rfl, hfg⟩
  intro x y hxy
  funext j
  exact (hf j (hfg j)) ((prFunctor j).map_objEquiv (PrRel.prod g) hxy)

/-- Hereditary gauntness of `StepProductQ` (`IsHereditarilyGaunt StepState.qFull`). -/
theorem isHereditarilyGaunt_qFull : IsHereditarilyGaunt StepState.qFull := by
  refine isHereditarilyGaunt_of_hom ?_ fun m' r' ↦ ?_
  · intro m' r' hmr
    let m : ℕ := m'
    let r : ℕ := r'
    have hm : ∀ j : ℕ, decide (j < m) = decide (j < r) := fun j ↦
      (isHereditarilyGaunt_monoid (j + 2)).isObjGaunt
        ((prFunctor j).map_objEquiv PrRel.top hmr)
    change m = r
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hm m
      simp [hlt] at this
    · have := hm r
      simp [hgt] at this
  · let m : ℕ := m'
    let r : ℕ := r'
    change IsHereditarilyGaunt (StepState.prod (qHomFamily m r))
    refine isHereditarilyGaunt_prod fun j ↦ ?_
    unfold qHomFamily
    dsimp only
    by_cases hj : j < Min.min m r
    · rw [qHomAt_eq_monoid_of_lt hj]
      exact isHereditarilyGaunt_monoid (j + 1)
    · rw [qHomAt_eq_pt_of_le (Nat.le_of_not_gt hj)]
      exact isHereditarilyGaunt_pt

/-- Explicit `Equiv` identifying `Obj (hom (s := StepState.qFull) m r)` with `Fin (min m r) → Bool`.
-/
noncomputable def homQ_equiv_finProd (m r : ℕ) :
    Obj (hom (s := StepState.qFull) m r) ≃ (Fin (min m r) → Bool) where
  toFun f i := cast (congrArg FactorState.obj (qHomAt_eq_monoid_of_lt i.isLt)) (f i.val)
  invFun g j :=
    if hj : j < min m r then
      cast (congrArg FactorState.obj (qHomAt_eq_monoid_of_lt hj).symm) (g ⟨j, hj⟩)
    else
      cast (congrArg FactorState.obj (qHomAt_eq_pt_of_le (Nat.le_of_not_gt hj)).symm) ()
  left_inv f := by
    funext j
    by_cases hj : j < min m r
    · simp only [dif_pos hj, cast_cast, cast_eq]
    · simp only [dif_neg hj]
      have hpt : qHomAt m r j = .pt := qHomAt_eq_pt_of_le (Nat.le_of_not_gt hj)
      have hsub : Subsingleton (FactorState.obj (qHomAt m r j)) := by
        rw [hpt]
        exact inferInstanceAs (Subsingleton Unit)
      exact hsub.elim _ _
  right_inv g := by
    funext i
    simp only [dif_pos i.isLt, cast_cast, cast_eq]

/-- Finite `Fintype` instance on `Obj (hom (s := StepState.qFull) m r)`. -/
noncomputable instance instFintypeHomQ (m r : ℕ) :
    Fintype (Obj (hom (s := StepState.qFull) m r)) :=
  Fintype.ofEquiv (Fin (min m r) → Bool) (homQ_equiv_finProd m r).symm

/-- Exact finite cardinality `Fintype.card (Obj (hom (s := .qFull) m r)) = 2 ^ min m r`. -/
theorem homQ_card_eq (m r : ℕ) :
    Fintype.card (Obj (hom (s := StepState.qFull) m r)) = 2 ^ min m r := by
  rw [Fintype.card_congr (homQ_equiv_finProd m r), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]

/-- Predicate characterizing factor states `.pt` and `.monoid m` used on slice off-coordinates. -/
def IsPtOrMonoid : FactorState → Prop
  | .pt => True
  | .monoid _ => True
  | _ => False

/-- Canonical top/identity object `1_s` on `IsPtOrMonoid` factor states. -/
def topElem : ∀ s : FactorState, IsPtOrMonoid s → FactorState.obj s
  | .pt, _ => ()
  | .monoid 0, _ => ()
  | .monoid (_ + 1), _ => true
  | .empty, h => False.elim h
  | .iso, h => False.elim h

/-- `IsPtOrMonoid` is closed under `FactorState.hom (topElem ...) (topElem ...)`. -/
theorem isPtOrMonoid_hom : ∀ {s : FactorState} (h : IsPtOrMonoid s),
    IsPtOrMonoid (FactorState.hom (topElem s h) (topElem s h))
  | .pt, _ => trivial
  | .monoid 0, _ => trivial
  | .monoid 1, _ => trivial
  | .monoid (_ + 2), _ => trivial
  | .empty, h => False.elim h
  | .iso, h => False.elim h

/-- `topElem` preserves `FactorState.idMor`. -/
theorem topElem_id : ∀ {s : FactorState} (h : IsPtOrMonoid s),
    FactorState.idMor (topElem s h) =
      topElem (FactorState.hom (topElem s h) (topElem s h)) (isPtOrMonoid_hom h)
  | .pt, _ => rfl
  | .monoid 0, _ => rfl
  | .monoid 1, _ => rfl
  | .monoid (_ + 2), _ => rfl
  | .empty, h => False.elim h
  | .iso, h => False.elim h

/-- `topElem` preserves `FactorState.compMor`. -/
theorem topElem_comp : ∀ {s : FactorState} (h : IsPtOrMonoid s),
    FactorState.compMor
      (topElem (FactorState.hom (topElem s h) (topElem s h)) (isPtOrMonoid_hom h))
      (topElem (FactorState.hom (topElem s h) (topElem s h)) (isPtOrMonoid_hom h)) =
      topElem (FactorState.hom (topElem s h) (topElem s h)) (isPtOrMonoid_hom h)
  | .pt, _ => rfl
  | .monoid 0, _ => rfl
  | .monoid 1, _ => rfl
  | .monoid (_ + 2), _ => rfl
  | .empty, h => False.elim h
  | .iso, h => False.elim h

/-- Every `qHomAt m r j` satisfies `IsPtOrMonoid`. -/
theorem isPtOrMonoid_qHomAt (m r j : ℕ) : IsPtOrMonoid (qHomAt m r j) := by
  unfold qHomAt
  cases decide (j < m) <;> cases decide (j < r) <;> exact trivial

/-- State correspondence relation for `sliceFunctor k : .factor (.monoid (k + 2)) → .qFull`. -/
inductive SliceRel (k : ℕ) : StepState → StepState → Type
  | top : SliceRel k (StepState.factor (.monoid (k + 2))) StepState.qFull
  | prod (s : FactorState) (f : EventuallyPtFamily) (hk : f.val k = s)
      (hother : ∀ j ≠ k, IsPtOrMonoid (f.val j)) :
      SliceRel k (StepState.factor s) (StepState.prod f)

/-- `0`-cell mapping of `sliceFunctor k` on `.prod`. -/
def sliceProdObj (k : ℕ) {s : FactorState} (f : EventuallyPtFamily) (hk : f.val k = s)
    (hother : ∀ j ≠ k, IsPtOrMonoid (f.val j)) (x : FactorState.obj s) :
    ∀ j : ℕ, FactorState.obj (f.val j) := fun j ↦
  if hj : j = k then
    cast (congrArg FactorState.obj (hj ▸ hk.symm)) x
  else
    topElem (f.val j) (hother j hj)

/-- Helper computing `FactorState.hom` across a cast `s' = s`. -/
private theorem factorHom_cast {s s' : FactorState} (h : s' = s) (x y : FactorState.obj s) :
    FactorState.hom (cast (congrArg FactorState.obj h.symm) x)
      (cast (congrArg FactorState.obj h.symm) y) = FactorState.hom x y := by
  subst h; rfl

/-- Helper commuting `FactorState.idMor` with `cast` across `s' = s`. -/
private theorem factorId_cast {s s' : FactorState} (h : s' = s) (x : FactorState.obj s) :
    FactorState.idMor (cast (congrArg FactorState.obj h.symm) x) =
      cast (congrArg FactorState.obj (factorHom_cast h x x).symm) (FactorState.idMor x) := by
  subst h; rfl

/-- Helper commuting `FactorState.compMor` with `cast` across `s' = s`. -/
private theorem factorComp_cast {s s' : FactorState} (h : s' = s) {x y z : FactorState.obj s}
    (u : FactorState.obj (FactorState.hom x y))
    (v : FactorState.obj (FactorState.hom y z)) :
    cast (congrArg FactorState.obj (factorHom_cast h x z).symm) (FactorState.compMor u v) =
      FactorState.compMor
        (cast (congrArg FactorState.obj (factorHom_cast h x y).symm) u)
        (cast (congrArg FactorState.obj (factorHom_cast h y z).symm) v) := by
  subst h; rfl

/-- Helper computing diagonal identity transport for `sliceFunctor`. -/
private theorem slice_top_id_diag (j : ℕ) (h : qHomAt (j + 1) (j + 1) j = .monoid (j + 1)) :
    cast (congrArg FactorState.obj h.symm)
        (FactorState.idMor (s := .monoid (j + 2)) true) =
      FactorState.idMor (s := .monoid (j + 2)) (decide (j < j + 1)) := by
  have hdec : decide (j < j + 1) = true := decide_eq_true (Nat.lt_succ_self j)
  revert h
  unfold qHomAt
  rw [hdec]
  intro h
  rfl

/-- Coordinate-`k` hom equality for `sliceProdObj`. -/
private theorem sliceProdObj_hom_at_k (k : ℕ) {s : FactorState} (f : EventuallyPtFamily)
    (hk : f.val k = s) (hother : ∀ j ≠ k, IsPtOrMonoid (f.val j))
    (x y : FactorState.obj s) :
    FactorState.hom (sliceProdObj k f hk hother x k) (sliceProdObj k f hk hother y k) =
      FactorState.hom x y := by
  simp only [sliceProdObj, dif_pos]
  exact factorHom_cast hk x y

/-- Off-coordinate `IsPtOrMonoid` invariance for `sliceProdObj`. -/
private theorem sliceProdObj_hom_other (k : ℕ) {s : FactorState} (f : EventuallyPtFamily)
    (hk : f.val k = s) (hother : ∀ j ≠ k, IsPtOrMonoid (f.val j))
    (x y : FactorState.obj s) :
    ∀ j ≠ k, IsPtOrMonoid
      (FactorState.hom (sliceProdObj k f hk hother x j) (sliceProdObj k f hk hother y j)) := by
  intro j hj
  simp only [sliceProdObj, dif_neg hj]
  by_cases hjj : FactorState.hom (topElem (f.val j) (hother j hj))
      (topElem (f.val j) (hother j hj)) = .pt
  · rw [hjj]; trivial
  · exact isPtOrMonoid_hom (hother j hj)

private theorem factorId_heq {s s' : FactorState} (h : s' = s)
    {a : FactorState.obj s'} {b : FactorState.obj s} (hab : a ≍ b) :
    FactorState.idMor a ≍ FactorState.idMor b := by
  subst h
  obtain rfl := eq_of_heq hab
  rfl

private theorem factorComp_heq {s s' : FactorState} (h : s' = s)
    {x y z : FactorState.obj s} {x' y' z' : FactorState.obj s'}
    (hx : x' ≍ x) (hy : y' ≍ y) (hz : z' ≍ z)
    {u : FactorState.obj (FactorState.hom x y)}
    {v : FactorState.obj (FactorState.hom y z)}
    {u' : FactorState.obj (FactorState.hom x' y')}
    {v' : FactorState.obj (FactorState.hom y' z')}
    (hu : u' ≍ u) (hv : v' ≍ v) :
    FactorState.compMor u' v' ≍ FactorState.compMor u v := by
  subst h
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  obtain rfl := eq_of_heq hz
  obtain rfl := eq_of_heq hu
  obtain rfl := eq_of_heq hv
  rfl

private theorem topElem_heq {s₁ s₂ : FactorState} (hs : s₁ = s₂)
    (h₁ : IsPtOrMonoid s₁) (h₂ : IsPtOrMonoid s₂) :
    topElem s₁ h₁ ≍ topElem s₂ h₂ := by
  subst hs
  rfl

private theorem slice_prod_id_at_k {s : FactorState} (j : ℕ) (f : EventuallyPtFamily)
    (hk : f.val j = s) (hother : ∀ i ≠ j, IsPtOrMonoid (f.val i))
    (x : FactorState.obj s)
    (hHom : FactorState.hom (sliceProdObj j f hk hother x j)
        (sliceProdObj j f hk hother x j) = FactorState.hom x x)
    (hother' : ∀ i ≠ j, IsPtOrMonoid (FactorState.hom (sliceProdObj j f hk hother x i)
        (sliceProdObj j f hk hother x i))) :
    sliceProdObj j (prodHomFamily f (sliceProdObj j f hk hother x)
        (sliceProdObj j f hk hother x)) hHom hother' (FactorState.idMor x) j =
      FactorState.idMor (sliceProdObj j f hk hother x j) := by
  have hx : sliceProdObj j f hk hother x j ≍ x := by
    simp only [sliceProdObj, dif_pos]
    exact cast_heq _ _
  have hl : sliceProdObj j (prodHomFamily f (sliceProdObj j f hk hother x)
        (sliceProdObj j f hk hother x)) hHom hother' (FactorState.idMor x) j ≍
      FactorState.idMor x := by
    simp only [sliceProdObj, prodHomFamily, dif_pos]
    exact cast_heq _ _
  exact eq_of_heq (hl.trans (factorId_heq hk hx).symm)

private theorem slice_top_id_lt (j m : ℕ) (h : qHomAt m m j = .monoid (j + 1))
    (hp : IsPtOrMonoid (qHomAt m m j)) (hd : decide (j < m) = true) :
    topElem (qHomAt m m j) hp =
      FactorState.idMor (s := .monoid (j + 2)) (decide (j < m)) := by
  revert hp h
  unfold qHomAt
  rw [hd]
  intro _ _
  cases j <;> rfl

private theorem slice_top_comp_lt (j mx my mz : ℕ)
    (hdx : decide (j < mx) = true) (hdy : decide (j < my) = true)
    (hdz : decide (j < mz) = true)
    (hpx : IsPtOrMonoid (qHomAt mx my j)) (hpy : IsPtOrMonoid (qHomAt my mz j))
    (hpz : IsPtOrMonoid (qHomAt mx mz j)) :
    topElem (qHomAt mx mz j) hpz =
      FactorState.compMor (s := .monoid (j + 2))
        (topElem (qHomAt mx my j) hpx) (topElem (qHomAt my mz j) hpy) := by
  revert hpx hpy hpz
  unfold qHomAt
  rw [hdx, hdy, hdz]
  intro _ _ _
  cases j <;> rfl

private theorem slice_top_comp_diag_tft (j : ℕ)
    (hkxz : qHomAt (j + 1) (j + 1) j = FactorState.hom (s := .monoid (j + 2)) true true)
    (hkxy : qHomAt (j + 1) j j = FactorState.hom (s := .monoid (j + 2)) true false)
    (hkyz : qHomAt j (j + 1) j = FactorState.hom (s := .monoid (j + 2)) false true)
    (f : FactorState.obj (FactorState.hom (s := .monoid (j + 2)) true false))
    (g : FactorState.obj (FactorState.hom (s := .monoid (j + 2)) false true)) :
    cast (congrArg FactorState.obj hkxz.symm)
        (FactorState.compMor (s := .monoid (j + 2)) f g) =
      FactorState.compMor (s := .monoid (j + 2))
        (x := decide (j < j + 1)) (y := decide (j < j)) (z := decide (j < j + 1))
        (cast (congrArg FactorState.obj hkxy.symm) f)
        (cast (congrArg FactorState.obj hkyz.symm) g) := by
  have hd1 : decide (j < j + 1) = true := decide_eq_true (Nat.lt_succ_self j)
  have hd2 : decide (j < j) = false := decide_eq_false (Nat.lt_irrefl j)
  revert hkxz hkxy hkyz f g
  unfold qHomAt
  rw [hd1, hd2]
  intro _ _ _ f g
  cases j <;> rfl

private theorem slice_top_comp_diag_ttt (j : ℕ)
    (hkxz : qHomAt (j + 1) (j + 1) j = FactorState.hom (s := .monoid (j + 2)) true true)
    (hkxy : qHomAt (j + 1) (j + 1) j = FactorState.hom (s := .monoid (j + 2)) true true)
    (hkyz : qHomAt (j + 1) (j + 1) j = FactorState.hom (s := .monoid (j + 2)) true true)
    (f g : FactorState.obj (FactorState.hom (s := .monoid (j + 2)) true true)) :
    cast (congrArg FactorState.obj hkxz.symm)
        (FactorState.compMor (s := .monoid (j + 2)) f g) =
      FactorState.compMor (s := .monoid (j + 2))
        (x := decide (j < j + 1)) (y := decide (j < j + 1)) (z := decide (j < j + 1))
        (cast (congrArg FactorState.obj hkxy.symm) f)
        (cast (congrArg FactorState.obj hkyz.symm) g) := by
  have hd1 : decide (j < j + 1) = true := decide_eq_true (Nat.lt_succ_self j)
  revert hkxz hkxy hkyz f g
  unfold qHomAt
  rw [hd1]
  intro _ _ _ f g
  rfl

private theorem slice_prod_comp_at_k {s : FactorState} (j : ℕ) (f : EventuallyPtFamily)
    (hk : f.val j = s) (hother : ∀ i ≠ j, IsPtOrMonoid (f.val i))
    {x y z : FactorState.obj s}
    (u : FactorState.obj (FactorState.hom x y))
    (v : FactorState.obj (FactorState.hom y z))
    (hxz : FactorState.hom (sliceProdObj j f hk hother x j)
        (sliceProdObj j f hk hother z j) = FactorState.hom x z)
    (hxy : FactorState.hom (sliceProdObj j f hk hother x j)
        (sliceProdObj j f hk hother y j) = FactorState.hom x y)
    (hyz : FactorState.hom (sliceProdObj j f hk hother y j)
        (sliceProdObj j f hk hother z j) = FactorState.hom y z) :
    sliceProdObj j (prodHomFamily f (sliceProdObj j f hk hother x)
        (sliceProdObj j f hk hother z))
      hxz (sliceProdObj_hom_other j f hk hother x z) (FactorState.compMor u v) j =
      FactorState.compMor
        (sliceProdObj j (prodHomFamily f (sliceProdObj j f hk hother x)
            (sliceProdObj j f hk hother y))
          hxy (sliceProdObj_hom_other j f hk hother x y) u j)
        (sliceProdObj j (prodHomFamily f (sliceProdObj j f hk hother y)
            (sliceProdObj j f hk hother z))
          hyz (sliceProdObj_hom_other j f hk hother y z) v j) := by
  have hx : sliceProdObj j f hk hother x j ≍ x := by
    simp only [sliceProdObj, dif_pos]
    exact cast_heq _ _
  have hy : sliceProdObj j f hk hother y j ≍ y := by
    simp only [sliceProdObj, dif_pos]
    exact cast_heq _ _
  have hz : sliceProdObj j f hk hother z j ≍ z := by
    simp only [sliceProdObj, dif_pos]
    exact cast_heq _ _
  have hl : sliceProdObj j (prodHomFamily f (sliceProdObj j f hk hother x)
        (sliceProdObj j f hk hother z))
      hxz (sliceProdObj_hom_other j f hk hother x z) (FactorState.compMor u v) j ≍
      FactorState.compMor u v := by
    simp only [sliceProdObj, dif_pos]
    exact cast_heq _ _
  have hu : sliceProdObj j (prodHomFamily f (sliceProdObj j f hk hother x)
        (sliceProdObj j f hk hother y))
      hxy (sliceProdObj_hom_other j f hk hother x y) u j ≍ u := by
    simp only [sliceProdObj, dif_pos]
    exact cast_heq _ _
  have hv : sliceProdObj j (prodHomFamily f (sliceProdObj j f hk hother y)
        (sliceProdObj j f hk hother z))
      hyz (sliceProdObj_hom_other j f hk hother y z) v j ≍ v := by
    simp only [sliceProdObj, dif_pos]
    exact cast_heq _ _
  exact eq_of_heq (hl.trans (factorComp_heq hk hx hy hz hu hv).symm)

private theorem slice_prod_id_other {s : FactorState} (j k : ℕ) (f : EventuallyPtFamily)
    (hk : f.val k = s) (hother : ∀ i ≠ k, IsPtOrMonoid (f.val i))
    (hj : j ≠ k) (x : FactorState.obj s)
    {hHom : FactorState.hom (sliceProdObj k f hk hother x k)
        (sliceProdObj k f hk hother x k) = FactorState.hom x x}
    {hother' : ∀ i ≠ k, IsPtOrMonoid (FactorState.hom (sliceProdObj k f hk hother x i)
        (sliceProdObj k f hk hother x i))} :
    sliceProdObj k (prodHomFamily f (sliceProdObj k f hk hother x)
        (sliceProdObj k f hk hother x)) hHom hother' (FactorState.idMor x) j =
      FactorState.idMor (sliceProdObj k f hk hother x j) := by
  have hx : sliceProdObj k f hk hother x j = topElem (f.val j) (hother j hj) := by
    simp only [sliceProdObj, dif_neg hj]
  have hl : sliceProdObj k (prodHomFamily f (sliceProdObj k f hk hother x)
        (sliceProdObj k f hk hother x)) hHom hother' (FactorState.idMor x) j =
      topElem (FactorState.hom (sliceProdObj k f hk hother x j)
        (sliceProdObj k f hk hother x j)) (hother' j hj) := by
    simp only [sliceProdObj, prodHomFamily, dif_neg hj]
  have hhom : FactorState.hom (sliceProdObj k f hk hother x j)
        (sliceProdObj k f hk hother x j) =
      FactorState.hom (topElem (f.val j) (hother j hj))
        (topElem (f.val j) (hother j hj)) := by
    rw [hx]
  have ht : topElem (FactorState.hom (sliceProdObj k f hk hother x j)
          (sliceProdObj k f hk hother x j)) (hother' j hj) ≍
        topElem (FactorState.hom (topElem (f.val j) (hother j hj))
          (topElem (f.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)) :=
    topElem_heq hhom (hother' j hj) (isPtOrMonoid_hom (hother j hj))
  have hid : topElem (FactorState.hom (topElem (f.val j) (hother j hj))
          (topElem (f.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)) =
        FactorState.idMor (topElem (f.val j) (hother j hj)) :=
    (topElem_id (hother j hj)).symm
  have hr : FactorState.idMor (topElem (f.val j) (hother j hj)) ≍
        FactorState.idMor (sliceProdObj k f hk hother x j) :=
    factorId_heq rfl (heq_of_eq hx.symm)
  exact eq_of_heq ((heq_of_eq hl).trans (ht.trans ((heq_of_eq hid).trans hr)))

private theorem slice_prod_comp_other {s : FactorState} (j k : ℕ) (f' : EventuallyPtFamily)
    (hk : f'.val k = s) (hother : ∀ i ≠ k, IsPtOrMonoid (f'.val i))
    (hj : j ≠ k) {x y z : FactorState.obj s}
    (u : FactorState.obj (FactorState.hom x y))
    (v : FactorState.obj (FactorState.hom y z))
    {hxz : FactorState.hom (sliceProdObj k f' hk hother x k)
        (sliceProdObj k f' hk hother z k) = FactorState.hom x z}
    {hxy : FactorState.hom (sliceProdObj k f' hk hother x k)
        (sliceProdObj k f' hk hother y k) = FactorState.hom x y}
    {hyz : FactorState.hom (sliceProdObj k f' hk hother y k)
        (sliceProdObj k f' hk hother z k) = FactorState.hom y z}
    {hother_xz : ∀ i ≠ k, IsPtOrMonoid (FactorState.hom (sliceProdObj k f' hk hother x i)
        (sliceProdObj k f' hk hother z i))}
    {hother_xy : ∀ i ≠ k, IsPtOrMonoid (FactorState.hom (sliceProdObj k f' hk hother x i)
        (sliceProdObj k f' hk hother y i))}
    {hother_yz : ∀ i ≠ k, IsPtOrMonoid (FactorState.hom (sliceProdObj k f' hk hother y i)
        (sliceProdObj k f' hk hother z i))} :
    sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother x)
        (sliceProdObj k f' hk hother z))
      hxz hother_xz (FactorState.compMor u v) j =
      FactorState.compMor
        (sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother x)
            (sliceProdObj k f' hk hother y))
          hxy hother_xy u j)
        (sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother y)
            (sliceProdObj k f' hk hother z))
          hyz hother_yz v j) := by
  have hx : sliceProdObj k f' hk hother x j = topElem (f'.val j) (hother j hj) := by
    simp only [sliceProdObj, dif_neg hj]
  have hy : sliceProdObj k f' hk hother y j = topElem (f'.val j) (hother j hj) := by
    simp only [sliceProdObj, dif_neg hj]
  have hz : sliceProdObj k f' hk hother z j = topElem (f'.val j) (hother j hj) := by
    simp only [sliceProdObj, dif_neg hj]
  have hl : sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother x)
        (sliceProdObj k f' hk hother z)) hxz hother_xz (FactorState.compMor u v) j =
      topElem (FactorState.hom (sliceProdObj k f' hk hother x j)
        (sliceProdObj k f' hk hother z j)) (hother_xz j hj) := by
    simp only [sliceProdObj, prodHomFamily, dif_neg hj]
  have hu : sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother x)
        (sliceProdObj k f' hk hother y)) hxy hother_xy u j =
      topElem (FactorState.hom (sliceProdObj k f' hk hother x j)
        (sliceProdObj k f' hk hother y j)) (hother_xy j hj) := by
    simp only [sliceProdObj, prodHomFamily, dif_neg hj]
  have hv : sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother y)
        (sliceProdObj k f' hk hother z)) hyz hother_yz v j =
      topElem (FactorState.hom (sliceProdObj k f' hk hother y j)
        (sliceProdObj k f' hk hother z j)) (hother_yz j hj) := by
    simp only [sliceProdObj, prodHomFamily, dif_neg hj]
  have hhom_xz : FactorState.hom (sliceProdObj k f' hk hother x j)
        (sliceProdObj k f' hk hother z j) =
      FactorState.hom (topElem (f'.val j) (hother j hj))
        (topElem (f'.val j) (hother j hj)) := by rw [hx, hz]
  have hhom_xy : FactorState.hom (sliceProdObj k f' hk hother x j)
        (sliceProdObj k f' hk hother y j) =
      FactorState.hom (topElem (f'.val j) (hother j hj))
        (topElem (f'.val j) (hother j hj)) := by rw [hx, hy]
  have hhom_yz : FactorState.hom (sliceProdObj k f' hk hother y j)
        (sliceProdObj k f' hk hother z j) =
      FactorState.hom (topElem (f'.val j) (hother j hj))
        (topElem (f'.val j) (hother j hj)) := by rw [hy, hz]
  have htxz : topElem (FactorState.hom (sliceProdObj k f' hk hother x j)
          (sliceProdObj k f' hk hother z j)) (hother_xz j hj) ≍
        topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
          (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)) :=
    topElem_heq hhom_xz _ _
  have htxy : topElem (FactorState.hom (sliceProdObj k f' hk hother x j)
          (sliceProdObj k f' hk hother y j)) (hother_xy j hj) ≍
        topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
          (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)) :=
    topElem_heq hhom_xy _ _
  have htyz : topElem (FactorState.hom (sliceProdObj k f' hk hother y j)
          (sliceProdObj k f' hk hother z j)) (hother_yz j hj) ≍
        topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
          (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)) :=
    topElem_heq hhom_yz _ _
  have hu' : sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother x)
        (sliceProdObj k f' hk hother y)) hxy hother_xy u j ≍
      topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
        (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)) :=
    (heq_of_eq hu).trans htxy
  have hv' : sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother y)
        (sliceProdObj k f' hk hother z)) hyz hother_yz v j ≍
      topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
        (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)) :=
    (heq_of_eq hv).trans htyz
  have hcomp : topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
          (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)) =
        FactorState.compMor
          (topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
            (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)))
          (topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
            (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj))) :=
    (topElem_comp (hother j hj)).symm
  have hr : FactorState.compMor
        (topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
          (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj)))
        (topElem (FactorState.hom (topElem (f'.val j) (hother j hj))
          (topElem (f'.val j) (hother j hj))) (isPtOrMonoid_hom (hother j hj))) ≍
      FactorState.compMor
        (sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother x)
          (sliceProdObj k f' hk hother y)) hxy hother_xy u j)
        (sliceProdObj k (prodHomFamily f' (sliceProdObj k f' hk hother y)
          (sliceProdObj k f' hk hother z)) hyz hother_yz v j) :=
    (factorComp_heq rfl (heq_of_eq hx) (heq_of_eq hy) (heq_of_eq hz) hu' hv').symm
  exact eq_of_heq ((heq_of_eq hl).trans (htxz.trans ((heq_of_eq hcomp).trans hr)))

private def sliceMapObj (k : ℕ) :
    ∀ {s₁ s₂ : StepState}, SliceRel k s₁ s₂ → Obj s₁ → Obj s₂
  | _, _, .top, x => cond x (k + 1) k
  | _, _, .prod _ f hk hother, x => sliceProdObj k f hk hother x

private def sliceMapHom (k : ℕ) :
    ∀ {s₁ s₂ : StepState} (φ : SliceRel k s₁ s₂) (x y : Obj s₁),
      SliceRel k (hom x y) (hom (sliceMapObj k φ x) (sliceMapObj k φ y))
  | _, _, .top, x, y =>
    SliceRel.prod (FactorState.hom (s := .monoid (k + 2)) x y)
      (qHomFamily (cond x (k + 1) k) (cond y (k + 1) k))
      (by
        change qHomAt (cond x (k + 1) k) (cond y (k + 1) k) k =
          FactorState.hom (s := .monoid (k + 2)) x y
        unfold qHomAt
        cases x <;> cases y <;> simp [FactorState.hom])
      (fun j _ ↦ isPtOrMonoid_qHomAt _ _ j)
  | _, _, .prod _ f hk hother, x, y =>
    SliceRel.prod (FactorState.hom x y) (prodHomFamily f
      (sliceProdObj k f hk hother x) (sliceProdObj k f hk hother y))
      (sliceProdObj_hom_at_k k f hk hother x y)
      (sliceProdObj_hom_other k f hk hother x y)

private theorem sliceMapId (k : ℕ) :
    ∀ {s₁ s₂ : StepState} (φ : SliceRel k s₁ s₂) (x : Obj s₁),
      sliceMapObj k (sliceMapHom k φ x x) (idMor x) = idMor (sliceMapObj k φ x)
  | _, _, .top, x => by
    funext j
    rcases lt_trichotomy j k with hjlt | rfl | hjgt
    · have hne : j ≠ k := Nat.ne_of_lt hjlt
      dsimp only [sliceMapObj, sliceMapHom, idMor, StepState.stepId]
      simp only [sliceProdObj, dif_neg hne]
      have hx1 : decide (j < cond x (k + 1) k) = true := by
        cases x <;> simp [hjlt, Nat.lt_succ_of_lt hjlt]
      have hlt_min : j < min (cond x (k + 1) k) (cond x (k + 1) k) := by
        cases x <;> simp [hjlt, Nat.lt_succ_of_lt hjlt]
      have hq : qHomAt (cond x (k + 1) k) (cond x (k + 1) k) j =
          .monoid (j + 1) := qHomAt_eq_monoid_of_lt hlt_min
      exact slice_top_id_lt j (cond x (k + 1) k) hq _ hx1
    · simp only [sliceMapObj, sliceMapHom, sliceProdObj, dif_pos]
      cases x
      · have hsub : Subsingleton (FactorState.obj (qHomAt j j j)) := by
          rw [qHomAt_eq_pt_of_le (min_le_left j j)]
          exact inferInstanceAs (Subsingleton Unit)
        exact hsub.elim _ _
      · exact slice_top_id_diag j
          (qHomAt_eq_monoid_of_lt (lt_min (Nat.lt_succ_self j) (Nat.lt_succ_self j)))
    · have hle : min (cond x (k + 1) k) (cond x (k + 1) k) ≤ j := by
        cases x <;> simp <;> omega
      have hpt : qHomAt (cond x (k + 1) k) (cond x (k + 1) k) j = .pt :=
        qHomAt_eq_pt_of_le hle
      have hsub : Subsingleton (FactorState.obj
          (qHomAt (cond x (k + 1) k) (cond x (k + 1) k) j)) := by
        rw [hpt]
        exact inferInstanceAs (Subsingleton Unit)
      exact hsub.elim _ _
  | _, _, .prod _ f hk hother, x => by
    funext j
    by_cases hj : j = k
    · subst hj
      dsimp only [sliceMapObj, sliceMapHom, prodHomFamily, idMor, StepState.stepId]
      exact slice_prod_id_at_k j f hk hother x
        (sliceProdObj_hom_at_k j f hk hother x x)
        (sliceProdObj_hom_other j f hk hother x x)
    · dsimp only [sliceMapObj, sliceMapHom, prodHomFamily, idMor, StepState.stepId]
      exact slice_prod_id_other j k f hk hother hj x

private theorem sliceMapComp (k : ℕ) :
    ∀ {s₁ s₂ : StepState} (φ : SliceRel k s₁ s₂) {x y z : Obj s₁}
      (f : Obj (hom x y)) (g : Obj (hom y z)),
      sliceMapObj k (sliceMapHom k φ x z) (compMor f g) =
        compMor (sliceMapObj k (sliceMapHom k φ x y) f)
          (sliceMapObj k (sliceMapHom k φ y z) g)
  | _, _, .top, x, y, z, f, g => by
    funext j
    rcases lt_trichotomy j k with hjlt | rfl | hjgt
    · have hne : j ≠ k := Nat.ne_of_lt hjlt
      dsimp only [sliceMapObj, sliceMapHom, compMor, StepState.stepComp]
      simp only [sliceProdObj, dif_neg hne]
      have hx1 : decide (j < cond x (k + 1) k) = true := by
        cases x <;> simp [hjlt, Nat.lt_succ_of_lt hjlt]
      have hy1 : decide (j < cond y (k + 1) k) = true := by
        cases y <;> simp [hjlt, Nat.lt_succ_of_lt hjlt]
      have hz1 : decide (j < cond z (k + 1) k) = true := by
        cases z <;> simp [hjlt, Nat.lt_succ_of_lt hjlt]
      exact slice_top_comp_lt j _ _ _ hx1 hy1 hz1 _ _ _
    · dsimp only [sliceMapObj, sliceMapHom, compMor, StepState.stepComp]
      simp only [sliceProdObj, dif_pos]
      cases x <;> cases y <;> cases z
      · have hpt : qHomAt j j j = .pt := qHomAt_eq_pt_of_le (min_le_left j j)
        have hsub : Subsingleton (FactorState.obj (qHomAt j j j)) := by
          rw [hpt]; exact inferInstanceAs (Subsingleton Unit)
        exact hsub.elim _ _
      · have hpt : qHomAt j (j + 1) j = .pt := qHomAt_eq_pt_of_le (min_le_left j (j + 1))
        have hsub : Subsingleton (FactorState.obj (qHomAt j (j + 1) j)) := by
          rw [hpt]; exact inferInstanceAs (Subsingleton Unit)
        exact hsub.elim _ _
      · have hpt : qHomAt j j j = .pt := qHomAt_eq_pt_of_le (min_le_left j j)
        have hsub : Subsingleton (FactorState.obj (qHomAt j j j)) := by
          rw [hpt]; exact inferInstanceAs (Subsingleton Unit)
        exact hsub.elim _ _
      · have hpt : qHomAt j (j + 1) j = .pt := qHomAt_eq_pt_of_le (min_le_left j (j + 1))
        have hsub : Subsingleton (FactorState.obj (qHomAt j (j + 1) j)) := by
          rw [hpt]; exact inferInstanceAs (Subsingleton Unit)
        exact hsub.elim _ _
      · have hpt : qHomAt (j + 1) j j = .pt := qHomAt_eq_pt_of_le (min_le_right (j + 1) j)
        have hsub : Subsingleton (FactorState.obj (qHomAt (j + 1) j j)) := by
          rw [hpt]; exact inferInstanceAs (Subsingleton Unit)
        exact hsub.elim _ _
      · exact slice_top_comp_diag_tft j
          (qHomAt_eq_monoid_of_lt (lt_min (Nat.lt_succ_self j) (Nat.lt_succ_self j)))
          (qHomAt_eq_pt_of_le (min_le_right (j + 1) j))
          (qHomAt_eq_pt_of_le (min_le_left j (j + 1))) f g
      · have hpt : qHomAt (j + 1) j j = .pt := qHomAt_eq_pt_of_le (min_le_right (j + 1) j)
        have hsub : Subsingleton (FactorState.obj (qHomAt (j + 1) j j)) := by
          rw [hpt]; exact inferInstanceAs (Subsingleton Unit)
        exact hsub.elim _ _
      · exact slice_top_comp_diag_ttt j
          (qHomAt_eq_monoid_of_lt (lt_min (Nat.lt_succ_self j) (Nat.lt_succ_self j)))
          (qHomAt_eq_monoid_of_lt (lt_min (Nat.lt_succ_self j) (Nat.lt_succ_self j)))
          (qHomAt_eq_monoid_of_lt (lt_min (Nat.lt_succ_self j) (Nat.lt_succ_self j))) f g
    · have hle : min (cond x (k + 1) k) (cond z (k + 1) k) ≤ j := by
        cases x <;> cases z <;> simp <;> omega
      have hpt : qHomAt (cond x (k + 1) k) (cond z (k + 1) k) j = .pt :=
        qHomAt_eq_pt_of_le hle
      have hsub : Subsingleton (FactorState.obj
          (qHomAt (cond x (k + 1) k) (cond z (k + 1) k) j)) := by
        rw [hpt]
        exact inferInstanceAs (Subsingleton Unit)
      exact hsub.elim _ _
  | _, _, .prod _ f' hk hother, _, _, _, f, g => by
    funext j
    by_cases hj : j = k
    · subst hj
      dsimp only [sliceMapObj, sliceMapHom, compMor, StepState.stepComp, prodHomFamily]
      exact slice_prod_comp_at_k j f' hk hother f g _ _ _
    · dsimp only [sliceMapObj, sliceMapHom, compMor, StepState.stepComp, prodHomFamily]
      exact slice_prod_comp_other j k f' hk hother hj f g

/-- Slice inclusion functor `sliceFunctor k : .factor (.monoid (k + 2)) → StepState.qFull`
sending `false ↦ k` (`e^{(k)}`) and `true ↦ k + 1` (`e^{(k+1)}`). -/
def sliceFunctor (k : ℕ) : GlobularFunctor StepState StepState where
  Rel := SliceRel k
  mapObj := sliceMapObj k
  mapHom := sliceMapHom k
  map_id := sliceMapId k
  map_comp := sliceMapComp k

/-- `StepProductQ` is NOT `n`-truncated for any finite `n : ℕ` (`¬ ∃ n, IsNTruncated n .qFull`). -/
theorem qFull_not_nTruncated : ¬ ∃ n : ℕ, IsNTruncated n StepState.qFull := by
  rintro ⟨n, hn⟩
  have hcoll := (absorbingMonoid_collapse_le (k := n + 1) (n := n)
    (Nat.le_add_left 1 n) (Nat.le_succ n) hn (sliceFunctor n) SliceRel.top).2
  have hlt := isHereditarilyGaunt_qFull.isObjGaunt hcoll
  change n = n + 1 at hlt
  omega

/-- **Theorem 12D (Model-Independent Phantom Non-Realization
`theorem12D_stepProductQ_phantom_not_realized`):**
For *every* `PostnikovReflectionSystem StepState.qFull`:
1. The natural-number sequence `x n := n` (`e^{(n)}`) is Postnikov-compatible
   (`ℓ_{n+1}(n+1) ~ ℓ_{n+1}(n)` and `bond n (ℓ_{n+2}(n+1)) ~ ℓ_{n+1}(n)`), yet
2. For every candidate `m : ℕ` (`e^{(m)}`), universal factorization of `prFunctor m` across
   `ℓ_{m+2}` refutes `ObjEquivRel (ℓ_{m+2}(m + 1)) (ℓ_{m+2}(m))`, so the phantom tower
   `y n := ℓ_{n+1}(n)` is never realized by any object of `StepProductQ`. -/
theorem theorem12D_stepProductQ_phantom_not_realized
    (P : PostnikovReflectionSystem.{0, u₁, 0} StepState.qFull) :
    (∀ n : ℕ, ObjEquivRel
        ((P.level n).unit.mapObj (P.level n).unitRel (n + 1))
        ((P.level n).unit.mapObj (P.level n).unitRel n) ∧
      ObjEquivRel
        ((P.bond n).mapObj (P.bondRel n)
          ((P.level (n + 1)).unit.mapObj (P.level (n + 1)).unitRel (n + 1)))
        ((P.level n).unit.mapObj (P.level n).unitRel n)) ∧
      (∀ m : ℕ, ¬ ObjEquivRel
        ((P.level (m + 1)).unit.mapObj (P.level (m + 1)).unitRel (m + 1))
        ((P.level (m + 1)).unit.mapObj (P.level (m + 1)).unitRel m)) ∧
      (¬ ∃ m : ℕ, ∀ n : ℕ, ObjEquivRel
        ((P.level n).unit.mapObj (P.level n).unitRel n)
        ((P.level n).unit.mapObj (P.level n).unitRel m)) := by
  have hcompat : ∀ n : ℕ, ObjEquivRel
      ((P.level n).unit.mapObj (P.level n).unitRel (n + 1))
      ((P.level n).unit.mapObj (P.level n).unitRel n) := by
    intro n
    let G := (P.level n).unit.compLeftZero (sliceFunctor n)
    have hcoll := (absorbingMonoid_collapse_le (k := n + 1) (n := n + 1)
      (Nat.le_add_left 1 n) le_rfl (P.level n).isTruncated G
      ⟨StepState.qFull, SliceRel.top, (P.level n).unitRel⟩).2
    exact hcoll.symm.to_objEquivRel
  have hcompat_pair : ∀ n : ℕ, ObjEquivRel
      ((P.level n).unit.mapObj (P.level n).unitRel (n + 1))
      ((P.level n).unit.mapObj (P.level n).unitRel n) ∧
      ObjEquivRel
        ((P.bond n).mapObj (P.bondRel n)
          ((P.level (n + 1)).unit.mapObj (P.level (n + 1)).unitRel (n + 1)))
        ((P.level n).unit.mapObj (P.level n).unitRel n) := fun n ↦
    ⟨hcompat n, (P.bond_compat_iff (fun k ↦ k) n).mpr (hcompat n)⟩
  have hnot_real : ∀ m : ℕ, ¬ ObjEquivRel
      ((P.level (m + 1)).unit.mapObj (P.level (m + 1)).unitRel (m + 1))
      ((P.level (m + 1)).unit.mapObj (P.level (m + 1)).unitRel m) := by
    intro m hm
    have htrunc : IsNTruncated (m + 2) (StepState.factor (.monoid (m + 2))) :=
      isNTruncated_monoid (m + 2)
    rcases (P.level (m + 1)).factor htrunc (prFunctor m) PrRel.top with ⟨Fbar, ψ, hcomm⟩
    have h1 := Fbar.map_objEquivRel ψ hm
    have h2 : ObjEquivRel
        ((prFunctor m).mapObj PrRel.top (m + 1))
        ((prFunctor m).mapObj PrRel.top m) :=
      (hcomm (m + 1)).symm.trans (h1.trans (hcomm m))
    have heq := (isHereditarilyGaunt_monoid (m + 2)).isObjGaunt.objEquivRel_eq.mp h2
    change decide (m < m + 1) = decide (m < m) at heq
    simp at heq
  refine ⟨hcompat_pair, hnot_real, ?_⟩
  rintro ⟨m, hm⟩
  exact hnot_real m (hm (m + 1))

/-- State correspondence relation unifying truncation unit `qTruncUnit n`, bonding map
`qTruncBond n`, and canonical inclusion `qTruncIncl n` via coordinate truncation `.prod`. -/
inductive QTruncRel : StepState → StepState → Type
  | unit (n : ℕ) : QTruncRel StepState.qFull (StepState.qTrunc (n + 1))
  | bond (n : ℕ) : QTruncRel (StepState.qTrunc (n + 2)) (StepState.qTrunc (n + 1))
  | incl (n : ℕ) : QTruncRel (StepState.qTrunc (n + 1)) StepState.qFull
  | prod (f g : EventuallyPtFamily) (h : ∀ j : ℕ, g.val j = f.val j ∨ g.val j = .pt) :
      QTruncRel (StepState.prod f) (StepState.prod g)

/-- `0`-cell projection on `.prod` preserving matching coordinates and collapsing truncated tail
coordinates to `()`. -/
def prodTruncObj (f g : EventuallyPtFamily)
    (h : ∀ j : ℕ, g.val j = f.val j ∨ g.val j = .pt)
    (x : ∀ j : ℕ, FactorState.obj (f.val j)) :
    ∀ j : ℕ, FactorState.obj (g.val j) := fun j ↦
  if hpt : g.val j = .pt then
    cast (congrArg FactorState.obj hpt.symm) ()
  else
    cast (congrArg FactorState.obj ((h j).resolve_right hpt).symm) (x j)

/-- Hom-state compatibility for `prodTruncObj`. -/
private theorem prodTruncObj_hom (f g : EventuallyPtFamily)
    (h : ∀ j : ℕ, g.val j = f.val j ∨ g.val j = .pt)
    (x y : ∀ j : ℕ, FactorState.obj (f.val j)) :
    ∀ j : ℕ,
      (prodHomFamily g (prodTruncObj f g h x) (prodTruncObj f g h y)).val j =
        (prodHomFamily f x y).val j ∨
      (prodHomFamily g (prodTruncObj f g h x) (prodTruncObj f g h y)).val j = .pt := by
  intro j
  change FactorState.hom (prodTruncObj f g h x j) (prodTruncObj f g h y j) =
      FactorState.hom (x j) (y j) ∨
    FactorState.hom (prodTruncObj f g h x j) (prodTruncObj f g h y j) = .pt
  by_cases hpt : g.val j = .pt
  · right
    simp only [prodTruncObj, dif_pos hpt]
    exact factor_hom_eq_pt_of_eq hpt _ _
  · left
    simp only [prodTruncObj, dif_neg hpt]
    exact factorHom_cast ((h j).resolve_right hpt) (x j) (y j)

/-- Helper proving `prodTruncObj` preserves `idMor` at coordinate `j`. -/
private theorem prodTrunc_id_coord_aux {s₁ s₂ : FactorState} (h : s₂ = s₁ ∨ s₂ = .pt)
    (x : FactorState.obj s₁) (d : Decidable (s₂ = .pt))
    (hHom : FactorState.hom
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x))
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x)) =
      FactorState.hom x x ∨
      FactorState.hom
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x))
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x)) = .pt) :
    (if hpt : FactorState.hom
          (@dite (FactorState.obj s₂) (s₂ = .pt) d
            (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
            (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x))
          (@dite (FactorState.obj s₂) (s₂ = .pt) d
            (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
            (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x)) = .pt then
        cast (congrArg FactorState.obj hpt.symm) ()
      else
        cast (congrArg FactorState.obj (hHom.resolve_right hpt).symm) (FactorState.idMor x)) =
      FactorState.idMor
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x)) := by
  cases d with
  | isTrue hpt0 =>
    subst hpt0
    rfl
  | isFalse hpt0 =>
    rcases h with rfl | hpt'
    · dsimp only [dite] at hHom ⊢
      have aux : ∀ (a : FactorState.obj s₂), a = x →
          ∀ hHom' : FactorState.hom a a = FactorState.hom x x ∨ FactorState.hom a a = .pt,
          (if hpt : FactorState.hom a a = .pt then cast (congrArg FactorState.obj hpt.symm) ()
            else cast (congrArg FactorState.obj (hHom'.resolve_right hpt).symm)
              (FactorState.idMor x)) =
            FactorState.idMor a := by
        intro a ha hHom'
        subst ha
        split_ifs with hhom
        · exact (by rw [hhom]; exact inferInstanceAs (Subsingleton Unit) : Subsingleton _).elim _ _
        · exact cast_eq _ _
      exact aux _ (cast_eq _ x) hHom
    · exact False.elim (hpt0 hpt')

private theorem prodTrunc_id_coord {s₁ s₂ : FactorState} (h : s₂ = s₁ ∨ s₂ = .pt)
    (x : FactorState.obj s₁) :
    let mx := if hpt0 : s₂ = .pt then cast (congrArg FactorState.obj hpt0.symm) ()
      else cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x
    have hHom : FactorState.hom mx mx = FactorState.hom x x ∨ FactorState.hom mx mx = .pt := by
      by_cases hpt0 : s₂ = .pt
      · right; simp only [mx, dif_pos hpt0]; exact factor_hom_eq_pt_of_eq hpt0 _ _
      · left; simp only [mx, dif_neg hpt0]; exact factorHom_cast (h.resolve_right hpt0) x x
    (if hpt : FactorState.hom mx mx = .pt then cast (congrArg FactorState.obj hpt.symm) ()
      else cast (congrArg FactorState.obj (hHom.resolve_right hpt).symm) (FactorState.idMor x)) =
      FactorState.idMor mx := by
  intro mx hHom
  exact prodTrunc_id_coord_aux h x _ hHom

/-- Helper proving `prodTruncObj` preserves `compMor` at coordinate `j`. -/
private theorem prodTrunc_comp_coord_aux {s₁ s₂ : FactorState} (h : s₂ = s₁ ∨ s₂ = .pt)
    {x y z : FactorState.obj s₁}
    (u : FactorState.obj (FactorState.hom x y))
    (v : FactorState.obj (FactorState.hom y z))
    (d : Decidable (s₂ = .pt))
    (hxy : FactorState.hom
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x))
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) y)) =
      FactorState.hom x y ∨
      FactorState.hom
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x))
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) y)) = .pt)
    (hyz : FactorState.hom
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) y))
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) z)) =
      FactorState.hom y z ∨
      FactorState.hom
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) y))
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) z)) = .pt)
    (hxz : FactorState.hom
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x))
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) z)) =
      FactorState.hom x z ∨
      FactorState.hom
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x))
        (@dite (FactorState.obj s₂) (s₂ = .pt) d
          (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
          (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) z)) = .pt) :
    (if hpt : FactorState.hom
          (@dite (FactorState.obj s₂) (s₂ = .pt) d
            (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
            (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x))
          (@dite (FactorState.obj s₂) (s₂ = .pt) d
            (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
            (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) z)) = .pt then
        cast (congrArg FactorState.obj hpt.symm) ()
      else
        cast (congrArg FactorState.obj (hxz.resolve_right hpt).symm)
          (FactorState.compMor u v)) =
      FactorState.compMor
        (if hpt : FactorState.hom
              (@dite (FactorState.obj s₂) (s₂ = .pt) d
                (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
                (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x))
              (@dite (FactorState.obj s₂) (s₂ = .pt) d
                (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
                (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) y)) =
              .pt then
            cast (congrArg FactorState.obj hpt.symm) ()
          else
            cast (congrArg FactorState.obj (hxy.resolve_right hpt).symm) u)
        (if hpt : FactorState.hom
              (@dite (FactorState.obj s₂) (s₂ = .pt) d
                (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
                (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) y))
              (@dite (FactorState.obj s₂) (s₂ = .pt) d
                (fun hpt0 ↦ cast (congrArg FactorState.obj hpt0.symm) ())
                (fun hpt0 ↦ cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) z)) =
              .pt then
            cast (congrArg FactorState.obj hpt.symm) ()
          else
            cast (congrArg FactorState.obj (hyz.resolve_right hpt).symm) v) := by
  cases d with
  | isTrue hpt0 =>
    subst hpt0
    rfl
  | isFalse hpt0 =>
    rcases h with rfl | hpt'
    · dsimp only [dite] at hxy hyz hxz ⊢
      have aux : ∀ (a b c : FactorState.obj s₂), a = x → b = y → c = z →
          ∀ (hxy' : FactorState.hom a b = FactorState.hom x y ∨ FactorState.hom a b = .pt)
            (hyz' : FactorState.hom b c = FactorState.hom y z ∨ FactorState.hom b c = .pt)
            (hxz' : FactorState.hom a c = FactorState.hom x z ∨ FactorState.hom a c = .pt),
          (if hpt : FactorState.hom a c = .pt then cast (congrArg FactorState.obj hpt.symm) ()
            else cast (congrArg FactorState.obj (hxz'.resolve_right hpt).symm)
              (FactorState.compMor u v)) =
            FactorState.compMor
              (if hpt : FactorState.hom a b = .pt then cast (congrArg FactorState.obj hpt.symm) ()
                else cast (congrArg FactorState.obj (hxy'.resolve_right hpt).symm) u)
              (if hpt : FactorState.hom b c = .pt then cast (congrArg FactorState.obj hpt.symm) ()
                else cast (congrArg FactorState.obj (hyz'.resolve_right hpt).symm) v) := by
        intro a b c ha hb hc hxy' hyz' hxz'
        subst ha; subst hb; subst hc
        by_cases hptxz : FactorState.hom a c = .pt
        · rw [dif_pos hptxz]
          exact (by rw [hptxz]; exact inferInstanceAs (Subsingleton Unit) : Subsingleton _).elim _ _
        · rw [dif_neg hptxz]
          by_cases hptxy : FactorState.hom a b = .pt
          · rw [dif_pos hptxy]
            by_cases hptyz : FactorState.hom b c = .pt
            · rw [dif_pos hptyz]
              have hsub1 : Subsingleton (FactorState.obj (FactorState.hom a b)) := by
                rw [show FactorState.hom a b = .pt from hptxy]
                exact inferInstanceAs (Subsingleton Unit)
              have hsub2 : Subsingleton (FactorState.obj (FactorState.hom b c)) := by
                rw [show FactorState.hom b c = .pt from hptyz]
                exact inferInstanceAs (Subsingleton Unit)
              rw [hsub1.elim u (cast (congrArg FactorState.obj hptxy.symm) ()),
                hsub2.elim v (cast (congrArg FactorState.obj hptyz.symm) ())]
              exact cast_eq _ _
            · rw [dif_neg hptyz]
              have hsub1 : Subsingleton (FactorState.obj (FactorState.hom a b)) := by
                rw [show FactorState.hom a b = .pt from hptxy]
                exact inferInstanceAs (Subsingleton Unit)
              rw [hsub1.elim u (cast (congrArg FactorState.obj hptxy.symm) ())]
              simp only [cast_eq]
          · rw [dif_neg hptxy]
            by_cases hptyz : FactorState.hom b c = .pt
            · rw [dif_pos hptyz]
              have hsub2 : Subsingleton (FactorState.obj (FactorState.hom b c)) := by
                rw [show FactorState.hom b c = .pt from hptyz]
                exact inferInstanceAs (Subsingleton Unit)
              rw [hsub2.elim v (cast (congrArg FactorState.obj hptyz.symm) ())]
              simp only [cast_eq]
            · rw [dif_neg hptyz]
              simp only [cast_eq]
      exact aux _ _ _ (cast_eq _ x) (cast_eq _ y) (cast_eq _ z) hxy hyz hxz
    · exact False.elim (hpt0 hpt')

private theorem prodTrunc_comp_coord {s₁ s₂ : FactorState} (h : s₂ = s₁ ∨ s₂ = .pt)
    {x y z : FactorState.obj s₁}
    (u : FactorState.obj (FactorState.hom x y))
    (v : FactorState.obj (FactorState.hom y z)) :
    let mx := if hpt0 : s₂ = .pt then cast (congrArg FactorState.obj hpt0.symm) ()
      else cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) x
    let my := if hpt0 : s₂ = .pt then cast (congrArg FactorState.obj hpt0.symm) ()
      else cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) y
    let mz := if hpt0 : s₂ = .pt then cast (congrArg FactorState.obj hpt0.symm) ()
      else cast (congrArg FactorState.obj (h.resolve_right hpt0).symm) z
    have hxy : FactorState.hom mx my = FactorState.hom x y ∨ FactorState.hom mx my = .pt := by
      by_cases hpt0 : s₂ = .pt
      · right; simp only [mx, my, dif_pos hpt0]; exact factor_hom_eq_pt_of_eq hpt0 _ _
      · left; simp only [mx, my, dif_neg hpt0]; exact factorHom_cast (h.resolve_right hpt0) x y
    have hyz : FactorState.hom my mz = FactorState.hom y z ∨ FactorState.hom my mz = .pt := by
      by_cases hpt0 : s₂ = .pt
      · right; simp only [my, mz, dif_pos hpt0]; exact factor_hom_eq_pt_of_eq hpt0 _ _
      · left; simp only [my, mz, dif_neg hpt0]; exact factorHom_cast (h.resolve_right hpt0) y z
    have hxz : FactorState.hom mx mz = FactorState.hom x z ∨ FactorState.hom mx mz = .pt := by
      by_cases hpt0 : s₂ = .pt
      · right; simp only [mx, mz, dif_pos hpt0]; exact factor_hom_eq_pt_of_eq hpt0 _ _
      · left; simp only [mx, mz, dif_neg hpt0]; exact factorHom_cast (h.resolve_right hpt0) x z
    (if hpt : FactorState.hom mx mz = .pt then cast (congrArg FactorState.obj hpt.symm) ()
      else cast (congrArg FactorState.obj (hxz.resolve_right hpt).symm)
        (FactorState.compMor u v)) =
      FactorState.compMor
        (if hpt : FactorState.hom mx my = .pt then cast (congrArg FactorState.obj hpt.symm) ()
          else cast (congrArg FactorState.obj (hxy.resolve_right hpt).symm) u)
        (if hpt : FactorState.hom my mz = .pt then cast (congrArg FactorState.obj hpt.symm) ()
          else cast (congrArg FactorState.obj (hyz.resolve_right hpt).symm) v) := by
  intro mx my mz hxy hyz hxz
  exact prodTrunc_comp_coord_aux h u v _ hxy hyz hxz

/-- Truncation compatibility of `qHomAt` when capping object indices at `n`. -/
private theorem qHomAt_trunc_compat (m r n j : ℕ) :
    qHomAt (min m n) (min r n) j = qHomAt m r j ∨ qHomAt (min m n) (min r n) j = .pt := by
  by_cases hjn : j < min (min m n) (min r n)
  · left
    have hjmr : j < min m r := lt_of_lt_of_le hjn (by omega)
    rw [qHomAt_eq_monoid_of_lt hjn, qHomAt_eq_monoid_of_lt hjmr]
  · right
    exact qHomAt_eq_pt_of_le (Nat.le_of_not_gt hjn)

private def qTruncMapObj :
    ∀ {s₁ s₂ : StepState}, QTruncRel s₁ s₂ → Obj s₁ → Obj s₂
  | _, _, .unit n, x => ⟨Min.min (x : ℕ) n, Nat.lt_succ_of_le (Nat.min_le_right (x : ℕ) n)⟩
  | _, _, .bond n, x => ⟨Min.min x.val n, Nat.lt_succ_of_le (Nat.min_le_right x.val n)⟩
  | _, _, .incl _, x => x.val
  | _, _, .prod f g h, x => prodTruncObj f g h x

private def qTruncMapHom :
    ∀ {s₁ s₂ : StepState} (φ : QTruncRel s₁ s₂) (x y : Obj s₁),
      QTruncRel (hom x y) (hom (qTruncMapObj φ x) (qTruncMapObj φ y))
  | _, _, .unit n, x, y =>
    QTruncRel.prod (qHomFamily (x : ℕ) (y : ℕ))
      (qHomFamily (Min.min (x : ℕ) n) (Min.min (y : ℕ) n))
      (qHomAt_trunc_compat (x : ℕ) (y : ℕ) n)
  | _, _, .bond n, x, y =>
    QTruncRel.prod (qHomFamily x.val y.val) (qHomFamily (Min.min x.val n) (Min.min y.val n))
      (qHomAt_trunc_compat x.val y.val n)
  | _, _, .incl _, x, y =>
    QTruncRel.prod (qHomFamily x.val y.val) (qHomFamily x.val y.val)
      (fun _ ↦ Or.inl rfl)
  | _, _, .prod f g h, x, y =>
    QTruncRel.prod (prodHomFamily f x y) (prodHomFamily g (prodTruncObj f g h x)
      (prodTruncObj f g h y)) (prodTruncObj_hom f g h x y)

private theorem qHom_id_lt (j m r : ℕ)
    (hm : decide (j < m) = true) (hr : decide (j < r) = true)
    (h : qHomAt r r j = qHomAt m m j) :
    cast (congrArg FactorState.obj h.symm)
        (FactorState.idMor (s := .monoid (j + 2)) (decide (j < m))) =
      FactorState.idMor (s := .monoid (j + 2)) (decide (j < r)) := by
  revert h
  unfold qHomAt
  rw [hm, hr]
  intro _
  cases j <;> rfl

private theorem qHom_comp_ttt (j x y z x' y' z' : ℕ)
    (hx : decide (j < x) = true) (hy : decide (j < y) = true) (hz : decide (j < z) = true)
    (hx' : decide (j < x') = true) (hy' : decide (j < y') = true) (hz' : decide (j < z') = true)
    (hxz : qHomAt x' z' j = qHomAt x z j)
    (hxy : qHomAt x' y' j = qHomAt x y j)
    (hyz : qHomAt y' z' j = qHomAt y z j)
    (u : FactorState.obj (qHomAt x y j)) (v : FactorState.obj (qHomAt y z j)) :
    cast (congrArg FactorState.obj hxz.symm)
        (FactorState.compMor (s := .monoid (j + 2))
          (x := decide (j < x)) (y := decide (j < y)) (z := decide (j < z)) u v) =
      FactorState.compMor (s := .monoid (j + 2))
        (x := decide (j < x')) (y := decide (j < y')) (z := decide (j < z'))
        (cast (congrArg FactorState.obj hxy.symm) u)
        (cast (congrArg FactorState.obj hyz.symm) v) := by
  revert u v hxz hxy hyz
  unfold qHomAt
  rw [hx, hy, hz]
  try rw [hx']
  try rw [hy']
  try rw [hz']
  intro u v _ _ _
  simp only [cast_eq]

private theorem qHom_comp_tft (j x y z x' y' z' : ℕ)
    (hx : decide (j < x) = true) (hy : decide (j < y) = false) (hz : decide (j < z) = true)
    (hx' : decide (j < x') = true) (hy' : decide (j < y') = false) (hz' : decide (j < z') = true)
    (hxz : qHomAt x' z' j = qHomAt x z j)
    (hxy : qHomAt x' y' j = .pt) (hyz : qHomAt y' z' j = .pt)
    (u : FactorState.obj (qHomAt x y j)) (v : FactorState.obj (qHomAt y z j)) :
    cast (congrArg FactorState.obj hxz.symm)
        (FactorState.compMor (s := .monoid (j + 2))
          (x := decide (j < x)) (y := decide (j < y)) (z := decide (j < z)) u v) =
      FactorState.compMor (s := .monoid (j + 2))
        (x := decide (j < x')) (y := decide (j < y')) (z := decide (j < z'))
        (cast (congrArg FactorState.obj hxy.symm) ())
        (cast (congrArg FactorState.obj hyz.symm) ()) := by
  revert u v hxz hxy hyz
  unfold qHomAt
  rw [hx, hy, hz]
  try rw [hx']
  try rw [hy']
  try rw [hz']
  intro u v _ _ _
  simp only [cast_eq]
  rfl

private theorem qTrunc_id_coord (n x j : ℕ) :
    prodTruncObj (qHomFamily x x) (qHomFamily (min x n) (min x n))
        (qHomAt_trunc_compat x x n)
        (fun i ↦ FactorState.idMor (s := .monoid (i + 2)) (decide (i < x))) j =
      FactorState.idMor (s := .monoid (j + 2)) (decide (j < min x n)) := by
  by_cases hjn : j < min x n
  · have hjx : j < x := lt_of_lt_of_le hjn (Nat.min_le_left x n)
    have hjmn : j < min (min x n) (min x n) := by omega
    have hpt : qHomAt (min x n) (min x n) j ≠ .pt := by
      rw [qHomAt_eq_monoid_of_lt hjmn]
      intro hc; cases hc
    simp only [prodTruncObj, qHomFamily, dif_neg hpt]
    exact qHom_id_lt j x (min x n) (decide_eq_true hjx) (decide_eq_true hjn)
      ((qHomAt_trunc_compat x x n j).resolve_right hpt)
  · have hle : min (min x n) (min x n) ≤ j := by omega
    have hpt : qHomAt (min x n) (min x n) j = .pt := qHomAt_eq_pt_of_le hle
    have hsub : Subsingleton (FactorState.obj (qHomAt (min x n) (min x n) j)) := by
      rw [hpt]; exact inferInstanceAs (Subsingleton Unit)
    exact hsub.elim _ _

private theorem qTrunc_comp_coord (n x y z j : ℕ)
    (f : ∀ i : ℕ, FactorState.obj (qHomAt x y i))
    (g : ∀ i : ℕ, FactorState.obj (qHomAt y z i)) :
    prodTruncObj (qHomFamily x z) (qHomFamily (min x n) (min z n))
        (qHomAt_trunc_compat x z n)
        (fun i ↦ FactorState.compMor (s := .monoid (i + 2))
          (x := decide (i < x)) (y := decide (i < y)) (z := decide (i < z)) (f i) (g i)) j =
      FactorState.compMor (s := .monoid (j + 2))
        (x := decide (j < min x n)) (y := decide (j < min y n)) (z := decide (j < min z n))
        (prodTruncObj (qHomFamily x y) (qHomFamily (min x n) (min y n))
          (qHomAt_trunc_compat x y n) f j)
        (prodTruncObj (qHomFamily y z) (qHomFamily (min y n) (min z n))
          (qHomAt_trunc_compat y z n) g j) := by
  by_cases hjn : j < min (min x n) (min z n)
  · have hjx : j < x := lt_of_lt_of_le hjn (by omega)
    have hjz : j < z := lt_of_lt_of_le hjn (by omega)
    have hptxz : qHomAt (min x n) (min z n) j ≠ .pt := by
      rw [qHomAt_eq_monoid_of_lt hjn]
      intro hc; cases hc
    simp only [prodTruncObj, qHomFamily, dif_neg hptxz]
    by_cases hjy : j < min y n
    · have hjy' : j < y := lt_of_lt_of_le hjy (Nat.min_le_left y n)
      have hxy : j < min (min x n) (min y n) := by omega
      have hyz : j < min (min y n) (min z n) := by omega
      have hptxy : qHomAt (min x n) (min y n) j ≠ .pt := by
        rw [qHomAt_eq_monoid_of_lt hxy]
        intro hc; cases hc
      have hptyz : qHomAt (min y n) (min z n) j ≠ .pt := by
        rw [qHomAt_eq_monoid_of_lt hyz]
        intro hc; cases hc
      simp only [dif_neg hptxy, dif_neg hptyz]
      exact qHom_comp_ttt j x y z (min x n) (min y n) (min z n)
        (decide_eq_true hjx) (decide_eq_true hjy') (decide_eq_true hjz)
        (decide_eq_true (by omega)) (decide_eq_true hjy) (decide_eq_true (by omega))
        ((qHomAt_trunc_compat x z n j).resolve_right hptxz)
        ((qHomAt_trunc_compat x y n j).resolve_right hptxy)
        ((qHomAt_trunc_compat y z n j).resolve_right hptyz)
        (f j) (g j)
    · have hjy_raw : ¬ j < y := by omega
      have hptxy : qHomAt (min x n) (min y n) j = .pt :=
        qHomAt_eq_pt_of_le (by omega)
      have hptyz : qHomAt (min y n) (min z n) j = .pt :=
        qHomAt_eq_pt_of_le (by omega)
      simp only [dif_pos hptxy, dif_pos hptyz]
      exact qHom_comp_tft j x y z (min x n) (min y n) (min z n)
        (decide_eq_true hjx) (decide_eq_false hjy_raw) (decide_eq_true hjz)
        (decide_eq_true (by omega)) (decide_eq_false hjy) (decide_eq_true (by omega))
        ((qHomAt_trunc_compat x z n j).resolve_right hptxz)
        hptxy hptyz (f j) (g j)
  · have hpt : qHomAt (min x n) (min z n) j = .pt :=
      qHomAt_eq_pt_of_le (Nat.le_of_not_gt hjn)
    have hsub : Subsingleton (FactorState.obj (qHomAt (min x n) (min z n) j)) := by
      rw [hpt]; exact inferInstanceAs (Subsingleton Unit)
    exact hsub.elim _ _

private theorem qTruncMapId :
    ∀ {s₁ s₂ : StepState} (φ : QTruncRel s₁ s₂) (x : Obj s₁),
      qTruncMapObj (qTruncMapHom φ x x) (idMor x) = idMor (qTruncMapObj φ x)
  | _, _, .unit n, (x : ℕ) => by
    funext j
    exact qTrunc_id_coord n x j
  | _, _, .bond n, x => by
    funext j
    exact qTrunc_id_coord n x.val j
  | _, _, .incl _, x => by
    funext j
    dsimp only [qTruncMapObj, qTruncMapHom, idMor, StepState.stepId]
    by_cases hj : qHomAt x.val x.val j = .pt
    · simp only [prodTruncObj, qHomFamily, dif_pos hj]
      have hsub : Subsingleton (FactorState.obj (qHomAt x.val x.val j)) := by
        rw [hj]; exact inferInstanceAs (Subsingleton Unit)
      exact hsub.elim _ _
    · simp only [prodTruncObj, qHomFamily, dif_neg hj]
      rfl
  | _, _, .prod f g h, x => by
    funext j
    exact prodTrunc_id_coord (h j) (x j)

private theorem qTruncMapComp :
    ∀ {s₁ s₂ : StepState} (φ : QTruncRel s₁ s₂) {x y z : Obj s₁}
      (f : Obj (hom x y)) (g : Obj (hom y z)),
      qTruncMapObj (qTruncMapHom φ x z) (compMor f g) =
        compMor (qTruncMapObj (qTruncMapHom φ x y) f) (qTruncMapObj (qTruncMapHom φ y z) g)
  | _, _, .unit n, (x : ℕ), (y : ℕ), (z : ℕ), f, g => by
    funext j
    exact qTrunc_comp_coord n x y z j f g
  | _, _, .bond n, x, y, z, f, g => by
    funext j
    exact qTrunc_comp_coord n x.val y.val z.val j f g
  | _, _, .incl _, x, y, z, f, g => by
    funext j
    dsimp only [qTruncMapObj, qTruncMapHom, compMor, StepState.stepComp]
    by_cases hptxz : qHomAt x.val z.val j = .pt
    · simp only [prodTruncObj, qHomFamily, dif_pos hptxz]
      have hsub : Subsingleton (FactorState.obj (qHomAt x.val z.val j)) := by
        rw [hptxz]; exact inferInstanceAs (Subsingleton Unit)
      exact hsub.elim _ _
    · simp only [prodTruncObj, qHomFamily, dif_neg hptxz]
      have hjxz : j < min x.val z.val := by
        by_contra hle
        exact hptxz (qHomAt_eq_pt_of_le (Nat.le_of_not_gt hle))
      by_cases hjy : j < y.val
      · have hptxy : qHomAt x.val y.val j ≠ .pt := by
          rw [qHomAt_eq_monoid_of_lt (lt_min (lt_of_lt_of_le hjxz (min_le_left _ _)) hjy)]
          intro hc; cases hc
        have hptyz : qHomAt y.val z.val j ≠ .pt := by
          rw [qHomAt_eq_monoid_of_lt (lt_min hjy (lt_of_lt_of_le hjxz (min_le_right _ _)))]
          intro hc; cases hc
        simp only [dif_neg hptxy, dif_neg hptyz]
        rfl
      · have hptxy : qHomAt x.val y.val j = .pt := qHomAt_eq_pt_of_le (by omega)
        have hptyz : qHomAt y.val z.val j = .pt := qHomAt_eq_pt_of_le (by omega)
        simp only [dif_pos hptxy, dif_pos hptyz]
        exact qHom_comp_tft j x.val y.val z.val x.val y.val z.val
          (decide_eq_true (lt_of_lt_of_le hjxz (min_le_left _ _)))
          (decide_eq_false hjy)
          (decide_eq_true (lt_of_lt_of_le hjxz (min_le_right _ _)))
          (decide_eq_true (lt_of_lt_of_le hjxz (min_le_left _ _)))
          (decide_eq_false hjy)
          (decide_eq_true (lt_of_lt_of_le hjxz (min_le_right _ _)))
          rfl hptxy hptyz (f j) (g j)
  | _, _, .prod f' g' h, _, _, _, f, g => by
    funext j
    exact prodTrunc_comp_coord (h j) (f j) (g j)

/-- Unified `GlobularFunctor` hosting truncation unit `unit n`, bonding map `bond n`, and
canonical inclusion `incl n`. -/
def qTruncFunctor : GlobularFunctor StepState StepState where
  Rel := QTruncRel
  mapObj := qTruncMapObj
  mapHom := qTruncMapHom
  map_id := qTruncMapId
  map_comp := qTruncMapComp

/-- Exact `(n + 1)`-truncation of `StepState.qTrunc (n + 1)`. -/
theorem isNTruncated_qTrunc_succ (n : ℕ) :
    IsNTruncated (n + 1) (StepState.qTrunc (n + 1)) := by
  intro a b
  refine isNTruncated_prod fun j ↦ ?_
  by_cases hj : j < min a.val b.val
  · rw [show (qHomFamily a.val b.val).val j = qHomAt a.val b.val j from rfl,
      qHomAt_eq_monoid_of_lt hj]
    exact (isNTruncated_monoid (j + 1)).mono (by omega : j + 1 ≤ n)
  · rw [show (qHomFamily a.val b.val).val j = qHomAt a.val b.val j from rfl,
      qHomAt_eq_pt_of_le (Nat.le_of_not_gt hj)]
    exact isNTruncated_pt.mono (Nat.zero_le n)

/-- Universal `(n + 1)`-truncation reflection of `StepState.qFull` realized inside `StepState` by
`StepState.qTrunc (n + 1)`. -/
def stepProductTruncReflection (n : ℕ) :
    TruncReflection.{0, 0, v} (n + 1) StepState.qFull where
  Target := StepState
  targetState := StepState.qTrunc (n + 1)
  isTruncated := isNTruncated_qTrunc_succ n
  unit := qTruncFunctor
  unitRel := QTruncRel.unit n
  factor {D} _ {d} hd F φ := by
    refine ⟨F.compLeftZero qTruncFunctor, ⟨StepState.qFull, QTruncRel.incl n, φ⟩, ?_⟩
    intro m'
    let m : ℕ := m'
    change ObjEquivRel (F.mapObj φ (min m n : ℕ)) (F.mapObj φ m)
    by_cases hmn : m ≤ n
    · rw [Nat.min_eq_left hmn]
      exact ObjEquivRel.refl _
    · have hnm : n ≤ m := Nat.le_of_not_ge hmn
      rw [Nat.min_eq_right hnm]
      have hstep : ∀ k : ℕ, n ≤ k →
          ObjEquiv (F.mapObj φ k) (F.mapObj φ (k + 1)) := by
        intro k hk
        let G := F.compLeftZero (sliceFunctor k)
        exact (absorbingMonoid_collapse_le (k := k + 1) (n := n + 1)
          (Nat.le_add_left 1 k) (Nat.succ_le_succ hk) hd G
          ⟨StepState.qFull, SliceRel.top, φ⟩).2
      have hchain : ∀ d' : ℕ, ObjEquivRel (F.mapObj φ n) (F.mapObj φ (n + d')) := by
        intro d'
        induction d' with
        | zero => exact ObjEquivRel.refl _
        | succ d'' ih =>
          exact ih.trans (hstep (n + d'') (Nat.le_add_right n d'')).to_objEquivRel
      obtain ⟨d', hd'⟩ := Nat.exists_eq_add_of_le hnm
      rw [hd']
      exact hchain d'

/-- Concrete `PostnikovReflectionSystem StepState.qFull` realizing the finite-prefix Postnikov
tower `(qTrunc (n + 1))_{n ≥ 0}` (`π_{\le n+1}(Q) ≃ Q_{< n+1}`). -/
def stepProductPostnikovSystem :
    PostnikovReflectionSystem.{0, 0, v} StepState.qFull where
  level := stepProductTruncReflection
  bond _ := qTruncFunctor
  bondRel n := QTruncRel.bond n
  bond_compat n m' := by
    let m : ℕ := m'
    change ObjEquivRel (s := StepState.qTrunc (n + 1))
      (⟨min (min m (n + 1)) n,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ : Fin (n + 1))
      (⟨min m n, Nat.lt_succ_of_le (Nat.min_le_right _ n)⟩ : Fin (n + 1))
    have hmin : min (min m (n + 1)) n = min m n := by omega
    simp only [hmin]
    exact ObjEquivRel.refl _

/-- **Negative Resolution of `Conjecture C1` (`conjecture_c1_disproof_summary`):**
`StepState.qFull` simultaneously satisfies:
1. Hereditary gauntness (`IsHereditarilyGaunt StepState.qFull`),
2. Local finite-dimensionality (`∀ m r, IsNTruncated (min m r) (hom m r)` and
   `Fintype.card (Obj (hom m r)) = 2 ^ min m r`),
3. Global ordinal rank `ω` (`rank StepState.qFull = Ordinal.omega0`), Theorem 9A `ω`-completeness,
   and ORW Question 5.58 `α = 0` stabilization (`stepProductQ_omega_completeness`),
4. Unbounded finite truncation (`¬ ∃ n, IsNTruncated n StepState.qFull`), and
5. Failure of Postnikov completeness (`RL(Q) ≠ Q`): under `stepProductPostnikovSystem`, the
   compatible sequence `n ↦ n` (`y_n = ℓ_{n+1}(n)`) is realized by **no** `m : ℕ`. -/
theorem conjecture_c1_disproof_summary :
    IsHereditarilyGaunt StepState.qFull ∧
      (∀ m r : ℕ, IsNTruncated (min m r) (hom (s := StepState.qFull) m r) ∧
        Fintype.card (Obj (hom (s := StepState.qFull) m r)) = 2 ^ min m r) ∧
      rank StepState.qFull = Ordinal.omega0 ∧
      (∀ {t : StepState}, ReachableFrom StepState.qFull t → ∀ (u w : Obj t),
        {f : Obj (hom u w) | IsOmegaInv f} = {f : Obj (hom u w) | IsEquiv f}) ∧
      (¬ ∃ n : ℕ, IsNTruncated n StepState.qFull) ∧
      ((∀ n : ℕ, ObjEquivRel
        ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
          (stepProductPostnikovSystem.{0}.level n).unitRel (n + 1))
        ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
          (stepProductPostnikovSystem.{0}.level n).unitRel n)) ∧
        ¬ ∃ m : ℕ, ∀ n : ℕ, ObjEquivRel
          ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
            (stepProductPostnikovSystem.{0}.level n).unitRel n)
          ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
            (stepProductPostnikovSystem.{0}.level n).unitRel m)) := by
  have h12D := theorem12D_stepProductQ_phantom_not_realized stepProductPostnikovSystem.{0}
  refine ⟨isHereditarilyGaunt_qFull,
    fun m r ↦ ⟨isNTruncated_qFull_hom_min m r, homQ_card_eq m r⟩,
    rfl, stepProductQ_omega_completeness.2.2, qFull_not_nTruncated,
    ⟨fun n ↦ (h12D.1 n).1, h12D.2.2⟩⟩

/-! ## Section 5: Mandatory 4-Layer Lean 4 Definition Check Gate (`namespace Checks`) -/

namespace Checks

/-! ### Layer 1: Inhabitation (Non-Degeneracy of Formalized Carriers) -/

/-- Layer 1 witness: `Obj (AbsorbingLaliMonoid k)` is `Nontrivial` (`false ≠ true`). -/
instance instNontrivialCalA (k : ℕ) : Nontrivial (Obj (AbsorbingLaliMonoid k)) :=
  ⟨⟨false, true, Bool.false_ne_true⟩⟩

/-- Layer 1 witness: `Obj StepState.qFull` is `Nontrivial` (`0 ≠ 1`). -/
instance instNontrivialQFull : Nontrivial (Obj StepState.qFull) :=
  ⟨⟨(0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩⟩

/-- Layer 1 witness: `Obj (StepState.factor .iso)` is `Nontrivial` (`false ≠ true`). -/
instance instNontrivialFactorIso : Nontrivial (Obj (StepState.factor .iso)) :=
  ⟨⟨false, true, Bool.false_ne_true⟩⟩

/-- Layer 1 witness: `AbsorbingMonoidCarrier (k + 1)` is `Nontrivial` (`⟨false⟩ ≠ ⟨true⟩`). -/
instance instNontrivialAbsorbingMonoidCarrier (k : ℕ) :
    Nontrivial (AbsorbingMonoidCarrier (k + 1)) :=
  ⟨⟨⟨false⟩, ⟨true⟩, fun h ↦ Bool.false_ne_true (congrArg AbsorbingMonoidCarrier.val h)⟩⟩

/-- Layer 1 witness: `StepState` is `Nontrivial`. -/
instance instNontrivialStepState : Nontrivial StepState :=
  ⟨⟨StepState.factor .pt, StepState.qFull, fun h ↦ by cases h⟩⟩

/-- Explicit existential inhabitation tuple across all formalized carriers in
`StepProductPhantom`. -/
theorem layer1_step_carriers_nontrivial :
    (∀ k : ℕ, ∃ x y : Obj (AbsorbingLaliMonoid k), x ≠ y) ∧
      (∃ m r : Obj StepState.qFull, m ≠ r) ∧
      (∃ u v : Obj (StepState.factor .iso), u ≠ v) ∧
      (∀ k : ℕ, ∃ a b : AbsorbingMonoidCarrier (k + 1), a ≠ b) :=
  ⟨fun _ ↦ exists_pair_ne _, exists_pair_ne _, exists_pair_ne _, fun _ ↦ exists_pair_ne _⟩

/-! ### Layer 2: Bidirectional Separation of Core Predicates -/

/-- Layer 2 Witness A — Bidirectional separation of `Reach1`, `SameSCC1`, & `IsOneAcyclic`:
`[1]` satisfies `Reach1 false true`, `¬ Reach1 true false`, `¬ SameSCC1 false true`, and
`IsOneAcyclic`; whereas `𝒜_1 = ℳ_2` (`AbsorbingLaliMonoid 1`) satisfies `SameSCC1 false true`
while refuting `IsOneAcyclic` (`¬ ObjEquivRel false true`). -/
theorem layer2_sep_reach1_and_isOneAcyclic :
    Reach1 (s := AbsorbingLaliMonoid 0) (false : Bool) true ∧
      ¬ Reach1 (s := AbsorbingLaliMonoid 0) (true : Bool) false ∧
      ¬ SameSCC1 (s := AbsorbingLaliMonoid 0) (false : Bool) true ∧
      IsOneAcyclic (AbsorbingLaliMonoid 0) ∧
      SameSCC1 (s := AbsorbingLaliMonoid 1) (false : Bool) true ∧
      ¬ IsOneAcyclic (AbsorbingLaliMonoid 1) := by
  have h1 : Reach1 (s := AbsorbingLaliMonoid 0) (false : Bool) true := ⟨()⟩
  have h2 : ¬ Reach1 (s := AbsorbingLaliMonoid 0) (true : Bool) false := by
    rintro ⟨g⟩
    exact Empty.elim g
  have h3 : ¬ SameSCC1 (s := AbsorbingLaliMonoid 0) (false : Bool) true := fun h ↦ h2 h.2
  have h4 : IsOneAcyclic (AbsorbingLaliMonoid 0) := by
    intro x y hxy hyx
    cases x <;> cases y
    · exact ObjEquivRel.refl (s := AbsorbingLaliMonoid 0) false
    · exact False.elim (h2 hyx)
    · exact False.elim (h2 hxy)
    · exact ObjEquivRel.refl (s := AbsorbingLaliMonoid 0) true
  have h5 : SameSCC1 (s := AbsorbingLaliMonoid 1) (false : Bool) true :=
    ⟨⟨monoidFwdArrow 1⟩, ⟨monoidRevArrow 0⟩⟩
  have h6 : ¬ IsOneAcyclic (AbsorbingLaliMonoid 1) := by
    intro hacyc
    have heq := (isHereditarilyGaunt_monoid 2).isObjGaunt.objEquivRel_eq.mp
      (hacyc h5.1 h5.2)
    exact Bool.false_ne_true heq
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Layer 2 Witness B — Bidirectional separation of `ObjEquiv`, `IsObjGaunt`, and
`IsHereditarilyGaunt`: `AbsorbingLaliMonoid k` is hereditarily gaunt with `¬ ObjEquiv false true`,
whereas walking isomorphism `.factor .iso` satisfies `ObjEquiv false true` and fails both
`IsObjGaunt` and `IsHereditarilyGaunt`. -/
theorem layer2_sep_gauntness :
    (∀ k : ℕ, IsHereditarilyGaunt (AbsorbingLaliMonoid k) ∧
      ¬ ObjEquiv (s := AbsorbingLaliMonoid k) (false : Bool) true) ∧
      ObjEquiv (s := StepState.factor .iso) (false : Bool) true ∧
      ¬ IsObjGaunt (StepState.factor .iso) ∧
      ¬ IsHereditarilyGaunt (StepState.factor .iso) := by
  have hiso : ObjEquiv (s := StepState.factor .iso) (false : Bool) true :=
    ⟨(), IsEquiv.mk (s := StepState.factor .iso) () () () ()
      (IsEquiv.id (s := StepState.factor .pt) ()) (IsEquiv.id (s := StepState.factor .pt) ())⟩
  have hnot_g : ¬ IsObjGaunt (StepState.factor .iso) := fun hg ↦
    Bool.false_ne_true (hg hiso)
  have hnot_hg : ¬ IsHereditarilyGaunt (StepState.factor .iso) := fun hhg ↦
    hnot_g hhg.isObjGaunt
  exact ⟨fun k ↦ ⟨isHereditarilyGaunt_monoid (k + 1), not_objEquiv_monoid_succ k⟩,
    hiso, hnot_g, hnot_hg⟩

/-- Layer 2 Witness C — Bidirectional separation of `IsNTruncated`: `AbsorbingLaliMonoid k` has
exact dimension `k + 1` (`IsNTruncated (k + 1)` and `¬ IsNTruncated k`), while `StepProductQ` has
finite local hom dimensions `IsNTruncated (min m r)` yet fails `IsNTruncated n` for all `n`. -/
theorem layer2_sep_truncation_dimension :
    (∀ k : ℕ, IsNTruncated (k + 1) (AbsorbingLaliMonoid k) ∧
      ¬ IsNTruncated k (AbsorbingLaliMonoid k)) ∧
      (∀ m r : ℕ, IsNTruncated (min m r) (hom (s := StepState.qFull) m r)) ∧
      ¬ ∃ n : ℕ, IsNTruncated n StepState.qFull :=
  ⟨fun k ↦ ⟨isNTruncated_monoid (k + 1), not_isNTruncated_monoid_pred k⟩,
    isNTruncated_qFull_hom_min, qFull_not_nTruncated⟩

/-- Layer 2 Witness D — Bidirectional separation of truncation collapse for `AbsorbingLaliMonoid k`:
at `n ≤ k` (`1 ≤ k`), every functor to an `n`-truncated target collapses `false` and `true` to
`ObjEquiv`; at `n = k + 1` (`F = GlobularFunctor.id`), `¬ ObjEquiv false true`. -/
theorem layer2_sep_absorbingMonoid_collapse (k : ℕ) (hk : 1 ≤ k) :
    (∀ {n : ℕ}, n ≤ k → ∀ {D : Type} [GlobularInfSystem D] {d : D}, IsNTruncated n d →
      ∀ (F : GlobularFunctor StepState D) (φ : F.Rel (AbsorbingLaliMonoid k) d),
        ObjEquiv (F.mapObj φ false) (F.mapObj φ true)) ∧
      (IsNTruncated (k + 1) (AbsorbingLaliMonoid k) ∧
        ¬ ObjEquiv
          ((GlobularFunctor.id StepState).mapObj (EqStateRel.refl (AbsorbingLaliMonoid k)) false)
          ((GlobularFunctor.id StepState).mapObj (EqStateRel.refl (AbsorbingLaliMonoid k)) true)) :=
  ⟨by
    intro n hnk D _ d hd F φ
    exact (absorbingMonoid_collapse_le hk hnk hd F φ).2,
    isNTruncated_monoid (k + 1), not_objEquiv_monoid_succ k⟩

/-- Layer 2 Witness E — Bidirectional separation of Postnikov tower realization:
any constant sequence `n ↦ x₀` (and every compatible sequence on `IsOneAcyclic` `[1]`) is
realized (`∃ m, ∀ n, ObjEquivRel ...`), whereas on `StepState.qFull` the compatible sequence
`n ↦ n` under `stepProductPostnikovSystem` is NOT realized by any `m : ℕ`. -/
theorem layer2_sep_postnikov_realization :
    (∀ (P : PostnikovReflectionSystem.{0, 0, 0} (AbsorbingLaliMonoid 0))
        (x : ℕ → Obj (AbsorbingLaliMonoid 0)),
      (∀ n : ℕ, ObjEquivRel
        ((P.level n).unit.mapObj (P.level n).unitRel (x (n + 1)))
        ((P.level n).unit.mapObj (P.level n).unitRel (x n))) →
      ∃ m : Obj (AbsorbingLaliMonoid 0), ∀ n : ℕ,
        ObjEquivRel (x n) m) ∧
      ((∀ n : ℕ, ObjEquivRel
        ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
          (stepProductPostnikovSystem.{0}.level n).unitRel (n + 1))
        ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
          (stepProductPostnikovSystem.{0}.level n).unitRel n)) ∧
        ¬ ∃ m : ℕ, ∀ n : ℕ, ObjEquivRel
          ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
            (stepProductPostnikovSystem.{0}.level n).unitRel n)
          ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
            (stepProductPostnikovSystem.{0}.level n).unitRel m)) := by
  refine ⟨fun P x hx ↦ ⟨x 0, ?_⟩, ?_⟩
  · exact (theorem12C_antisymmetric_postnikov_completeness
      layer2_sep_reach1_and_isOneAcyclic.2.2.2.1 P x hx).1
  · exact ⟨fun n ↦ ((theorem12D_stepProductQ_phantom_not_realized
      stepProductPostnikovSystem.{0}).1 n).1,
      (theorem12D_stepProductQ_phantom_not_realized stepProductPostnikovSystem.{0}).2.2⟩

/-! ### Layer 3: Projection to Stock Mathlib Classes & Derived Sanity Lemmas -/

/-- Layer 3 sanity 1: stock Mathlib `Preorder`, `CommMonoid`, `SemilatticeInf`, and `OrderBot`
projections on `reach1Preorder` and `AbsorbingMonoidCarrier (k + 1)` with `⊥ * a = ⊥` and
`1 * a = a`. -/
theorem layer3_mathlib_preorder_and_monoid (k : ℕ)
    (a : AbsorbingMonoidCarrier (k + 1)) :
    let p : Preorder (Obj StepState.qFull) := reach1Preorder StepState.qFull
    p.le (0 : ℕ) (1 : ℕ) ∧
      ((⊥ : AbsorbingMonoidCarrier (k + 1)) * a = ⊥) ∧
      ((1 : AbsorbingMonoidCarrier (k + 1)) * a = a) ∧
      ((a ⊓ ⊥) = ⊥) := by
  refine ⟨⟨fun j ↦ cast (congrArg FactorState.obj
    (qHomAt_eq_pt_of_le (Nat.zero_le j)).symm) ()⟩, ?_, one_mul a, ?_⟩
  · exact AbsorbingMonoidCarrier.ext (Bool.false_and a.val)
  · exact AbsorbingMonoidCarrier.ext (Bool.and_false a.val)

/-- Layer 3 sanity 2: exact finite hom-space cardinality `Fintype.card = 2 ^ min m r` on
`StepProductQ`. -/
theorem layer3_homQ_fintype_card (m r : ℕ) :
    Fintype.card (Obj (hom (s := StepState.qFull) m r)) = 2 ^ min m r :=
  homQ_card_eq m r

/-- Layer 3 sanity 3: ordinal rank `ω`, hom-rank `min m r < ω`, and ORW Question 5.58 `α = 0`
stabilization on `StepProductQ`. -/
theorem layer3_ordinal_rank_and_orw558 (m r : ℕ) :
    rank StepState.qFull = Ordinal.omega0 ∧
      rank (hom (s := StepState.qFull) m r) = ((min m r : ℕ) : Ordinal.{0}) ∧
      rank (hom (s := StepState.qFull) m r) < Ordinal.omega0 ∧
      {f : Obj (hom (s := StepState.qFull) m r) | IsOmegaInv f} =
        {f : Obj (hom (s := StepState.qFull) m r) | IsEquiv f} :=
  ⟨rfl, (stepProductQ_rank_hom m r).1,
    lt_of_le_of_lt (stepProductQ_rank_hom m r).2.1 (stepProductQ_rank_hom m r).2.2,
    stepProductQ_omega_completeness.2.1 m r⟩

/-- Layer 3 sanity 4: full `Conjecture C1` negative resolution assembly. -/
theorem layer3_conjecture_c1_disproof :
    IsHereditarilyGaunt StepState.qFull ∧
      rank StepState.qFull = Ordinal.omega0 ∧
      ¬ ∃ n : ℕ, IsNTruncated n StepState.qFull :=
  ⟨conjecture_c1_disproof_summary.1,
    conjecture_c1_disproof_summary.2.2.1,
    conjecture_c1_disproof_summary.2.2.2.2.1⟩

/-! ### Layer 4: Kernel Axiom Gate (`#guard_msgs in #print axioms`) -/

section KernelAxiomGate

set_option linter.hashCommand false
set_option linter.style.longLine false

/-- info: 'HomotopyCRM.objEquivRel_equivalence' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.objEquivRel_equivalence

/-- info: 'HomotopyCRM.IsNTruncated.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.IsNTruncated.mono

/-- info: 'HomotopyCRM.GlobularFunctor.map_isEquiv' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.GlobularFunctor.map_isEquiv

/-- info: 'HomotopyCRM.theorem12B_classifier_scc_trapping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theorem12B_classifier_scc_trapping

/-- info: 'HomotopyCRM.theorem12B_tower_trapped_in_single_scc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theorem12B_tower_trapped_in_single_scc

/-- info: 'HomotopyCRM.theorem12C_antisymmetric_postnikov_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theorem12C_antisymmetric_postnikov_completeness

/-- info: 'HomotopyCRM.mulFunctor_monoid_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.mulFunctor_monoid_laws

/-- info: 'HomotopyCRM.isHereditarilyGaunt_monoid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.isHereditarilyGaunt_monoid

/-- info: 'HomotopyCRM.absorbingMonoid_collapse_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.absorbingMonoid_collapse_le

/-- info: 'HomotopyCRM.stepProductQ_omega_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.stepProductQ_omega_completeness

/-- info: 'HomotopyCRM.isHereditarilyGaunt_qFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.isHereditarilyGaunt_qFull

/-- info: 'HomotopyCRM.homQ_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.homQ_card_eq

/-- info: 'HomotopyCRM.qFull_not_nTruncated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.qFull_not_nTruncated

/-- info: 'HomotopyCRM.theorem12D_stepProductQ_phantom_not_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theorem12D_stepProductQ_phantom_not_realized

/-- info: 'HomotopyCRM.conjecture_c1_disproof_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.conjecture_c1_disproof_summary

/-- info: 'HomotopyCRM.Checks.layer1_step_carriers_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer1_step_carriers_nontrivial

/-- info: 'HomotopyCRM.Checks.layer2_sep_reach1_and_isOneAcyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_reach1_and_isOneAcyclic

/-- info: 'HomotopyCRM.Checks.layer2_sep_gauntness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_gauntness

/-- info: 'HomotopyCRM.Checks.layer2_sep_truncation_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_truncation_dimension

/-- info: 'HomotopyCRM.Checks.layer2_sep_absorbingMonoid_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_absorbingMonoid_collapse

/-- info: 'HomotopyCRM.Checks.layer2_sep_postnikov_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_postnikov_realization

/-- info: 'HomotopyCRM.Checks.layer3_mathlib_preorder_and_monoid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer3_mathlib_preorder_and_monoid

end KernelAxiomGate

end Checks

end HomotopyCRM
