/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HomotopyCRM Formalization Team
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Logic.Relation
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.UpperLower.Basic

/-!
# Directed Fraïssé Strong Amalgamation and the Steiner Cycle Obstruction

This module formalizes `MSG_007` (`TODO-07`) of the `HomotopyCRM` library, calibrating the
site-level Strong Amalgamation Property (`SAP`) and directed acyclicity conditions needed to build
multiplicity-preserving Fraïssé classes of finite directed cellular shapes (Steiner / loop-free
oriented graded posets, whose nerves lie in the Postnikov-complete tier `Cat^L_(∞,∞)` of the
strict reflective localization hierarchy
`Cat^L_(∞,∞) ⊊ Cat^ω_(∞,∞) ⊊ Cat^coind_(∞,∞) ⊊ Cat^R_(∞,∞) := lim_κ Cat_(∞,n)` established by
Ozornova–Rovelli–Walde `arXiv:2603.11005v2`, `arXiv:2608.28355`, `arXiv:2610.38698` and
Gepner–Heine `arXiv:2603.09903`, Thm. 3.7.26).

## Main Results

1. **Oriented Graded Posets & Closed Cellular Embeddings (`OrientedGradedPoset`):**
   - `OrientedGradedPoset P` extends stock `PartialOrder P` with a strictly monotone dimension
     grading `dim : P → ℕ` (`x < y → dim x < dim y`) and a non-dependent coface orientation
     `sign : P → P → Bool` active on codimension-1 facets
     `IsFacet x y := x ≤ y ∧ dim y = dim x + 1`.
   - `IsClosedEmbedding f` packages monotone, injective, downward-closed, grade-preserving, and
     facet-sign-preserving embeddings, inducing canonical principal-closure order isomorphisms
     `cl (f x) ≃o cl x` (`IsClosedEmbedding.clOrderIso`).

2. **Quotient-Free Set Pushouts (`SetPushoutSquare` & `CanonicalPushout`):**
   - `SetPushoutSquare i₁ i₂ j₁ j₂` axiomatizes injective strong-amalgamation pushouts of types
     with quotient-free universal `desc`.
   - `CanonicalPushout i₁ i₂ := B₁ ⊕ {b₂ : B₂ // b₂ ∉ Set.range i₂}` instantiates
     `SetPushoutSquare` without quotients (`CanonicalPushout.setPushoutSquare`).

3. **Strong Amalgamation of Closed Oriented Graded Posets (`sap_closed_oriented_poset`):**
   - Because `i₁` and `i₂` have downward-closed images, the direct union of leg orders on a
     `SetPushoutSquare` is **already transitive and antisymmetric** without taking transitive
     closures, endowing `Q` with a canonical `OrientedGradedPoset` structure under which `j₁, j₂`
     are closed embeddings with `cl (j₁ b₁) ≃o cl b₁` and `cl (j₂ b₂) ≃o cl b₂`.

4. **Directed Steiner Flow & Cycle Obstruction (`steiner_cycle_obstruction`):**
   - `FlowStep x y` holds when some cell `w` has `x` as an input (`sign x w = false`) facet and
     `y` as an output (`sign y w = true`) facet; `FlowReach` is `Relation.TransGen FlowStep`, and
     `IsFlowAcyclic P` forbids directed cycles `FlowReach x x`.
   - Amalgamating the span of bare closed embeddings `{0, 1} ↪ (0 → 1)` and `{0, 1} ↪ (1 → 0)`
     between finite `IsFlowAcyclic` posets creates a directed 2-cycle `0 ⇄ 1` in the pushout,
     proving that bare `IsClosedEmbedding`s do **not** preserve `IsFlowAcyclic` under pushouts.

5. **Directed Fraïssé Candidate Classes (`IsFlowReachReflecting` & `IsFlowConvex`):**
   - Both `IsFlowReachReflecting` and the strictly stronger `IsFlowConvex` class (related by
     derived theorems `IsFlowConvex.toIsFlowReachReflecting` and
     `IsFlowReachReflecting.toIsClosedEmbedding`) are closed under composition, stable under
     pushout cobase-change, and **preserve `IsFlowAcyclic`** on amalgamated pushouts
     (`sap_flowReachReflecting` and `sap_flowConvex`).

6. **Mandatory 4-Layer Definition Check Gate (`namespace Checks`):**
   - Verifies Inhabitation (Layer 1), strict Bidirectional Separation across all predicates
     including `IsClosedEmbedding` vs. `IsFlowReachReflecting` vs. `IsFlowConvex` (Layer 2),
     Mathlib projections & derived lemmas (Layer 3), and `#guard_msgs in #print axioms` (Layer 4).
-/

universe u v

namespace HomotopyCRM

/-! ## Section 1: Oriented Graded Posets, Facets, Principal Closures, and Closed Embeddings -/

/-- An **oriented graded poset** equips a partially ordered type `P` with a strictly monotone
natural-number dimension `dim : P → ℕ` and a non-dependent coface orientation `sign : P → P → Bool`
interpreted on codimension-1 facets (`false` = input/source `-`, `true` = output/target `+`). -/
class OrientedGradedPoset (P : Type u) extends PartialOrder P where
  /-- Natural-number dimension of each cell. -/
  dim : P → ℕ
  /-- Dimension is strictly monotone along strict face inclusions `x < y`. -/
  dim_strictMono : StrictMono dim
  /-- Non-dependent coface sign `sign x y : Bool` (evaluated on codimension-1 facets). -/
  sign : P → P → Bool

namespace OrientedGradedPoset

/-- Monotonicity of `dim` (`x ≤ y → dim x ≤ dim y`) derived from `dim_strictMono`. -/
theorem dim_mono {P : Type*} [OrientedGradedPoset P] :
    Monotone (dim (P := P)) :=
  dim_strictMono.monotone

/-- Two comparable cells `x ≤ y` of equal dimension must coincide. -/
theorem eq_of_le_of_dim_eq {P : Type*} [OrientedGradedPoset P] {x y : P}
    (hle : x ≤ y) (hdim : dim x = dim y) : x = y := by
  by_contra hne
  have hlt : dim x < dim y := dim_strictMono (lt_of_le_of_ne hle hne)
  omega

end OrientedGradedPoset

/-- Codimension-1 facet incidence `x ◁ y` in an `OrientedGradedPoset`: `x ≤ y` and
`dim y = dim x + 1`. -/
def IsFacet {P : Type*} [OrientedGradedPoset P] (x y : P) : Prop :=
  x ≤ y ∧ OrientedGradedPoset.dim y = OrientedGradedPoset.dim x + 1

namespace IsFacet

/-- Underlying face inequality `x ≤ y` of a facet `IsFacet x y`. -/
theorem le {P : Type*} [OrientedGradedPoset P] {x y : P} (h : IsFacet x y) : x ≤ y :=
  h.1

/-- Codimension-1 equation `dim y = dim x + 1` of a facet `IsFacet x y`. -/
theorem dim_eq {P : Type*} [OrientedGradedPoset P] {x y : P} (h : IsFacet x y) :
    OrientedGradedPoset.dim y = OrientedGradedPoset.dim x + 1 :=
  h.2

/-- A codimension-1 facet `x` of `y` is strictly distinct from `y`. -/
theorem ne {P : Type*} [OrientedGradedPoset P] {x y : P} (h : IsFacet x y) : x ≠ y := by
  intro hxy
  subst hxy
  have hd := h.2
  omega

/-- Strict face inequality `x < y` of a codimension-1 facet. -/
theorem lt {P : Type*} [OrientedGradedPoset P] {x y : P} (h : IsFacet x y) : x < y :=
  lt_of_le_of_ne h.1 h.ne

/-- Asymmetry of codimension-1 facet incidence. -/
theorem asymm {P : Type*} [OrientedGradedPoset P] {x y : P} (h : IsFacet x y) :
    ¬ IsFacet y x := by
  intro hyx
  have h1 := h.2
  have h2 := hyx.2
  omega

end IsFacet

/-- Principal downward closure `cl x := {y | y ≤ x}` (`Set.Iic x`) in a partial order. -/
abbrev cl {P : Type*} [PartialOrder P] (x : P) : Set P :=
  Set.Iic x

namespace OrientedGradedPoset

/-- Bundled grade- and facet-orientation-preserving order morphism between
`OrientedGradedPoset`s. -/
@[ext]
structure Hom (P : Type*) (Q : Type*) [OrientedGradedPoset P] [OrientedGradedPoset Q] where
  /-- Underlying function on cells. -/
  toFun : P → Q
  /-- Order preservation (`x ≤ y → toFun x ≤ toFun y`). -/
  monotone' : Monotone toFun
  /-- Exact dimension preservation. -/
  map_dim' : ∀ x : P, dim (toFun x) = dim x
  /-- Preservation of coface orientation signs on codimension-1 facets. -/
  map_sign' : ∀ ⦃x y : P⦄, IsFacet x y → sign (toFun x) (toFun y) = sign x y

instance (P Q : Type*) [OrientedGradedPoset P] [OrientedGradedPoset Q] :
    FunLike (Hom P Q) P Q where
  coe := Hom.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr

namespace Hom

/-- Projection from `OrientedGradedPoset.Hom P Q` to stock `OrderHom` (`P →o Q`). -/
def toOrderHom {P Q : Type*} [OrientedGradedPoset P] [OrientedGradedPoset Q]
    (f : Hom P Q) : P →o Q where
  toFun := f
  monotone' := f.monotone'

/-- Identity morphism of `OrientedGradedPoset`s. -/
def id (P : Type*) [OrientedGradedPoset P] : Hom P P where
  toFun x := x
  monotone' _ _ h := h
  map_dim' _ := rfl
  map_sign' _ _ _ := rfl

/-- Composition of morphisms of `OrientedGradedPoset`s. -/
def comp {P Q R : Type*} [OrientedGradedPoset P] [OrientedGradedPoset Q]
    [OrientedGradedPoset R] (g : Hom Q R) (f : Hom P Q) : Hom P R where
  toFun x := g (f x)
  monotone' := g.monotone'.comp f.monotone'
  map_dim' x := (g.map_dim' (f x)).trans (f.map_dim' x)
  map_sign' x y hxy := by
    have hfx : IsFacet (f x) (f y) :=
      ⟨f.monotone' hxy.1,
        (f.map_dim' y).trans (hxy.2.trans (congrArg (· + 1) (f.map_dim' x).symm))⟩
    exact (g.map_sign' hfx).trans (f.map_sign' hxy)

end Hom

end OrientedGradedPoset

/-- Predicate asserting that `f : P → Q` is a **closed cellular embedding** of
`OrientedGradedPoset`s: monotone, injective, downward-closed on principal closures, dimension-
preserving, and facet-orientation-preserving. -/
structure IsClosedEmbedding {P Q : Type*} [OrientedGradedPoset P] [OrientedGradedPoset Q]
    (f : P → Q) : Prop where
  /-- Order preservation (`x ≤ y → f x ≤ f y`). -/
  mono : Monotone f
  /-- Injectivity on underlying cells. -/
  injective : Function.Injective f
  /-- Principal-closure surjectivity / downward-closedness: every `q ≤ f x` lifts to some `a ≤ x`
  with `f a = q`. -/
  downward_closed : ∀ ⦃x : P⦄ ⦃q : Q⦄, q ≤ f x → ∃ a : P, a ≤ x ∧ f a = q
  /-- Exact preservation of dimension. -/
  map_dim : ∀ x : P, OrientedGradedPoset.dim (f x) = OrientedGradedPoset.dim x
  /-- Preservation of coface orientation sign on codimension-1 facets. -/
  map_sign : ∀ ⦃x y : P⦄, IsFacet x y →
    OrientedGradedPoset.sign (f x) (f y) = OrientedGradedPoset.sign x y

/-- Bundled closed cellular embedding between `OrientedGradedPoset`s. -/
structure OrientedGradedPoset.Embedding (P : Type*) (Q : Type*)
    [OrientedGradedPoset P] [OrientedGradedPoset Q] where
  /-- Underlying cell map. -/
  toFun : P → Q
  /-- Witness that `toFun` is a closed cellular embedding. -/
  isClosed : IsClosedEmbedding toFun

namespace IsClosedEmbedding

variable {P Q R : Type*} [OrientedGradedPoset P] [OrientedGradedPoset Q] [OrientedGradedPoset R]
variable {f : P → Q} {g : Q → R}

/-- Bundled `OrientedGradedPoset.Hom` underlying a closed embedding. -/
def toHom (hf : IsClosedEmbedding f) : OrientedGradedPoset.Hom P Q where
  toFun := f
  monotone' := hf.mono
  map_dim' := hf.map_dim
  map_sign' := hf.map_sign

/-- Derived order-reflection law: downward-closedness plus injectivity forces `f x ≤ f y ↔ x ≤ y`.
-/
theorem map_le_iff (hf : IsClosedEmbedding f) {x y : P} :
    f x ≤ f y ↔ x ≤ y := by
  constructor
  · intro hle
    rcases hf.downward_closed hle with ⟨a, hay, hfa⟩
    rwa [hf.injective hfa] at hay
  · exact fun hle ↦ hf.mono hle

/-- Strict-order reflection `f x < f y ↔ x < y` for a closed embedding. -/
theorem map_lt_iff (hf : IsClosedEmbedding f) {x y : P} :
    f x < f y ↔ x < y := by
  simp only [lt_iff_le_not_ge, hf.map_le_iff]

/-- Projection from `IsClosedEmbedding f` to stock `OrderEmbedding` (`P ↪o Q`). -/
def toOrderEmbedding (hf : IsClosedEmbedding f) : P ↪o Q :=
  OrderEmbedding.ofMapLEIff f (fun _ _ ↦ hf.map_le_iff)

/-- The image `Set.range f` of a closed embedding is a lower set (`IsLowerSet`) in `Q`. -/
theorem isLowerSet_range (hf : IsClosedEmbedding f) :
    IsLowerSet (Set.range f) := by
  rintro q q' hle ⟨x, rfl⟩
  rcases hf.downward_closed hle with ⟨a, _, rfl⟩
  exact ⟨a, rfl⟩

/-- Exact reflection and preservation of codimension-1 facets along a closed embedding. -/
theorem map_isFacet_iff (hf : IsClosedEmbedding f) {x y : P} :
    IsFacet (f x) (f y) ↔ IsFacet x y := by
  simp only [IsFacet, hf.map_le_iff, hf.map_dim]

/-- Image identity `f '' cl x = cl (f x)` on principal closures. -/
theorem image_cl_eq (hf : IsClosedEmbedding f) (x : P) :
    f '' cl x = cl (f x) :=
  hf.toOrderEmbedding.image_Iic hf.isLowerSet_range x

/-- **Principal-Closure Order Isomorphism:** every closed embedding `f : P → Q` restricts to an
order isomorphism `cl (f x) ≃o cl x` for each `x : P`. -/
noncomputable def clOrderIso (hf : IsClosedEmbedding f) (x : P) :
    cl (f x) ≃o cl x :=
  (OrderIso.symm
    { toFun := fun a ↦ ⟨f a.1, hf.mono a.2⟩
      invFun := fun b ↦
        ⟨Classical.choose (hf.downward_closed b.2),
          (Classical.choose_spec (hf.downward_closed b.2)).1⟩
      left_inv := fun a ↦ by
        apply Subtype.ext
        exact hf.injective (Classical.choose_spec (hf.downward_closed (hf.mono a.2))).2
      right_inv := fun b ↦ by
        apply Subtype.ext
        exact (Classical.choose_spec (hf.downward_closed b.2)).2
      map_rel_iff' := fun {a₁ a₂} ↦ hf.map_le_iff })

@[simp]
lemma clOrderIso_symm_apply_coe (hf : IsClosedEmbedding f) (x : P) (a : cl x) :
    ((hf.clOrderIso x).symm a : Q) = f a.1 := rfl

@[simp]
lemma map_clOrderIso_coe (hf : IsClosedEmbedding f) (x : P) (b : cl (f x)) :
    f (hf.clOrderIso x b : P) = b.1 :=
  (Classical.choose_spec (hf.downward_closed b.2)).2

/-- Identity map is a closed cellular embedding. -/
theorem id (P : Type*) [OrientedGradedPoset P] :
    IsClosedEmbedding ( _root_.id : P → P) where
  mono _ _ h := h
  injective := Function.injective_id
  downward_closed _ q hq := ⟨q, hq, rfl⟩
  map_dim _ := rfl
  map_sign _ _ _ := rfl

/-- Closed cellular embeddings are closed under composition. -/
theorem comp (hg : IsClosedEmbedding g) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (g ∘ f) where
  mono := hg.mono.comp hf.mono
  injective := hg.injective.comp hf.injective
  downward_closed x r hr := by
    rcases hg.downward_closed hr with ⟨q, hq, rfl⟩
    rcases hf.downward_closed hq with ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  map_dim x := (hg.map_dim (f x)).trans (hf.map_dim x)
  map_sign _ _ hxy := (hg.map_sign (hf.map_isFacet_iff.mpr hxy)).trans (hf.map_sign hxy)

end IsClosedEmbedding

/-! ## Section 2: Quotient-Free `SetPushoutSquare` & `CanonicalPushout` -/

/-- An injective **Strong Amalgamation pushout square of sets/types**: `j₁ ∘ i₁ = j₂ ∘ i₂`, all
four legs are injective, `j₁` and `j₂` are jointly surjective onto `Q`, and the square is also a
pullback (`j₁ b₁ = j₂ b₂ → ∃ a, i₁ a = b₁ ∧ i₂ a = b₂`). -/
structure SetPushoutSquare {A B₁ B₂ Q : Type*}
    (i₁ : A → B₁) (i₂ : A → B₂) (j₁ : B₁ → Q) (j₂ : B₂ → Q) : Prop where
  /-- Injectivity of `i₁`. -/
  inj_i₁ : Function.Injective i₁
  /-- Injectivity of `i₂`. -/
  inj_i₂ : Function.Injective i₂
  /-- Injectivity of `j₁`. -/
  inj_j₁ : Function.Injective j₁
  /-- Injectivity of `j₂`. -/
  inj_j₂ : Function.Injective j₂
  /-- Commutativity `j₁ (i₁ a) = j₂ (i₂ a)`. -/
  comm : ∀ a : A, j₁ (i₁ a) = j₂ (i₂ a)
  /-- Joint surjectivity of `(j₁, j₂)` onto `Q`. -/
  jointly_surj : ∀ q : Q, (∃ b₁ : B₁, j₁ b₁ = q) ∨ (∃ b₂ : B₂, j₂ b₂ = q)
  /-- Exact pullback / Strong Amalgamation (`SAP`) condition. -/
  pullback_sap : ∀ ⦃b₁ : B₁⦄ ⦃b₂ : B₂⦄, j₁ b₁ = j₂ b₂ → ∃ a : A, i₁ a = b₁ ∧ i₂ a = b₂

namespace SetPushoutSquare

variable {A B₁ B₂ Q : Type*} {i₁ : A → B₁} {i₂ : A → B₂} {j₁ : B₁ → Q} {j₂ : B₂ → Q}

/-- Symmetry of a `SetPushoutSquare` swapping `(B₁, i₁, j₁)` and `(B₂, i₂, j₂)`. -/
theorem symm (sq : SetPushoutSquare i₁ i₂ j₁ j₂) :
    SetPushoutSquare i₂ i₁ j₂ j₁ where
  inj_i₁ := sq.inj_i₂
  inj_i₂ := sq.inj_i₁
  inj_j₁ := sq.inj_j₂
  inj_j₂ := sq.inj_j₁
  comm a := (sq.comm a).symm
  jointly_surj q := (sq.jointly_surj q).symm
  pullback_sap {_ _} h := by
    rcases sq.pullback_sap h.symm with ⟨a, ha₁, ha₂⟩
    exact ⟨a, ha₂, ha₁⟩

/-- Bidirectional Strong Amalgamation characterization `j₁ b₁ = j₂ b₂ ↔ ∃ a, i₁ a = b₁ ∧ i₂ a = b₂`.
-/
theorem eq_iff (sq : SetPushoutSquare i₁ i₂ j₁ j₂) {b₁ : B₁} {b₂ : B₂} :
    j₁ b₁ = j₂ b₂ ↔ ∃ a : A, i₁ a = b₁ ∧ i₂ a = b₂ := by
  constructor
  · exact fun h ↦ sq.pullback_sap h
  · rintro ⟨a, rfl, rfl⟩
    exact sq.comm a

/-- Set-level Strong Amalgamation intersection identity
`Set.range j₁ ∩ Set.range j₂ = Set.range (j₁ ∘ i₁)`. -/
theorem range_inter_eq (sq : SetPushoutSquare i₁ i₂ j₁ j₂) :
    Set.range j₁ ∩ Set.range j₂ = Set.range (j₁ ∘ i₁) := by
  ext q
  constructor
  · rintro ⟨⟨b₁, rfl⟩, ⟨b₂, hb₂⟩⟩
    rcases sq.pullback_sap hb₂.symm with ⟨a, rfl, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨i₁ a, rfl⟩, ⟨i₂ a, (sq.comm a).symm⟩⟩

private theorem exists_right_of_not_left (sq : SetPushoutSquare i₁ i₂ j₁ j₂) {q : Q}
    (hnot : ¬ ∃ b₁ : B₁, j₁ b₁ = q) : ∃ b₂ : B₂, j₂ b₂ = q := by
  rcases sq.jointly_surj q with h₁ | h₂
  · exact False.elim (hnot h₁)
  · exact h₂

/-- Quotient-free universal pushout Eliminator `desc : Q → X` induced by compatible maps
`f₁ : B₁ → X` and `f₂ : B₂ → X` with `∀ a, f₁ (i₁ a) = f₂ (i₂ a)`. -/
noncomputable def desc (sq : SetPushoutSquare i₁ i₂ j₁ j₂) {X : Type*}
    (f₁ : B₁ → X) (f₂ : B₂ → X) (_hcomm : ∀ a : A, f₁ (i₁ a) = f₂ (i₂ a)) (q : Q) : X := by
  classical
  exact if h₁ : ∃ b₁ : B₁, j₁ b₁ = q then
    f₁ (Classical.choose h₁)
  else
    f₂ (Classical.choose (sq.exists_right_of_not_left h₁))

@[simp]
theorem desc_j₁ (sq : SetPushoutSquare i₁ i₂ j₁ j₂) {X : Type*}
    (f₁ : B₁ → X) (f₂ : B₂ → X) (hcomm : ∀ a : A, f₁ (i₁ a) = f₂ (i₂ a)) (b₁ : B₁) :
    sq.desc f₁ f₂ hcomm (j₁ b₁) = f₁ b₁ := by
  classical
  have hex : ∃ b₁' : B₁, j₁ b₁' = j₁ b₁ := ⟨b₁, rfl⟩
  simp only [desc, dif_pos hex]
  congr 1
  exact sq.inj_j₁ (Classical.choose_spec hex)

@[simp]
theorem desc_j₂ (sq : SetPushoutSquare i₁ i₂ j₁ j₂) {X : Type*}
    (f₁ : B₁ → X) (f₂ : B₂ → X) (hcomm : ∀ a : A, f₁ (i₁ a) = f₂ (i₂ a)) (b₂ : B₂) :
    sq.desc f₁ f₂ hcomm (j₂ b₂) = f₂ b₂ := by
  classical
  by_cases hex : ∃ b₁ : B₁, j₁ b₁ = j₂ b₂
  · simp only [desc, dif_pos hex]
    rcases sq.pullback_sap (Classical.choose_spec hex) with ⟨a, ha₁, ha₂⟩
    rw [← ha₁, ← ha₂, hcomm a]
  · simp only [desc, dif_neg hex]
    congr 1
    exact sq.inj_j₂ (Classical.choose_spec (sq.exists_right_of_not_left hex))

/-- Uniqueness of the universal map out of `Q`. -/
theorem desc_unique (sq : SetPushoutSquare i₁ i₂ j₁ j₂) {X : Type*}
    (f₁ : B₁ → X) (f₂ : B₂ → X) (hcomm : ∀ a : A, f₁ (i₁ a) = f₂ (i₂ a))
    (g : Q → X) (hg₁ : ∀ b₁ : B₁, g (j₁ b₁) = f₁ b₁) (hg₂ : ∀ b₂ : B₂, g (j₂ b₂) = f₂ b₂) :
    g = sq.desc f₁ f₂ hcomm := by
  funext q
  rcases sq.jointly_surj q with ⟨b₁, rfl⟩ | ⟨b₂, rfl⟩
  · rw [hg₁, sq.desc_j₁]
  · rw [hg₂, sq.desc_j₂]

end SetPushoutSquare

/-- Explicit **quotient-free canonical pushout carrier** `B₁ ⊕ {b₂ : B₂ // b₂ ∉ Set.range i₂}`
amalgamating `B₁` and the complement of `Set.range i₂` in `B₂`. -/
def CanonicalPushout {A B₁ B₂ : Type*} (_i₁ : A → B₁) (i₂ : A → B₂) : Type _ :=
  B₁ ⊕ {b₂ : B₂ // b₂ ∉ Set.range i₂}

namespace CanonicalPushout

/-- Left canonical injection `B₁ → CanonicalPushout i₁ i₂`. -/
def inl {A B₁ B₂ : Type*} (i₁ : A → B₁) (i₂ : A → B₂) (b₁ : B₁) :
    CanonicalPushout i₁ i₂ :=
  Sum.inl b₁

/-- Right canonical injection `B₂ → CanonicalPushout i₁ i₂`, sending `i₂ a` to `Sum.inl (i₁ a)`
and `b₂ ∉ Set.range i₂` to `Sum.inr ⟨b₂, _⟩`. -/
noncomputable def inr {A B₁ B₂ : Type*} (i₁ : A → B₁) (i₂ : A → B₂) (b₂ : B₂) :
    CanonicalPushout i₁ i₂ := by
  classical
  exact if h : b₂ ∈ Set.range i₂ then
    Sum.inl (i₁ (Classical.choose h))
  else
    Sum.inr ⟨b₂, h⟩

/-- `CanonicalPushout i₁ i₂` equipped with `inl` and `inr` instantiates `SetPushoutSquare`
whenever `i₁` and `i₂` are injective. -/
theorem setPushoutSquare {A B₁ B₂ : Type*} {i₁ : A → B₁} {i₂ : A → B₂}
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) :
    SetPushoutSquare i₁ i₂ (inl i₁ i₂) (inr i₁ i₂) where
  inj_i₁ := hi₁
  inj_i₂ := hi₂
  inj_j₁ := Sum.inl_injective
  inj_j₂ x y hxy := by
    classical
    by_cases hx : x ∈ Set.range i₂
    · by_cases hy : y ∈ Set.range i₂
      · simp only [inr, dif_pos hx, dif_pos hy] at hxy
        injection hxy with h
        rw [← Classical.choose_spec hx, ← Classical.choose_spec hy, hi₁ h]
      · simp only [inr, dif_pos hx, dif_neg hy] at hxy
        change (_ : B₁ ⊕ _) = _ at hxy
        cases hxy
    · by_cases hy : y ∈ Set.range i₂
      · simp only [inr, dif_neg hx, dif_pos hy] at hxy
        change (_ : B₁ ⊕ _) = _ at hxy
        cases hxy
      · simp only [inr, dif_neg hx, dif_neg hy] at hxy
        injection hxy with h
        exact congrArg Subtype.val h
  comm a := by
    classical
    have ha : i₂ a ∈ Set.range i₂ := ⟨a, rfl⟩
    simp only [inl, inr, dif_pos ha]
    congr 2
    exact (hi₂ (Classical.choose_spec ha)).symm
  jointly_surj q := by
    rcases q with b₁ | ⟨b₂, hb₂⟩
    · exact Or.inl ⟨b₁, rfl⟩
    · refine Or.inr ⟨b₂, ?_⟩
      simp [inr, hb₂]
  pullback_sap {b₁ b₂} heq := by
    classical
    by_cases hb₂ : b₂ ∈ Set.range i₂
    · simp only [inl, inr, dif_pos hb₂] at heq
      injection heq with h
      exact ⟨Classical.choose hb₂, h.symm, Classical.choose_spec hb₂⟩
    · simp only [inl, inr, dif_neg hb₂] at heq
      change (_ : B₁ ⊕ _) = _ at heq
      cases heq

end CanonicalPushout

/-! ## Section 3: Strong Amalgamation (`SAP`) of Closed `OrientedGradedPoset`s -/

private lemma choose_eq_of_inj {X Y : Type*} {f : X → Y} (hf : Function.Injective f)
    {x : X} {P : X → Prop} (h : ∃ x' : X, f x' = f x ∧ P x') :
    Classical.choose h = x :=
  hf (Classical.choose_spec h).1

private lemma choose_eq_of_inj' {X Y : Type*} {f : X → Y} (hf : Function.Injective f)
    {x : X} (h : ∃ x' : X, f x' = f x) :
    Classical.choose h = x :=
  hf (Classical.choose_spec h)

section PushoutPoset

variable {A B₁ B₂ Q : Type*}
variable [OrientedGradedPoset B₁] [OrientedGradedPoset B₂]
variable {i₁ : A → B₁} {i₂ : A → B₂} {j₁ : B₁ → Q} {j₂ : B₂ → Q}

/-- Direct union partial order relation on a `SetPushoutSquare`: `q ≤ q'` iff `(q, q')` is the
image of an ordered pair in `B₁` or of an ordered pair in `B₂` (no transitive closure needed!). -/
def PushoutLE (_sq : SetPushoutSquare i₁ i₂ j₁ j₂) (q q' : Q) : Prop :=
  (∃ b₁ b₁' : B₁, j₁ b₁ = q ∧ j₁ b₁' = q' ∧ b₁ ≤ b₁') ∨
    (∃ b₂ b₂' : B₂, j₂ b₂ = q ∧ j₂ b₂' = q' ∧ b₂ ≤ b₂')

/-- Reflexivity of `PushoutLE`. -/
theorem pushoutLE_refl (sq : SetPushoutSquare i₁ i₂ j₁ j₂) (q : Q) :
    PushoutLE sq q q := by
  rcases sq.jointly_surj q with ⟨b₁, rfl⟩ | ⟨b₂, rfl⟩
  · exact Or.inl ⟨b₁, b₁, rfl, rfl, le_rfl⟩
  · exact Or.inr ⟨b₂, b₂, rfl, rfl, le_rfl⟩

variable [OrientedGradedPoset A]

/-- Key downward-closedness lemma on the left leg: `PushoutLE sq q (j₁ y₁)` holds iff `q = j₁ x₁`
for some `x₁ ≤ y₁` in `B₁`. -/
theorem pushoutLE_j₁_right_iff (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) (q : Q) (y₁ : B₁) :
    PushoutLE sq q (j₁ y₁) ↔ ∃ x₁ : B₁, j₁ x₁ = q ∧ x₁ ≤ y₁ := by
  constructor
  · rintro (⟨b₁, b₁', rfl, hb₁', hle⟩ | ⟨b₂, b₂', rfl, hb₂', hle⟩)
    · rw [sq.inj_j₁ hb₁'] at hle
      exact ⟨b₁, rfl, hle⟩
    · rcases sq.pullback_sap hb₂'.symm with ⟨a', rfl, rfl⟩
      rcases hi₂.downward_closed hle with ⟨a, ha, rfl⟩
      exact ⟨i₁ a, sq.comm a, hi₁.mono ha⟩
  · rintro ⟨x₁, rfl, hle⟩
    exact Or.inl ⟨x₁, y₁, rfl, rfl, hle⟩

/-- Key downward-closedness lemma on the right leg: `PushoutLE sq q (j₂ y₂)` holds iff `q = j₂ x₂`
for some `x₂ ≤ y₂` in `B₂`. -/
theorem pushoutLE_j₂_right_iff (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) (q : Q) (y₂ : B₂) :
    PushoutLE sq q (j₂ y₂) ↔ ∃ x₂ : B₂, j₂ x₂ = q ∧ x₂ ≤ y₂ := by
  constructor
  · rintro (⟨b₁, b₁', rfl, hb₁', hle⟩ | ⟨b₂, b₂', rfl, hb₂', hle⟩)
    · rcases sq.pullback_sap hb₁' with ⟨a', rfl, rfl⟩
      rcases hi₁.downward_closed hle with ⟨a, ha, rfl⟩
      exact ⟨i₂ a, (sq.comm a).symm, hi₂.mono ha⟩
    · rw [sq.inj_j₂ hb₂'] at hle
      exact ⟨b₂, rfl, hle⟩
  · rintro ⟨x₂, rfl, hle⟩
    exact Or.inr ⟨x₂, y₂, rfl, rfl, hle⟩

/-- Order-reflection of `j₁` for `PushoutLE`. -/
theorem pushoutLE_j₁_iff (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) (x₁ y₁ : B₁) :
    PushoutLE sq (j₁ x₁) (j₁ y₁) ↔ x₁ ≤ y₁ := by
  rw [pushoutLE_j₁_right_iff sq hi₁ hi₂]
  constructor
  · rintro ⟨x₁', hx₁', hle⟩
    rwa [sq.inj_j₁ hx₁'] at hle
  · exact fun hle ↦ ⟨x₁, rfl, hle⟩

/-- Order-reflection of `j₂` for `PushoutLE`. -/
theorem pushoutLE_j₂_iff (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) (x₂ y₂ : B₂) :
    PushoutLE sq (j₂ x₂) (j₂ y₂) ↔ x₂ ≤ y₂ := by
  rw [pushoutLE_j₂_right_iff sq hi₁ hi₂]
  constructor
  · rintro ⟨x₂', hx₂', hle⟩
    rwa [sq.inj_j₂ hx₂'] at hle
  · exact fun hle ↦ ⟨x₂, rfl, hle⟩

/-- Direct transitivity of `PushoutLE` without transitive closure! -/
theorem pushoutLE_trans (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂)
    {q₁ q₂ q₃ : Q} (h₁₂ : PushoutLE sq q₁ q₂) (h₂₃ : PushoutLE sq q₂ q₃) :
    PushoutLE sq q₁ q₃ := by
  rcases sq.jointly_surj q₃ with ⟨z₁, rfl⟩ | ⟨z₂, rfl⟩
  · rcases (pushoutLE_j₁_right_iff sq hi₁ hi₂ q₂ z₁).mp h₂₃ with ⟨y₁, rfl, hyz⟩
    rcases (pushoutLE_j₁_right_iff sq hi₁ hi₂ q₁ y₁).mp h₁₂ with ⟨x₁, rfl, hxy⟩
    exact Or.inl ⟨x₁, z₁, rfl, rfl, le_trans hxy hyz⟩
  · rcases (pushoutLE_j₂_right_iff sq hi₁ hi₂ q₂ z₂).mp h₂₃ with ⟨y₂, rfl, hyz⟩
    rcases (pushoutLE_j₂_right_iff sq hi₁ hi₂ q₁ y₂).mp h₁₂ with ⟨x₂, rfl, hxy⟩
    exact Or.inr ⟨x₂, z₂, rfl, rfl, le_trans hxy hyz⟩

/-- Direct antisymmetry of `PushoutLE`. -/
theorem pushoutLE_antisymm (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂)
    {q₁ q₂ : Q} (h₁₂ : PushoutLE sq q₁ q₂) (h₂₁ : PushoutLE sq q₂ q₁) :
    q₁ = q₂ := by
  rcases sq.jointly_surj q₂ with ⟨y₁, rfl⟩ | ⟨y₂, rfl⟩
  · rcases (pushoutLE_j₁_right_iff sq hi₁ hi₂ q₁ y₁).mp h₁₂ with ⟨x₁, rfl, hxy⟩
    have hyx : y₁ ≤ x₁ := (pushoutLE_j₁_iff sq hi₁ hi₂ y₁ x₁).mp h₂₁
    rw [le_antisymm hxy hyx]
  · rcases (pushoutLE_j₂_right_iff sq hi₁ hi₂ q₁ y₂).mp h₁₂ with ⟨x₂, rfl, hxy⟩
    have hyx : y₂ ≤ x₂ := (pushoutLE_j₂_iff sq hi₁ hi₂ y₂ x₂).mp h₂₁
    rw [le_antisymm hxy hyx]

/-- Amalgamated dimension map `Q → ℕ` on a `SetPushoutSquare`. -/
noncomputable def pushoutDim (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) : Q → ℕ :=
  sq.desc OrientedGradedPoset.dim OrientedGradedPoset.dim
    (fun a ↦ (hi₁.map_dim a).trans (hi₂.map_dim a).symm)

@[simp]
theorem pushoutDim_j₁ (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) (b₁ : B₁) :
    pushoutDim sq hi₁ hi₂ (j₁ b₁) = OrientedGradedPoset.dim b₁ :=
  sq.desc_j₁ _ _ _ b₁

@[simp]
theorem pushoutDim_j₂ (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) (b₂ : B₂) :
    pushoutDim sq hi₁ hi₂ (j₂ b₂) = OrientedGradedPoset.dim b₂ :=
  sq.desc_j₂ _ _ _ b₂

/-- Non-dependent amalgamated facet sign `Q → Q → Bool`, normalized to `false` outside facets of
`Q` and agreeing with `sign` on both `B₁` and `B₂` along all codimension-1 facets. -/
noncomputable def pushoutSign (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) (q q' : Q) : Bool := by
  classical
  exact if hle : PushoutLE sq q q' ∧
      pushoutDim sq hi₁ hi₂ q' = pushoutDim sq hi₁ hi₂ q + 1 then
    if h₁ : ∃ y₁ : B₁, j₁ y₁ = q' then
      let y₁ := Classical.choose h₁
      have hq : PushoutLE sq q (j₁ y₁) := by
        rw [Classical.choose_spec h₁]
        exact hle.1
      let x₁ := Classical.choose ((pushoutLE_j₁_right_iff sq hi₁ hi₂ q y₁).mp hq)
      OrientedGradedPoset.sign x₁ y₁
    else
      let h₂ : ∃ y₂ : B₂, j₂ y₂ = q' := by
        rcases sq.jointly_surj q' with h | h
        · exact False.elim (h₁ h)
        · exact h
      let y₂ := Classical.choose h₂
      have hq : PushoutLE sq q (j₂ y₂) := by
        rw [Classical.choose_spec h₂]
        exact hle.1
      let x₂ := Classical.choose ((pushoutLE_j₂_right_iff sq hi₁ hi₂ q y₂).mp hq)
      OrientedGradedPoset.sign x₂ y₂
  else
    false

private lemma sign_choose_pullback (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂)
    {x₂ y₂ : B₂} (hf : IsFacet x₂ y₂)
    (hy : ∃ y₁ : B₁, j₁ y₁ = j₂ y₂)
    (hx : ∃ x₁ : B₁, j₁ x₁ = j₂ x₂ ∧ x₁ ≤ Classical.choose hy) :
    OrientedGradedPoset.sign (Classical.choose hx) (Classical.choose hy) =
      OrientedGradedPoset.sign x₂ y₂ := by
  obtain ⟨a, ha₁, ha₂⟩ := sq.pullback_sap (Classical.choose_spec hx).1
  obtain ⟨a', ha'₁, ha'₂⟩ := sq.pullback_sap (Classical.choose_spec hy)
  rw [← ha₁, ← ha'₁, ← ha₂, ← ha'₂]
  have hfa : IsFacet a a' := by
    rw [← hi₂.map_isFacet_iff, ha₂, ha'₂]
    exact hf
  exact (hi₁.map_sign hfa).trans (hi₂.map_sign hfa).symm

/-- `pushoutSign` agrees with `sign` on all codimension-1 facets of `B₁`. -/
theorem pushoutSign_j₁ (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂)
    {x₁ y₁ : B₁} (hf : IsFacet x₁ y₁) :
    pushoutSign sq hi₁ hi₂ (j₁ x₁) (j₁ y₁) = OrientedGradedPoset.sign x₁ y₁ := by
  classical
  have hcond : PushoutLE sq (j₁ x₁) (j₁ y₁) ∧
      pushoutDim sq hi₁ hi₂ (j₁ y₁) = pushoutDim sq hi₁ hi₂ (j₁ x₁) + 1 :=
    ⟨Or.inl ⟨x₁, y₁, rfl, rfl, hf.1⟩, by simp [hf.2]⟩
  have h₁ : ∃ y₁' : B₁, j₁ y₁' = j₁ y₁ := ⟨y₁, rfl⟩
  simp only [pushoutSign, dif_pos hcond, dif_pos h₁]
  exact congrArg₂ OrientedGradedPoset.sign
    (choose_eq_of_inj sq.inj_j₁ _) (choose_eq_of_inj' sq.inj_j₁ _)

/-- `pushoutSign` agrees with `sign` on all codimension-1 facets of `B₂`. -/
theorem pushoutSign_j₂ (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂)
    {x₂ y₂ : B₂} (hf : IsFacet x₂ y₂) :
    pushoutSign sq hi₁ hi₂ (j₂ x₂) (j₂ y₂) = OrientedGradedPoset.sign x₂ y₂ := by
  classical
  have hcond : PushoutLE sq (j₂ x₂) (j₂ y₂) ∧
      pushoutDim sq hi₁ hi₂ (j₂ y₂) = pushoutDim sq hi₁ hi₂ (j₂ x₂) + 1 :=
    ⟨Or.inr ⟨x₂, y₂, rfl, rfl, hf.1⟩, by simp [hf.2]⟩
  by_cases h₁ : ∃ y₁ : B₁, j₁ y₁ = j₂ y₂
  · simp only [pushoutSign, dif_pos hcond, dif_pos h₁]
    exact sign_choose_pullback sq hi₁ hi₂ hf _ _
  · simp only [pushoutSign, dif_pos hcond, dif_neg h₁]
    exact congrArg₂ OrientedGradedPoset.sign
      (choose_eq_of_inj sq.inj_j₂ _) (choose_eq_of_inj' sq.inj_j₂ _)

/-- Amalgamated `OrientedGradedPoset` structure on the vertex `Q` of any `SetPushoutSquare` along
closed cellular embeddings `i₁ : A → B₁` and `i₂ : A → B₂`. -/
noncomputable def pushoutOrientedGradedPoset (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) :
    OrientedGradedPoset Q where
  le := PushoutLE sq
  le_refl := pushoutLE_refl sq
  le_trans _ _ _ := pushoutLE_trans sq hi₁ hi₂
  le_antisymm _ _ := pushoutLE_antisymm sq hi₁ hi₂
  dim := pushoutDim sq hi₁ hi₂
  dim_strictMono := by
    intro q q' hlt
    have hle : PushoutLE sq q q' := hlt.1
    have hne : q ≠ q' := fun h ↦ hlt.2 (h ▸ pushoutLE_refl sq q)
    rcases sq.jointly_surj q' with ⟨y₁, rfl⟩ | ⟨y₂, rfl⟩
    · rcases (pushoutLE_j₁_right_iff sq hi₁ hi₂ q y₁).mp hle with ⟨x₁, rfl, hxy⟩
      have hxne : x₁ ≠ y₁ := fun h ↦ hne (congrArg j₁ h)
      simpa using OrientedGradedPoset.dim_strictMono (lt_of_le_of_ne hxy hxne)
    · rcases (pushoutLE_j₂_right_iff sq hi₁ hi₂ q y₂).mp hle with ⟨x₂, rfl, hxy⟩
      have hxne : x₂ ≠ y₂ := fun h ↦ hne (congrArg j₂ h)
      simpa using OrientedGradedPoset.dim_strictMono (lt_of_le_of_ne hxy hxne)
  sign := pushoutSign sq hi₁ hi₂

/-- Canonical `OrientedGradedPoset` structure on the quotient-free pushout carrier
`CanonicalPushout i₁ i₂`. -/
noncomputable def canonicalPushoutOrientedGradedPoset
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) :
    OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
  pushoutOrientedGradedPoset
    (CanonicalPushout.setPushoutSquare hi₁.injective hi₂.injective) hi₁ hi₂

/-- Left cobase-change `j₁ : B₁ → Q` is a closed cellular embedding into
`pushoutOrientedGradedPoset sq hi₁ hi₂`. -/
theorem pushout_isClosedEmbedding_j₁ (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) :
    @IsClosedEmbedding B₁ Q _ (pushoutOrientedGradedPoset sq hi₁ hi₂) j₁ := by
  letI : OrientedGradedPoset Q := pushoutOrientedGradedPoset sq hi₁ hi₂
  exact
    { mono := fun x₁ y₁ hxy ↦ Or.inl ⟨x₁, y₁, rfl, rfl, hxy⟩
      injective := sq.inj_j₁
      downward_closed := fun y₁ q hq ↦ by
        rcases (pushoutLE_j₁_right_iff sq hi₁ hi₂ q y₁).mp hq with ⟨x₁, rfl, hxy⟩
        exact ⟨x₁, hxy, rfl⟩
      map_dim := pushoutDim_j₁ sq hi₁ hi₂
      map_sign := fun _ _ hf ↦ pushoutSign_j₁ sq hi₁ hi₂ hf }

/-- Right cobase-change `j₂ : B₂ → Q` is a closed cellular embedding into
`pushoutOrientedGradedPoset sq hi₁ hi₂`. -/
theorem pushout_isClosedEmbedding_j₂ (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) :
    @IsClosedEmbedding B₂ Q _ (pushoutOrientedGradedPoset sq hi₁ hi₂) j₂ := by
  letI : OrientedGradedPoset Q := pushoutOrientedGradedPoset sq hi₁ hi₂
  exact
    { mono := fun x₂ y₂ hxy ↦ Or.inr ⟨x₂, y₂, rfl, rfl, hxy⟩
      injective := sq.inj_j₂
      downward_closed := fun y₂ q hq ↦ by
        rcases (pushoutLE_j₂_right_iff sq hi₁ hi₂ q y₂).mp hq with ⟨x₂, rfl, hxy⟩
        exact ⟨x₂, hxy, rfl⟩
      map_dim := pushoutDim_j₂ sq hi₁ hi₂
      map_sign := fun _ _ hf ↦ pushoutSign_j₂ sq hi₁ hi₂ hf }

/-- Symmetric specification of an amalgamated `OrientedGradedPoset` pushout square, allowing left/
right duality without mutating the `OrientedGradedPoset` instance on `Q`. -/
structure AmalgamatedPosetSquare {A B₁ B₂ Q : Type*}
    [OrientedGradedPoset A] [OrientedGradedPoset B₁] [OrientedGradedPoset B₂]
    [OrientedGradedPoset Q]
    (i₁ : A → B₁) (i₂ : A → B₂) (j₁ : B₁ → Q) (j₂ : B₂ → Q) : Prop where
  /-- Underlying Strong Amalgamation set pushout square. -/
  toSetPushout : SetPushoutSquare i₁ i₂ j₁ j₂
  /-- Closedness of `i₁`. -/
  closed_i₁ : IsClosedEmbedding i₁
  /-- Closedness of `i₂`. -/
  closed_i₂ : IsClosedEmbedding i₂
  /-- Closedness of `j₁`. -/
  closed_j₁ : IsClosedEmbedding j₁
  /-- Closedness of `j₂`. -/
  closed_j₂ : IsClosedEmbedding j₂

/-- Symmetry of `AmalgamatedPosetSquare` preserving the ambient `OrientedGradedPoset Q` instance.
-/
theorem AmalgamatedPosetSquare.symm {A B₁ B₂ Q : Type*}
    [OrientedGradedPoset A] [OrientedGradedPoset B₁] [OrientedGradedPoset B₂]
    [OrientedGradedPoset Q] {i₁ : A → B₁} {i₂ : A → B₂} {j₁ : B₁ → Q} {j₂ : B₂ → Q}
    (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂) :
    AmalgamatedPosetSquare i₂ i₁ j₂ j₁ where
  toSetPushout := amalg.toSetPushout.symm
  closed_i₁ := amalg.closed_i₂
  closed_i₂ := amalg.closed_i₁
  closed_j₁ := amalg.closed_j₂
  closed_j₂ := amalg.closed_j₁

/-- `pushoutOrientedGradedPoset sq hi₁ hi₂` canonically satisfies `AmalgamatedPosetSquare`. -/
theorem pushout_amalgamatedPosetSquare (sq : SetPushoutSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) :
    @AmalgamatedPosetSquare A B₁ B₂ Q _ _ _ (pushoutOrientedGradedPoset sq hi₁ hi₂)
      i₁ i₂ j₁ j₂ := by
  letI : OrientedGradedPoset Q := pushoutOrientedGradedPoset sq hi₁ hi₂
  exact
    { toSetPushout := sq
      closed_i₁ := hi₁
      closed_i₂ := hi₂
      closed_j₁ := pushout_isClosedEmbedding_j₁ sq hi₁ hi₂
      closed_j₂ := pushout_isClosedEmbedding_j₂ sq hi₁ hi₂ }

/-- Data-level principal closure order isomorphism `cl_Q (inl b₁) ≃o cl_{B₁} b₁` on
`CanonicalPushout i₁ i₂`. -/
noncomputable def canonicalPushoutClIsoLeft
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) (b₁ : B₁) :
    letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
      canonicalPushoutOrientedGradedPoset hi₁ hi₂
    cl (CanonicalPushout.inl i₁ i₂ b₁) ≃o cl b₁ := by
  letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
    canonicalPushoutOrientedGradedPoset hi₁ hi₂
  exact (pushout_isClosedEmbedding_j₁
    (CanonicalPushout.setPushoutSquare hi₁.injective hi₂.injective) hi₁ hi₂).clOrderIso b₁

/-- Data-level principal closure order isomorphism `cl_Q (inr b₂) ≃o cl_{B₂} b₂` on
`CanonicalPushout i₁ i₂`. -/
noncomputable def canonicalPushoutClIsoRight
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) (b₂ : B₂) :
    letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
      canonicalPushoutOrientedGradedPoset hi₁ hi₂
    cl (CanonicalPushout.inr i₁ i₂ b₂) ≃o cl b₂ := by
  letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
    canonicalPushoutOrientedGradedPoset hi₁ hi₂
  exact (pushout_isClosedEmbedding_j₂
    (CanonicalPushout.setPushoutSquare hi₁.injective hi₂.injective) hi₁ hi₂).clOrderIso b₂

/-- **Strong Amalgamation Property (`SAP`) for Closed `OrientedGradedPoset`s:**
Given closed cellular embeddings `i₁ : A → B₁` and `i₂ : A → B₂`, the quotient-free pushout
`Q = CanonicalPushout i₁ i₂` carries an `OrientedGradedPoset` structure whose canonical legs
`j₁ = inl` and `j₂ = inr` are closed cellular embeddings satisfying exact Strong Amalgamation
(`j₁ b₁ = j₂ b₂ ↔ ∃ a, i₁ a = b₁ ∧ i₂ a = b₂`, `range j₁ ∩ range j₂ = range (j₁ ∘ i₁)`) and
inducing principal-closure order isomorphisms `cl (j₁ b₁) ≃o cl b₁` and `cl (j₂ b₂) ≃o cl b₂`. -/
theorem sap_closed_oriented_poset
    (hi₁ : IsClosedEmbedding i₁) (hi₂ : IsClosedEmbedding i₂) :
    letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
      canonicalPushoutOrientedGradedPoset hi₁ hi₂
    let j₁ := CanonicalPushout.inl i₁ i₂
    let j₂ := CanonicalPushout.inr i₁ i₂
    IsClosedEmbedding j₁ ∧
      IsClosedEmbedding j₂ ∧
      (∀ a : A, j₁ (i₁ a) = j₂ (i₂ a)) ∧
      (∀ b₁ : B₁, ∀ b₂ : B₂, j₁ b₁ = j₂ b₂ ↔ ∃ a : A, i₁ a = b₁ ∧ i₂ a = b₂) ∧
      Set.range j₁ ∩ Set.range j₂ = Set.range (j₁ ∘ i₁) ∧
      (∀ b₁ : B₁, Nonempty (cl (j₁ b₁) ≃o cl b₁)) ∧
      (∀ b₂ : B₂, Nonempty (cl (j₂ b₂) ≃o cl b₂)) := by
  let sq := CanonicalPushout.setPushoutSquare hi₁.injective hi₂.injective
  letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
    canonicalPushoutOrientedGradedPoset hi₁ hi₂
  have hj₁ : IsClosedEmbedding (CanonicalPushout.inl i₁ i₂) :=
    pushout_isClosedEmbedding_j₁ sq hi₁ hi₂
  have hj₂ : IsClosedEmbedding (CanonicalPushout.inr i₁ i₂) :=
    pushout_isClosedEmbedding_j₂ sq hi₁ hi₂
  exact ⟨hj₁, hj₂, sq.comm, fun _ _ ↦ sq.eq_iff, sq.range_inter_eq,
    fun b₁ ↦ ⟨hj₁.clOrderIso b₁⟩, fun b₂ ↦ ⟨hj₂.clOrderIso b₂⟩⟩

end PushoutPoset

/-! ## Section 4: Directed Steiner Flow, Acyclicity, and `steiner_cycle_obstruction` -/

/-- One-step **directed Steiner flow** `x → y` in an `OrientedGradedPoset`: some cell `w` has `x`
as an input (`sign x w = false`) codimension-1 facet and `y` as an output (`sign y w = true`)
codimension-1 facet. -/
def FlowStep {P : Type*} [OrientedGradedPoset P] (x y : P) : Prop :=
  ∃ w : P, IsFacet x w ∧ OrientedGradedPoset.sign x w = false ∧
    IsFacet y w ∧ OrientedGradedPoset.sign y w = true

/-- Non-empty directed flow reachability (`Relation.TransGen FlowStep`). -/
abbrev FlowReach {P : Type*} [OrientedGradedPoset P] (x y : P) : Prop :=
  Relation.TransGen (FlowStep (P := P)) x y

/-- An `OrientedGradedPoset` is **flow-acyclic** (loop-free in the sense of Steiner) when no cell
admits a non-empty directed flow cycle `FlowReach x x`. -/
def IsFlowAcyclic (P : Type*) [OrientedGradedPoset P] : Prop :=
  ∀ x : P, ¬ FlowReach x x

/-- Every `FlowStep x y` relates cells of equal dimension (`dim x = dim y`). -/
theorem FlowStep.dim_eq {P : Type*} [OrientedGradedPoset P] {x y : P} (h : FlowStep x y) :
    OrientedGradedPoset.dim x = OrientedGradedPoset.dim y := by
  rcases h with ⟨w, hxw, _, hyw, _⟩
  have h1 := hxw.2
  have h2 := hyw.2
  omega

/-- Every non-empty directed flow path `FlowReach x y` preserves cell dimension (`dim x = dim y`).
-/
theorem FlowReach.dim_eq {P : Type*} [OrientedGradedPoset P] {x y : P} (h : FlowReach x y) :
    OrientedGradedPoset.dim x = OrientedGradedPoset.dim y := by
  induction h with
  | single hs => exact hs.dim_eq
  | tail _ hs ih => exact ih.trans hs.dim_eq

/-- Closed embeddings push `FlowStep` forward. -/
theorem IsClosedEmbedding.map_flowStep {P Q : Type*}
    [OrientedGradedPoset P] [OrientedGradedPoset Q] {f : P → Q}
    (hf : IsClosedEmbedding f) {x y : P} (h : FlowStep x y) :
    FlowStep (f x) (f y) := by
  rcases h with ⟨w, hxw, hsx, hyw, hsy⟩
  exact ⟨f w, hf.map_isFacet_iff.mpr hxw, (hf.map_sign hxw).trans hsx,
    hf.map_isFacet_iff.mpr hyw, (hf.map_sign hyw).trans hsy⟩

/-- Closed embeddings push `FlowReach` forward. -/
theorem IsClosedEmbedding.map_flowReach {P Q : Type*}
    [OrientedGradedPoset P] [OrientedGradedPoset Q] {f : P → Q}
    (hf : IsClosedEmbedding f) {x y : P} (h : FlowReach x y) :
    FlowReach (f x) (f y) := by
  induction h with
  | single hs => exact .single (hf.map_flowStep hs)
  | tail _ hs ih => exact ih.tail (hf.map_flowStep hs)

/-- Any closed subcomplex of a flow-acyclic `OrientedGradedPoset` is flow-acyclic. -/
theorem IsClosedEmbedding.isFlowAcyclic_domain {P Q : Type*}
    [OrientedGradedPoset P] [OrientedGradedPoset Q] {f : P → Q}
    (hf : IsClosedEmbedding f) (hQ : IsFlowAcyclic Q) :
    IsFlowAcyclic P :=
  fun x hxx ↦ hQ (f x) (hf.map_flowReach hxx)

/-- Discrete two-point `0`-dimensional `OrientedGradedPoset` `{v0, v1}` (`S⁰`). -/
inductive TwoPt : Type
  | v0
  | v1
  deriving DecidableEq, Repr

instance instOrientedGradedPosetTwoPt : OrientedGradedPoset TwoPt where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h
  dim _ := 0
  dim_strictMono _ _ h := absurd h.1.symm h.2
  sign _ _ := false

@[simp]
lemma twoPt_le_iff {a b : TwoPt} : (a ≤ b) ↔ a = b := Iff.rfl

@[simp]
lemma twoPt_dim (a : TwoPt) : OrientedGradedPoset.dim a = 0 := rfl

/-- `TwoPt` has no codimension-1 facets and is therefore `IsFlowAcyclic`. -/
theorem isFlowAcyclic_twoPt : IsFlowAcyclic TwoPt := by
  intro x hxx
  cases hxx with
  | single hs =>
    rcases hs with ⟨_, ⟨_, hdim⟩, _, _, _⟩
    simp at hdim
  | tail _ hs =>
    rcases hs with ⟨_, ⟨_, hdim⟩, _, _, _⟩
    simp at hdim

/-- Forward walking arrow `0 → 1` (`v0, v1` of dimension `0` and `edge` of dimension `1` with
`sign v0 edge = false`, `sign v1 edge = true`). -/
inductive WalkingArrow : Type
  | v0
  | v1
  | edge
  deriving DecidableEq, Repr

/-- Decidable partial order test on `WalkingArrow`. -/
def walkingArrowLEBool : WalkingArrow → WalkingArrow → Bool
  | _, .edge => true
  | .v0, .v0 => true
  | .v1, .v1 => true
  | _, _ => false

/-- Dimension grading on `WalkingArrow`. -/
def walkingArrowDim : WalkingArrow → ℕ
  | .v0 | .v1 => 0
  | .edge => 1

/-- Coface sign on `WalkingArrow` (`v0` is `-`, `v1` is `+`). -/
def walkingArrowSign : WalkingArrow → WalkingArrow → Bool
  | .v0, .edge => false
  | .v1, .edge => true
  | _, _ => false

instance instOrientedGradedPosetWalkingArrow : OrientedGradedPoset WalkingArrow where
  le x y := walkingArrowLEBool x y = true
  le_refl x := by cases x <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide
  dim := walkingArrowDim
  dim_strictMono a b h := by
    rcases h with ⟨hab, hba⟩
    cases a <;> cases b <;> simp_all [walkingArrowLEBool, walkingArrowDim]
  sign := walkingArrowSign

instance : DecidableLE WalkingArrow :=
  fun a b ↦ inferInstanceAs (Decidable (walkingArrowLEBool a b = true))

/-- Exact characterization of `FlowStep` in `WalkingArrow`: `x → y ↔ x = .v0 ∧ y = .v1`. -/
theorem walkingArrow_flowStep_iff {x y : WalkingArrow} :
    FlowStep x y ↔ x = .v0 ∧ y = .v1 := by
  constructor
  · rintro ⟨w, ⟨hxle, hxdim⟩, hxs, ⟨hyle, hydim⟩, hys⟩
    cases x <;> cases y <;> cases w <;>
      revert hxle hxdim hxs hyle hydim hys <;> decide
  · rintro ⟨rfl, rfl⟩
    exact ⟨.edge, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩

/-- Exact characterization of `FlowReach` in `WalkingArrow`. -/
theorem walkingArrow_flowReach_iff {x y : WalkingArrow} :
    FlowReach x y ↔ x = .v0 ∧ y = .v1 := by
  constructor
  · intro h
    induction h with
    | single hs => exact walkingArrow_flowStep_iff.mp hs
    | tail _ hs ih =>
      rcases ih with ⟨rfl, rfl⟩
      rcases walkingArrow_flowStep_iff.mp hs with ⟨hb, _⟩
      cases hb
  · rintro ⟨rfl, rfl⟩
    exact .single (walkingArrow_flowStep_iff.mpr ⟨rfl, rfl⟩)

/-- `WalkingArrow = (0 → 1)` is `IsFlowAcyclic`. -/
theorem isFlowAcyclic_walkingArrow : IsFlowAcyclic WalkingArrow := by
  intro x hxx
  rcases walkingArrow_flowReach_iff.mp hxx with ⟨rfl, h⟩
  cases h

/-- Reverse walking arrow `1 → 0` (`v0, v1` of dimension `0` and `edge` of dimension `1` with
`sign v1 edge = false`, `sign v0 edge = true`). -/
inductive RevWalkingArrow : Type
  | v0
  | v1
  | edge
  deriving DecidableEq, Repr

/-- Decidable partial order test on `RevWalkingArrow`. -/
def revWalkingArrowLEBool : RevWalkingArrow → RevWalkingArrow → Bool
  | _, .edge => true
  | .v0, .v0 => true
  | .v1, .v1 => true
  | _, _ => false

/-- Dimension grading on `RevWalkingArrow`. -/
def revWalkingArrowDim : RevWalkingArrow → ℕ
  | .v0 | .v1 => 0
  | .edge => 1

/-- Coface sign on `RevWalkingArrow` (`v1` is `-`, `v0` is `+`). -/
def revWalkingArrowSign : RevWalkingArrow → RevWalkingArrow → Bool
  | .v1, .edge => false
  | .v0, .edge => true
  | _, _ => false

instance instOrientedGradedPosetRevWalkingArrow : OrientedGradedPoset RevWalkingArrow where
  le x y := revWalkingArrowLEBool x y = true
  le_refl x := by cases x <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide
  dim := revWalkingArrowDim
  dim_strictMono a b h := by
    rcases h with ⟨hab, hba⟩
    cases a <;> cases b <;> simp_all [revWalkingArrowLEBool, revWalkingArrowDim]
  sign := revWalkingArrowSign

instance : DecidableLE RevWalkingArrow :=
  fun a b ↦ inferInstanceAs (Decidable (revWalkingArrowLEBool a b = true))

/-- Exact characterization of `FlowStep` in `RevWalkingArrow`: `x → y ↔ x = .v1 ∧ y = .v0`. -/
theorem revWalkingArrow_flowStep_iff {x y : RevWalkingArrow} :
    FlowStep x y ↔ x = .v1 ∧ y = .v0 := by
  constructor
  · rintro ⟨w, ⟨hxle, hxdim⟩, hxs, ⟨hyle, hydim⟩, hys⟩
    cases x <;> cases y <;> cases w <;>
      revert hxle hxdim hxs hyle hydim hys <;> decide
  · rintro ⟨rfl, rfl⟩
    exact ⟨.edge, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩

/-- Exact characterization of `FlowReach` in `RevWalkingArrow`. -/
theorem revWalkingArrow_flowReach_iff {x y : RevWalkingArrow} :
    FlowReach x y ↔ x = .v1 ∧ y = .v0 := by
  constructor
  · intro h
    induction h with
    | single hs => exact revWalkingArrow_flowStep_iff.mp hs
    | tail _ hs ih =>
      rcases ih with ⟨rfl, rfl⟩
      rcases revWalkingArrow_flowStep_iff.mp hs with ⟨hb, _⟩
      cases hb
  · rintro ⟨rfl, rfl⟩
    exact .single (revWalkingArrow_flowStep_iff.mpr ⟨rfl, rfl⟩)

/-- `RevWalkingArrow = (1 → 0)` is `IsFlowAcyclic`. -/
theorem isFlowAcyclic_revWalkingArrow : IsFlowAcyclic RevWalkingArrow := by
  intro x hxx
  rcases revWalkingArrow_flowReach_iff.mp hxx with ⟨rfl, h⟩
  cases h

/-- Boundary inclusion `{0, 1} ↪ (0 → 1)`. -/
def steinerLeft : TwoPt → WalkingArrow
  | .v0 => .v0
  | .v1 => .v1

/-- Boundary inclusion `{0, 1} ↪ (1 → 0)`. -/
def steinerRight : TwoPt → RevWalkingArrow
  | .v0 => .v0
  | .v1 => .v1

/-- `steinerLeft : TwoPt → WalkingArrow` is a closed cellular embedding. -/
theorem isClosedEmbedding_steinerLeft : IsClosedEmbedding steinerLeft where
  mono a b h := by
    rw [twoPt_le_iff] at h
    subst h
    exact le_rfl
  injective a b h := by
    cases a <;> cases b <;> cases h <;> rfl
  downward_closed x q hq := by
    cases x with
    | v0 =>
      cases q with
      | v0 => exact ⟨.v0, rfl, rfl⟩
      | v1 | edge => exact absurd hq (by decide)
    | v1 =>
      cases q with
      | v1 => exact ⟨.v1, rfl, rfl⟩
      | v0 | edge => exact absurd hq (by decide)
  map_dim x := by cases x <;> rfl
  map_sign _ _ h := by
    rcases h with ⟨_, hd⟩
    simp at hd

/-- `steinerRight : TwoPt → RevWalkingArrow` is a closed cellular embedding. -/
theorem isClosedEmbedding_steinerRight : IsClosedEmbedding steinerRight where
  mono a b h := by
    rw [twoPt_le_iff] at h
    subst h
    exact le_rfl
  injective a b h := by
    cases a <;> cases b <;> cases h <;> rfl
  downward_closed x q hq := by
    cases x with
    | v0 =>
      cases q with
      | v0 => exact ⟨.v0, rfl, rfl⟩
      | v1 | edge => exact absurd hq (by decide)
    | v1 =>
      cases q with
      | v1 => exact ⟨.v1, rfl, rfl⟩
      | v0 | edge => exact absurd hq (by decide)
  map_dim x := by cases x <;> rfl
  map_sign _ _ h := by
    rcases h with ⟨_, hd⟩
    simp at hd

/-- The amalgamated Steiner pushout `SteinerPushout := (0 → 1) ⊔_{0, 1} (1 → 0)` (`0 ⇄ 1`). -/
abbrev SteinerPushout : Type :=
  CanonicalPushout steinerLeft steinerRight

noncomputable instance instOrientedGradedPosetSteinerPushout :
    OrientedGradedPoset SteinerPushout :=
  canonicalPushoutOrientedGradedPoset isClosedEmbedding_steinerLeft isClosedEmbedding_steinerRight

/-- **Steiner Cycle Obstruction Theorem (`steiner_cycle_obstruction`):**
`TwoPt = {0, 1}`, `WalkingArrow = (0 → 1)`, and `RevWalkingArrow = (1 → 0)` are all finite
`IsFlowAcyclic` `OrientedGradedPoset`s and both boundary inclusions `steinerLeft` and
`steinerRight` are `IsClosedEmbedding`s, yet their amalgamated pushout `SteinerPushout` exhibits
the directed 2-cycle `inl v0 → inl v1 → inl v0` and **violates `IsFlowAcyclic`**. -/
theorem steiner_cycle_obstruction :
    IsFlowAcyclic TwoPt ∧
      IsFlowAcyclic WalkingArrow ∧
      IsFlowAcyclic RevWalkingArrow ∧
      IsClosedEmbedding steinerLeft ∧
      IsClosedEmbedding steinerRight ∧
      FlowStep (CanonicalPushout.inl steinerLeft steinerRight .v0)
        (CanonicalPushout.inl steinerLeft steinerRight .v1) ∧
      FlowStep (CanonicalPushout.inl steinerLeft steinerRight .v1)
        (CanonicalPushout.inl steinerLeft steinerRight .v0) ∧
      ¬ IsFlowAcyclic SteinerPushout := by
  let sq := CanonicalPushout.setPushoutSquare
    isClosedEmbedding_steinerLeft.injective isClosedEmbedding_steinerRight.injective
  have hj₁ : IsClosedEmbedding (CanonicalPushout.inl steinerLeft steinerRight) :=
    pushout_isClosedEmbedding_j₁ sq isClosedEmbedding_steinerLeft isClosedEmbedding_steinerRight
  have hj₂ : IsClosedEmbedding (CanonicalPushout.inr steinerLeft steinerRight) :=
    pushout_isClosedEmbedding_j₂ sq isClosedEmbedding_steinerLeft isClosedEmbedding_steinerRight
  have hfwd : FlowStep (CanonicalPushout.inl steinerLeft steinerRight .v0)
      (CanonicalPushout.inl steinerLeft steinerRight .v1) :=
    hj₁.map_flowStep (walkingArrow_flowStep_iff.mpr ⟨rfl, rfl⟩)
  have hrev_raw : FlowStep (CanonicalPushout.inr steinerLeft steinerRight .v1)
      (CanonicalPushout.inr steinerLeft steinerRight .v0) :=
    hj₂.map_flowStep (revWalkingArrow_flowStep_iff.mpr ⟨rfl, rfl⟩)
  have hv0 : CanonicalPushout.inl steinerLeft steinerRight .v0 =
      CanonicalPushout.inr steinerLeft steinerRight .v0 :=
    sq.comm .v0
  have hv1 : CanonicalPushout.inl steinerLeft steinerRight .v1 =
      CanonicalPushout.inr steinerLeft steinerRight .v1 :=
    sq.comm .v1
  have hrev : FlowStep (CanonicalPushout.inl steinerLeft steinerRight .v1)
      (CanonicalPushout.inl steinerLeft steinerRight .v0) := by
    rwa [hv1, hv0]
  have hnot : ¬ IsFlowAcyclic SteinerPushout := by
    intro hacyc
    exact hacyc (CanonicalPushout.inl steinerLeft steinerRight .v0)
      ((Relation.TransGen.single hfwd).tail hrev)
  exact ⟨isFlowAcyclic_twoPt, isFlowAcyclic_walkingArrow, isFlowAcyclic_revWalkingArrow,
    isClosedEmbedding_steinerLeft, isClosedEmbedding_steinerRight, hfwd, hrev, hnot⟩

/-! ## Section 5: `IsFlowReachReflecting` and `IsFlowConvex` — SAP & Flow-Acyclicity Preservation -/

/-- A map `f : P → Q` of `OrientedGradedPoset`s is **flow-reach-reflecting** when it is an order
embedding onto a downward-closed (`IsLowerSet`) subcomplex preserving dimension and facet signs,
and reflects directed reachability (`FlowReach (f x) (f y) → FlowReach x y`). -/
structure IsFlowReachReflecting {P Q : Type*}
    [OrientedGradedPoset P] [OrientedGradedPoset Q] (f : P → Q) : Prop where
  /-- Order-embedding equivalence `f x ≤ f y ↔ x ≤ y`. -/
  map_le_iff : ∀ ⦃x y : P⦄, f x ≤ f y ↔ x ≤ y
  /-- Downward-closedness of `Set.range f` as a stock `IsLowerSet`. -/
  isLowerSet_range : IsLowerSet (Set.range f)
  /-- Exact preservation of dimension. -/
  map_dim : ∀ x : P, OrientedGradedPoset.dim (f x) = OrientedGradedPoset.dim x
  /-- Preservation of coface orientation sign on codimension-1 facets. -/
  map_sign : ∀ ⦃x y : P⦄, IsFacet x y →
    OrientedGradedPoset.sign (f x) (f y) = OrientedGradedPoset.sign x y
  /-- Reflection of non-empty directed reachability (`FlowReach`). -/
  reflect_flowReach : ∀ ⦃x y : P⦄, FlowReach (f x) (f y) → FlowReach x y

/-- A map `f : P → Q` of `OrientedGradedPoset`s is **flow-convex** when it is an order embedding
onto a downward-closed (`IsLowerSet`) subcomplex preserving dimension and facet signs, whose range
contains both every cell `w` witnessing a single `FlowStep` between elements of `Set.range f` and
every intermediate vertex `u` along any directed flow path between elements of `Set.range f`. -/
structure IsFlowConvex {P Q : Type*}
    [OrientedGradedPoset P] [OrientedGradedPoset Q] (f : P → Q) : Prop where
  /-- Order-embedding equivalence `f x ≤ f y ↔ x ≤ y`. -/
  map_le_iff : ∀ ⦃x y : P⦄, f x ≤ f y ↔ x ≤ y
  /-- Downward-closedness of `Set.range f` as a stock `IsLowerSet`. -/
  isLowerSet_range : IsLowerSet (Set.range f)
  /-- Exact preservation of dimension. -/
  map_dim : ∀ x : P, OrientedGradedPoset.dim (f x) = OrientedGradedPoset.dim x
  /-- Preservation of coface orientation sign on codimension-1 facets. -/
  map_sign : ∀ ⦃x y : P⦄, IsFacet x y →
    OrientedGradedPoset.sign (f x) (f y) = OrientedGradedPoset.sign x y
  /-- Witness-cell convexity: any cell `w : Q` mediating `f x → f y` lies in `Set.range f`. -/
  cell_mem : ∀ ⦃x y : P⦄ ⦃w : Q⦄,
    IsFacet (f x) w → OrientedGradedPoset.sign (f x) w = false →
    IsFacet (f y) w → OrientedGradedPoset.sign (f y) w = true → w ∈ Set.range f
  /-- Directed-interval convexity: any vertex `u : Q` on a flow path `f x →+ u →+ f y` lies in
  `Set.range f`. -/
  inter_mem : ∀ ⦃x y : P⦄ ⦃u : Q⦄, FlowReach (f x) u → FlowReach u (f y) → u ∈ Set.range f

namespace IsFlowReachReflecting

variable {P Q R : Type*} [OrientedGradedPoset P] [OrientedGradedPoset Q] [OrientedGradedPoset R]
variable {f : P → Q} {g : Q → R}

/-- Derived injectivity of a flow-reach-reflecting map via `le_antisymm` and `map_le_iff`. -/
theorem injective (hf : IsFlowReachReflecting f) : Function.Injective f := by
  intro x y hxy
  exact le_antisymm (hf.map_le_iff.mp (le_of_eq hxy)) (hf.map_le_iff.mp (le_of_eq hxy.symm))

/-- **Derived Hierarchy Theorem (`IsFlowReachReflecting → IsClosedEmbedding`):** every
flow-reach-reflecting map is a closed cellular embedding (synthesizing `injective` and principal-
closure downward-closedness from `map_le_iff` and `isLowerSet_range`). -/
theorem toIsClosedEmbedding (hf : IsFlowReachReflecting f) : IsClosedEmbedding f where
  mono _ _ h := hf.map_le_iff.mpr h
  injective := hf.injective
  downward_closed x q hq := by
    rcases hf.isLowerSet_range hq ⟨x, rfl⟩ with ⟨a, rfl⟩
    exact ⟨a, hf.map_le_iff.mp hq, rfl⟩
  map_dim := hf.map_dim
  map_sign := hf.map_sign

/-- Constructor building `IsFlowReachReflecting f` from `IsClosedEmbedding f` and reachability
reflection. -/
theorem ofClosedEmbedding (hf : IsClosedEmbedding f)
    (hrefl : ∀ ⦃x y : P⦄, FlowReach (f x) (f y) → FlowReach x y) :
    IsFlowReachReflecting f where
  map_le_iff := fun _ _ ↦ hf.map_le_iff
  isLowerSet_range := hf.isLowerSet_range
  map_dim := hf.map_dim
  map_sign := hf.map_sign
  reflect_flowReach := hrefl

/-- Exact equivalence `FlowReach (f x) (f y) ↔ FlowReach x y` for `IsFlowReachReflecting f`. -/
theorem flowReach_iff (hf : IsFlowReachReflecting f) {x y : P} :
    FlowReach (f x) (f y) ↔ FlowReach x y :=
  ⟨fun h ↦ hf.reflect_flowReach h, fun h ↦ hf.toIsClosedEmbedding.map_flowReach h⟩

/-- Identity map is `IsFlowReachReflecting`. -/
theorem id (P : Type*) [OrientedGradedPoset P] :
    IsFlowReachReflecting (_root_.id : P → P) :=
  ofClosedEmbedding (IsClosedEmbedding.id P) (fun _ _ h ↦ h)

/-- `IsFlowReachReflecting` is closed under composition. -/
theorem comp (hg : IsFlowReachReflecting g) (hf : IsFlowReachReflecting f) :
    IsFlowReachReflecting (g ∘ f) :=
  ofClosedEmbedding (hg.toIsClosedEmbedding.comp hf.toIsClosedEmbedding)
    (fun _ _ h ↦ hf.reflect_flowReach (hg.reflect_flowReach h))

end IsFlowReachReflecting

namespace IsFlowConvex

variable {P Q R : Type*} [OrientedGradedPoset P] [OrientedGradedPoset Q] [OrientedGradedPoset R]
variable {f : P → Q} {g : Q → R}

/-- Derived injectivity of a flow-convex map. -/
theorem injective (hf : IsFlowConvex f) : Function.Injective f := by
  intro x y hxy
  exact le_antisymm (hf.map_le_iff.mp (le_of_eq hxy)) (hf.map_le_iff.mp (le_of_eq hxy.symm))

/-- Derived closed-embedding theorem for `IsFlowConvex`. -/
theorem toIsClosedEmbedding (hf : IsFlowConvex f) : IsClosedEmbedding f where
  mono _ _ h := hf.map_le_iff.mpr h
  injective := hf.injective
  downward_closed x q hq := by
    rcases hf.isLowerSet_range hq ⟨x, rfl⟩ with ⟨a, rfl⟩
    exact ⟨a, hf.map_le_iff.mp hq, rfl⟩
  map_dim := hf.map_dim
  map_sign := hf.map_sign

/-- Derived 1-step `FlowStep` reflection for `IsFlowConvex`: any single step `f x → f y` in `Q`
has its mediating cell `w` in `Set.range f`, hence lifts to `FlowStep x y` in `P`. -/
theorem reflect_flowStep (hf : IsFlowConvex f) {x y : P} (h : FlowStep (f x) (f y)) :
    FlowStep x y := by
  have hcl := hf.toIsClosedEmbedding
  rcases h with ⟨w, hxw, hsx, hyw, hsy⟩
  rcases hf.cell_mem hxw hsx hyw hsy with ⟨z, rfl⟩
  exact ⟨z, hcl.map_isFacet_iff.mp hxw, (hcl.map_sign (hcl.map_isFacet_iff.mp hxw)).symm.trans hsx,
    hcl.map_isFacet_iff.mp hyw, (hcl.map_sign (hcl.map_isFacet_iff.mp hyw)).symm.trans hsy⟩

/-- **Derived Hierarchy Theorem (`IsFlowConvex → IsFlowReachReflecting`):** every flow-convex map
is flow-reach-reflecting, proved by `Relation.TransGen.head_induction_on` pulling each intermediate
vertex into `Set.range f` via `inter_mem` and reflecting each step via `reflect_flowStep`. -/
theorem toIsFlowReachReflecting (hf : IsFlowConvex f) : IsFlowReachReflecting f where
  map_le_iff := hf.map_le_iff
  isLowerSet_range := hf.isLowerSet_range
  map_dim := hf.map_dim
  map_sign := hf.map_sign
  reflect_flowReach {x y} hreach := by
    have haux : ∀ u : Q, FlowReach u (f y) → ∀ a : P, f a = u → FlowReach a y := by
      intro u hu
      induction hu using Relation.TransGen.head_induction_on with
      | single hs =>
        intro a ha
        subst ha
        exact .single (hf.reflect_flowStep hs)
      | head hs hrest ih =>
        intro a ha
        subst ha
        rcases hf.inter_mem (.single hs) hrest with ⟨z, rfl⟩
        exact (ih z rfl).head (hf.reflect_flowStep hs)
    exact haux (f x) hreach x rfl

/-- Constructor building `IsFlowConvex f` from `IsClosedEmbedding f`, `cell_mem`, and `inter_mem`.
-/
theorem ofClosedEmbedding (hf : IsClosedEmbedding f)
    (hcell : ∀ ⦃x y : P⦄ ⦃w : Q⦄,
      IsFacet (f x) w → OrientedGradedPoset.sign (f x) w = false →
      IsFacet (f y) w → OrientedGradedPoset.sign (f y) w = true → w ∈ Set.range f)
    (hinter : ∀ ⦃x y : P⦄ ⦃u : Q⦄, FlowReach (f x) u → FlowReach u (f y) → u ∈ Set.range f) :
    IsFlowConvex f where
  map_le_iff := fun _ _ ↦ hf.map_le_iff
  isLowerSet_range := hf.isLowerSet_range
  map_dim := hf.map_dim
  map_sign := hf.map_sign
  cell_mem := hcell
  inter_mem := hinter

/-- Identity map is `IsFlowConvex`. -/
theorem id (P : Type*) [OrientedGradedPoset P] :
    IsFlowConvex (_root_.id : P → P) :=
  ofClosedEmbedding (IsClosedEmbedding.id P)
    (fun _ _ w _ _ _ _ ↦ ⟨w, rfl⟩)
    (fun _ _ u _ _ ↦ ⟨u, rfl⟩)

/-- `IsFlowConvex` is closed under composition (using `hg.toIsFlowReachReflecting` to reflect
intermediate path segments into `Q`). -/
theorem comp (hg : IsFlowConvex g) (hf : IsFlowConvex f) :
    IsFlowConvex (g ∘ f) := by
  have hg_cl := hg.toIsClosedEmbedding
  have hg_refl := hg.toIsFlowReachReflecting
  refine ofClosedEmbedding (hg_cl.comp hf.toIsClosedEmbedding) ?_ ?_
  · intro x y w hxw hsx hyw hsy
    rcases hg.cell_mem hxw hsx hyw hsy with ⟨wQ, rfl⟩
    have hfxw : IsFacet (f x) wQ := hg_cl.map_isFacet_iff.mp hxw
    have hfyw : IsFacet (f y) wQ := hg_cl.map_isFacet_iff.mp hyw
    have hsxQ : OrientedGradedPoset.sign (f x) wQ = false :=
      (hg_cl.map_sign hfxw).symm.trans hsx
    have hsyQ : OrientedGradedPoset.sign (f y) wQ = true :=
      (hg_cl.map_sign hfyw).symm.trans hsy
    rcases hf.cell_mem hfxw hsxQ hfyw hsyQ with ⟨wP, rfl⟩
    exact ⟨wP, rfl⟩
  · intro x y u hxu huy
    rcases hg.inter_mem hxu huy with ⟨uQ, rfl⟩
    rcases hf.inter_mem (hg_refl.reflect_flowReach hxu) (hg_refl.reflect_flowReach huy) with
      ⟨uP, rfl⟩
    exact ⟨uP, rfl⟩

end IsFlowConvex

namespace AmalgamatedPosetSquare

variable {A B₁ B₂ Q : Type*}
variable [OrientedGradedPoset A] [OrientedGradedPoset B₁] [OrientedGradedPoset B₂]
variable [OrientedGradedPoset Q]
variable {i₁ : A → B₁} {i₂ : A → B₂} {j₁ : B₁ → Q} {j₂ : B₂ → Q}

/-- **Exact `FlowStep` Union Decomposition on Amalgamated Pushouts:** because `j₁` and `j₂` are
jointly surjective closed embeddings, every `FlowStep u v` in `Q` lifts to a `FlowStep` in `B₁` or
a `FlowStep` in `B₂`. -/
theorem flowStep_iff (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂) {u v : Q} :
    FlowStep u v ↔
      (∃ u₁ v₁ : B₁, j₁ u₁ = u ∧ j₁ v₁ = v ∧ FlowStep u₁ v₁) ∨
        (∃ u₂ v₂ : B₂, j₂ u₂ = u ∧ j₂ v₂ = v ∧ FlowStep u₂ v₂) := by
  constructor
  · rintro ⟨w, huw, hsu, hvw, hsv⟩
    rcases amalg.toSetPushout.jointly_surj w with ⟨w₁, rfl⟩ | ⟨w₂, rfl⟩
    · rcases amalg.closed_j₁.downward_closed huw.1 with ⟨u₁, _, rfl⟩
      rcases amalg.closed_j₁.downward_closed hvw.1 with ⟨v₁, _, rfl⟩
      have hu₁ : IsFacet u₁ w₁ := amalg.closed_j₁.map_isFacet_iff.mp huw
      have hv₁ : IsFacet v₁ w₁ := amalg.closed_j₁.map_isFacet_iff.mp hvw
      exact Or.inl ⟨u₁, v₁, rfl, rfl, w₁, hu₁,
        (amalg.closed_j₁.map_sign hu₁).symm.trans hsu, hv₁,
        (amalg.closed_j₁.map_sign hv₁).symm.trans hsv⟩
    · rcases amalg.closed_j₂.downward_closed huw.1 with ⟨u₂, _, rfl⟩
      rcases amalg.closed_j₂.downward_closed hvw.1 with ⟨v₂, _, rfl⟩
      have hu₂ : IsFacet u₂ w₂ := amalg.closed_j₂.map_isFacet_iff.mp huw
      have hv₂ : IsFacet v₂ w₂ := amalg.closed_j₂.map_isFacet_iff.mp hvw
      exact Or.inr ⟨u₂, v₂, rfl, rfl, w₂, hu₂,
        (amalg.closed_j₂.map_sign hu₂).symm.trans hsu, hv₂,
        (amalg.closed_j₂.map_sign hv₂).symm.trans hsv⟩
  · rintro (⟨u₁, v₁, rfl, rfl, hs⟩ | ⟨u₂, v₂, rfl, rfl, hs⟩)
    · exact amalg.closed_j₁.map_flowStep hs
    · exact amalg.closed_j₂.map_flowStep hs

/-- Forward 2-state reachability invariant from `j₁ x` (`x : B₁`) to `v : Q`: either `v` lies in
`Set.range j₁` with `FlowReach x y`, or `v` is currently on a `B₂`-excursion from a shared `A`-cell
`a`. -/
private def ReachFromLeft (_amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (x : B₁) (v : Q) : Prop :=
  (∃ y : B₁, j₁ y = v ∧ FlowReach x y) ∨
    (∃ (z : B₁) (a : A) (v₂ : B₂),
      (z = x ∨ FlowReach x z) ∧ i₁ a = z ∧ j₂ v₂ = v ∧ FlowReach (i₂ a) v₂)

private theorem reachFromLeft_extract (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₂ : IsFlowReachReflecting i₂) {x y : B₁}
    (h : amalg.ReachFromLeft x (j₁ y)) : FlowReach x y := by
  rcases h with ⟨y', hy', hxy⟩ | ⟨z, a, v₂, hxz, rfl, hv₂, ha_v₂⟩
  · rwa [amalg.toSetPushout.inj_j₁ hy'] at hxy
  · rcases amalg.toSetPushout.pullback_sap hv₂.symm with ⟨a', rfl, rfl⟩
    have haa' : FlowReach (i₁ a) (i₁ a') :=
      amalg.closed_i₁.map_flowReach (hi₂.reflect_flowReach ha_v₂)
    rcases hxz with hzx | hxz
    · rwa [← hzx]
    · exact hxz.trans haa'

private theorem reachFromLeft_of_flowReach (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₂ : IsFlowReachReflecting i₂) {x : B₁} {v : Q}
    (h : FlowReach (j₁ x) v) : amalg.ReachFromLeft x v := by
  induction h with
  | single hs =>
    rcases (amalg.flowStep_iff).mp hs with
      ⟨u₁, v₁, hu₁, rfl, hs₁⟩ | ⟨u₂, v₂, hu₂, rfl, hs₂⟩
    · rw [amalg.toSetPushout.inj_j₁ hu₁] at hs₁
      exact Or.inl ⟨v₁, rfl, .single hs₁⟩
    · rcases amalg.toSetPushout.pullback_sap hu₂.symm with ⟨a, rfl, rfl⟩
      exact Or.inr ⟨i₁ a, a, v₂, Or.inl rfl, rfl, rfl, .single hs₂⟩
  | @tail u w _ hstep ih =>
    rcases (amalg.flowStep_iff).mp hstep with
      ⟨u₁, w₁, rfl, rfl, hs₁⟩ | ⟨u₂, w₂, hu₂, rfl, hs₂⟩
    · exact Or.inl ⟨w₁, rfl, (amalg.reachFromLeft_extract hi₂ ih).tail hs₁⟩
    · rcases ih with ⟨y₁, hy₁, hxy₁⟩ | ⟨z, a, v₂, hxz, ha, hv₂, hav₂⟩
      · have hj : j₁ y₁ = j₂ u₂ := hy₁.trans hu₂.symm
        rcases amalg.toSetPushout.pullback_sap hj with ⟨a, rfl, rfl⟩
        exact Or.inr ⟨i₁ a, a, w₂, Or.inr hxy₁, rfl, rfl, .single hs₂⟩
      · have hv₂_eq : v₂ = u₂ := amalg.toSetPushout.inj_j₂ (hv₂.trans hu₂.symm)
        subst hv₂_eq
        exact Or.inr ⟨z, a, w₂, hxz, ha, rfl, hav₂.tail hs₂⟩

/-- **Cobase-Change of `IsFlowReachReflecting` (Left Leg):** if `i₂ : A → B₂` is
`IsFlowReachReflecting` in an `AmalgamatedPosetSquare`, then its cobase-change `j₁ : B₁ → Q` is
also `IsFlowReachReflecting`. -/
theorem isFlowReachReflecting_j₁ (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₂ : IsFlowReachReflecting i₂) : IsFlowReachReflecting j₁ :=
  IsFlowReachReflecting.ofClosedEmbedding amalg.closed_j₁
    (fun _ _ h ↦ amalg.reachFromLeft_extract hi₂ (amalg.reachFromLeft_of_flowReach hi₂ h))

/-- **Cobase-Change of `IsFlowReachReflecting` (Right Leg):** if `i₁ : A → B₁` is
`IsFlowReachReflecting` in an `AmalgamatedPosetSquare`, then its cobase-change `j₂ : B₂ → Q` is
also `IsFlowReachReflecting`. -/
theorem isFlowReachReflecting_j₂ (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsFlowReachReflecting i₁) : IsFlowReachReflecting j₂ :=
  amalg.symm.isFlowReachReflecting_j₁ hi₁

/-- **Flow-Acyclicity Preservation under `IsFlowReachReflecting` Pushouts:** if both `B₁` and `B₂`
are `IsFlowAcyclic` and both legs `i₁, i₂` are `IsFlowReachReflecting`, then `Q` is `IsFlowAcyclic`.
-/
theorem isFlowAcyclic_of_flowReachReflecting (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsFlowReachReflecting i₁) (hi₂ : IsFlowReachReflecting i₂)
    (hB₁ : IsFlowAcyclic B₁) (hB₂ : IsFlowAcyclic B₂) :
    IsFlowAcyclic Q := by
  have hj₁ := amalg.isFlowReachReflecting_j₁ hi₂
  have hj₂ := amalg.isFlowReachReflecting_j₂ hi₁
  intro q hqq
  rcases amalg.toSetPushout.jointly_surj q with ⟨b₁, rfl⟩ | ⟨b₂, rfl⟩
  · exact hB₁ b₁ (hj₁.reflect_flowReach hqq)
  · exact hB₂ b₂ (hj₂.reflect_flowReach hqq)

/-- Backward 2-state reachability invariant from `u : Q` to `j₁ y` (`y : B₁`). -/
private def ReachToLeft (_amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (u : Q) (y : B₁) : Prop :=
  (∃ x : B₁, j₁ x = u ∧ FlowReach x y) ∨
    (∃ (w : B₁) (a : A) (u₂ : B₂),
      (w = y ∨ FlowReach w y) ∧ i₁ a = w ∧ j₂ u₂ = u ∧ FlowReach u₂ (i₂ a))

private theorem reachToLeft_extract (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₂ : IsFlowReachReflecting i₂) {x y : B₁}
    (h : amalg.ReachToLeft (j₁ x) y) : FlowReach x y := by
  rcases h with ⟨x', hx', hxy⟩ | ⟨w, a, u₂, hwy, rfl, hu₂, hu₂_a⟩
  · rwa [amalg.toSetPushout.inj_j₁ hx'] at hxy
  · rcases amalg.toSetPushout.pullback_sap hu₂.symm with ⟨a', rfl, rfl⟩
    have ha'a : FlowReach (i₁ a') (i₁ a) :=
      amalg.closed_i₁.map_flowReach (hi₂.reflect_flowReach hu₂_a)
    rcases hwy with hwy | hwy
    · rwa [hwy] at ha'a
    · exact ha'a.trans hwy

private theorem reachToLeft_of_flowReach (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₂ : IsFlowReachReflecting i₂) {u : Q} {y : B₁}
    (h : FlowReach u (j₁ y)) : amalg.ReachToLeft u y := by
  induction h using Relation.TransGen.head_induction_on with
  | single hs =>
    rcases (amalg.flowStep_iff).mp hs with
      ⟨u₁, v₁, rfl, hv₁, hs₁⟩ | ⟨u₂, v₂, rfl, hv₂, hs₂⟩
    · rw [amalg.toSetPushout.inj_j₁ hv₁] at hs₁
      exact Or.inl ⟨u₁, rfl, .single hs₁⟩
    · rcases amalg.toSetPushout.pullback_sap hv₂.symm with ⟨a, rfl, rfl⟩
      exact Or.inr ⟨i₁ a, a, u₂, Or.inl rfl, rfl, rfl, .single hs₂⟩
  | @head u' c hstep _ ih =>
    rcases (amalg.flowStep_iff).mp hstep with
      ⟨u'₁, c₁, rfl, rfl, hs₁⟩ | ⟨u'₂, c₂, rfl, hc₂, hs₂⟩
    · exact Or.inl ⟨u'₁, rfl, (amalg.reachToLeft_extract hi₂ ih).head hs₁⟩
    · rcases ih with ⟨x₁, hx₁, hx₁y⟩ | ⟨w, a, u₂, hwy, ha, hu₂, hu₂a⟩
      · have hj : j₁ x₁ = j₂ c₂ := hx₁.trans hc₂.symm
        rcases amalg.toSetPushout.pullback_sap hj with ⟨a, rfl, rfl⟩
        exact Or.inr ⟨i₁ a, a, u'₂, Or.inr hx₁y, rfl, rfl, .single hs₂⟩
      · have hc₂_eq : c₂ = u₂ := amalg.toSetPushout.inj_j₂ (hc₂.trans hu₂.symm)
        subst hc₂_eq
        exact Or.inr ⟨w, a, u'₂, hwy, ha, rfl, hu₂a.head hs₂⟩

/-- **Cobase-Change of `IsFlowConvex` (Left Leg):** if `i₂ : A → B₂` is `IsFlowConvex` in an
`AmalgamatedPosetSquare`, then its cobase-change `j₁ : B₁ → Q` is also `IsFlowConvex`. -/
theorem isFlowConvex_j₁ (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₂ : IsFlowConvex i₂) : IsFlowConvex j₁ := by
  have hi₂_refl := hi₂.toIsFlowReachReflecting
  refine IsFlowConvex.ofClosedEmbedding amalg.closed_j₁ ?_ ?_
  · intro x y w hxw hsx hyw hsy
    rcases amalg.toSetPushout.jointly_surj w with ⟨w₁, rfl⟩ | ⟨w₂, rfl⟩
    · exact ⟨w₁, rfl⟩
    · rcases amalg.closed_j₂.downward_closed hxw.1 with ⟨u₂, _, hu₂⟩
      rcases amalg.closed_j₂.downward_closed hyw.1 with ⟨v₂, _, hv₂⟩
      rcases amalg.toSetPushout.pullback_sap hu₂.symm with ⟨a, rfl, rfl⟩
      rcases amalg.toSetPushout.pullback_sap hv₂.symm with ⟨a', rfl, rfl⟩
      have hxw' : IsFacet (j₂ (i₂ a)) (j₂ w₂) := by rwa [← amalg.toSetPushout.comm a]
      have hyw' : IsFacet (j₂ (i₂ a')) (j₂ w₂) := by rwa [← amalg.toSetPushout.comm a']
      have hf_u₂ : IsFacet (i₂ a) w₂ := amalg.closed_j₂.map_isFacet_iff.mp hxw'
      have hf_v₂ : IsFacet (i₂ a') w₂ := amalg.closed_j₂.map_isFacet_iff.mp hyw'
      have hsu₂ : OrientedGradedPoset.sign (i₂ a) w₂ = false := by
        rw [← amalg.closed_j₂.map_sign hf_u₂, ← amalg.toSetPushout.comm a]
        exact hsx
      have hsv₂ : OrientedGradedPoset.sign (i₂ a') w₂ = true := by
        rw [← amalg.closed_j₂.map_sign hf_v₂, ← amalg.toSetPushout.comm a']
        exact hsy
      rcases hi₂.cell_mem hf_u₂ hsu₂ hf_v₂ hsv₂ with ⟨c, rfl⟩
      exact ⟨i₁ c, amalg.toSetPushout.comm c⟩
  · intro x y u hxu huy
    have hfrom := amalg.reachFromLeft_of_flowReach hi₂_refl hxu
    have hto := amalg.reachToLeft_of_flowReach hi₂_refl huy
    rcases hfrom with ⟨y₁, hy₁, _⟩ | ⟨_, a₁, u₂, _, _, hu₂, ha₁_u₂⟩
    · exact ⟨y₁, hy₁⟩
    · rcases hto with ⟨x₁, hx₁, _⟩ | ⟨_, a₂, u₂', _, _, hu₂', hu₂'_a₂⟩
      · exact ⟨x₁, hx₁⟩
      · have hu_eq : u₂' = u₂ := amalg.toSetPushout.inj_j₂ (hu₂'.trans hu₂.symm)
        subst hu_eq
        rcases hi₂.inter_mem ha₁_u₂ hu₂'_a₂ with ⟨c, rfl⟩
        exact ⟨i₁ c, (amalg.toSetPushout.comm c).trans hu₂⟩

/-- **Cobase-Change of `IsFlowConvex` (Right Leg):** if `i₁ : A → B₁` is `IsFlowConvex` in an
`AmalgamatedPosetSquare`, then its cobase-change `j₂ : B₂ → Q` is also `IsFlowConvex`. -/
theorem isFlowConvex_j₂ (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsFlowConvex i₁) : IsFlowConvex j₂ :=
  amalg.symm.isFlowConvex_j₁ hi₁

/-- **Flow-Acyclicity Preservation under `IsFlowConvex` Pushouts:** if both `B₁` and `B₂` are
`IsFlowAcyclic` and both legs `i₁, i₂` are `IsFlowConvex`, then `Q` is `IsFlowAcyclic`. -/
theorem isFlowAcyclic_of_flowConvex (amalg : AmalgamatedPosetSquare i₁ i₂ j₁ j₂)
    (hi₁ : IsFlowConvex i₁) (hi₂ : IsFlowConvex i₂)
    (hB₁ : IsFlowAcyclic B₁) (hB₂ : IsFlowAcyclic B₂) :
    IsFlowAcyclic Q :=
  amalg.isFlowAcyclic_of_flowReachReflecting
    hi₁.toIsFlowReachReflecting hi₂.toIsFlowReachReflecting hB₁ hB₂

end AmalgamatedPosetSquare

/-- **Headline `SAP` + Flow-Acyclicity Theorem for `IsFlowReachReflecting` Embeddings:**
Given `IsFlowReachReflecting` embeddings `i₁ : A → B₁` and `i₂ : A → B₂`, the amalgamated
quotient-free pushout `Q = CanonicalPushout i₁ i₂` satisfies Strong Amalgamation, principal-closure
order equivalence, cobase-change stability (`IsFlowReachReflecting j₁` and
`IsFlowReachReflecting j₂`), and **preserves `IsFlowAcyclic`**. -/
theorem sap_flowReachReflecting {A B₁ B₂ : Type*}
    [OrientedGradedPoset A] [OrientedGradedPoset B₁] [OrientedGradedPoset B₂]
    {i₁ : A → B₁} {i₂ : A → B₂}
    (hi₁ : IsFlowReachReflecting i₁) (hi₂ : IsFlowReachReflecting i₂) :
    letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
      canonicalPushoutOrientedGradedPoset hi₁.toIsClosedEmbedding hi₂.toIsClosedEmbedding
    let j₁ := CanonicalPushout.inl i₁ i₂
    let j₂ := CanonicalPushout.inr i₁ i₂
    IsFlowReachReflecting j₁ ∧
      IsFlowReachReflecting j₂ ∧
      (∀ b₁ : B₁, ∀ b₂ : B₂, j₁ b₁ = j₂ b₂ ↔ ∃ a : A, i₁ a = b₁ ∧ i₂ a = b₂) ∧
      (∀ b₁ : B₁, Nonempty (cl (j₁ b₁) ≃o cl b₁)) ∧
      (∀ b₂ : B₂, Nonempty (cl (j₂ b₂) ≃o cl b₂)) ∧
      (IsFlowAcyclic B₁ → IsFlowAcyclic B₂ → IsFlowAcyclic (CanonicalPushout i₁ i₂)) := by
  let hcl₁ := hi₁.toIsClosedEmbedding
  let hcl₂ := hi₂.toIsClosedEmbedding
  let sq := CanonicalPushout.setPushoutSquare hcl₁.injective hcl₂.injective
  letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
    canonicalPushoutOrientedGradedPoset hcl₁ hcl₂
  have amalg : AmalgamatedPosetSquare i₁ i₂
      (CanonicalPushout.inl i₁ i₂) (CanonicalPushout.inr i₁ i₂) :=
    pushout_amalgamatedPosetSquare sq hcl₁ hcl₂
  exact ⟨amalg.isFlowReachReflecting_j₁ hi₂, amalg.isFlowReachReflecting_j₂ hi₁,
    fun _ _ ↦ sq.eq_iff,
    fun b₁ ↦ ⟨amalg.closed_j₁.clOrderIso b₁⟩,
    fun b₂ ↦ ⟨amalg.closed_j₂.clOrderIso b₂⟩,
    fun hB₁ hB₂ ↦ amalg.isFlowAcyclic_of_flowReachReflecting hi₁ hi₂ hB₁ hB₂⟩

/-- **Headline `SAP` + Flow-Acyclicity Theorem for `IsFlowConvex` Embeddings:**
Given `IsFlowConvex` embeddings `i₁ : A → B₁` and `i₂ : A → B₂`, the amalgamated quotient-free
pushout `Q = CanonicalPushout i₁ i₂` satisfies Strong Amalgamation, principal-closure order
equivalence, cobase-change stability (`IsFlowConvex j₁` and `IsFlowConvex j₂`), and **preserves
`IsFlowAcyclic`**. -/
theorem sap_flowConvex {A B₁ B₂ : Type*}
    [OrientedGradedPoset A] [OrientedGradedPoset B₁] [OrientedGradedPoset B₂]
    {i₁ : A → B₁} {i₂ : A → B₂}
    (hi₁ : IsFlowConvex i₁) (hi₂ : IsFlowConvex i₂) :
    letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
      canonicalPushoutOrientedGradedPoset hi₁.toIsClosedEmbedding hi₂.toIsClosedEmbedding
    let j₁ := CanonicalPushout.inl i₁ i₂
    let j₂ := CanonicalPushout.inr i₁ i₂
    IsFlowConvex j₁ ∧
      IsFlowConvex j₂ ∧
      (∀ b₁ : B₁, ∀ b₂ : B₂, j₁ b₁ = j₂ b₂ ↔ ∃ a : A, i₁ a = b₁ ∧ i₂ a = b₂) ∧
      (∀ b₁ : B₁, Nonempty (cl (j₁ b₁) ≃o cl b₁)) ∧
      (∀ b₂ : B₂, Nonempty (cl (j₂ b₂) ≃o cl b₂)) ∧
      (IsFlowAcyclic B₁ → IsFlowAcyclic B₂ → IsFlowAcyclic (CanonicalPushout i₁ i₂)) := by
  let hcl₁ := hi₁.toIsClosedEmbedding
  let hcl₂ := hi₂.toIsClosedEmbedding
  let sq := CanonicalPushout.setPushoutSquare hcl₁.injective hcl₂.injective
  letI : OrientedGradedPoset (CanonicalPushout i₁ i₂) :=
    canonicalPushoutOrientedGradedPoset hcl₁ hcl₂
  have amalg : AmalgamatedPosetSquare i₁ i₂
      (CanonicalPushout.inl i₁ i₂) (CanonicalPushout.inr i₁ i₂) :=
    pushout_amalgamatedPosetSquare sq hcl₁ hcl₂
  exact ⟨amalg.isFlowConvex_j₁ hi₂, amalg.isFlowConvex_j₂ hi₁,
    fun _ _ ↦ sq.eq_iff,
    fun b₁ ↦ ⟨amalg.closed_j₁.clOrderIso b₁⟩,
    fun b₂ ↦ ⟨amalg.closed_j₂.clOrderIso b₂⟩,
    fun hB₁ hB₂ ↦ amalg.isFlowAcyclic_of_flowConvex hi₁ hi₂ hB₁ hB₂⟩

/-! ## Section 6: Mandatory 4-Layer Lean 4 Definition Check Gate (`namespace Checks`) -/

namespace Checks

/-! ### Layer 1: Inhabitation (Non-Degeneracy of Formalized Carriers) -/

/-- Layer 1 witness: `WalkingArrow` is `Nontrivial` (`.v0 ≠ .v1`). -/
instance instNontrivialWalkingArrow : Nontrivial WalkingArrow :=
  ⟨⟨.v0, .v1, by decide⟩⟩

/-- Explicit existential non-degeneracy witness on `WalkingArrow`. -/
theorem walkingArrow_exists_ne : ∃ x y : WalkingArrow, x ≠ y :=
  ⟨.v0, .v1, by decide⟩

/-- Layer 1 witness: the amalgamated pushout carrier `SteinerPushout` is `Nontrivial`. -/
instance instNontrivialSteinerPushout : Nontrivial SteinerPushout :=
  ⟨⟨CanonicalPushout.inl steinerLeft steinerRight .v0,
    CanonicalPushout.inl steinerLeft steinerRight .v1,
    fun h ↦ WalkingArrow.noConfusion (Sum.inl.inj h)⟩⟩

/-- Explicit existential non-degeneracy witness on `SteinerPushout`. -/
theorem steinerPushout_exists_ne : ∃ x y : SteinerPushout, x ≠ y :=
  exists_pair_ne SteinerPushout

/-! ### Layer 2: Bidirectional Separation of Core Predicates -/

/-- Single `1`-cell poset `TopCell` used to witness an injective grade- and sign-preserving
morphism (`TopCell → WalkingArrow`) that is **not** a closed cellular embedding. -/
inductive TopCell : Type
  | top
  deriving DecidableEq, Repr

instance instOrientedGradedPosetTopCell : OrientedGradedPoset TopCell where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  le_antisymm a b _ _ := by cases a; cases b; rfl
  dim _ := 1
  dim_strictMono _ _ h := False.elim (h.2 trivial)
  sign _ _ := false

/-- Inclusion of the bare `1`-cell `top ↦ .edge` without its `0`-dimensional boundary. -/
def topCellInclude : TopCell → WalkingArrow
  | .top => .edge

/-- `topCellInclude` is a valid `OrientedGradedPoset.Hom`. -/
def topCellIncludeHom : OrientedGradedPoset.Hom TopCell WalkingArrow where
  toFun := topCellInclude
  monotone' a b _ := by cases a; cases b; exact le_rfl
  map_dim' a := by cases a; rfl
  map_sign' a b h := by
    cases a
    cases b
    rcases h with ⟨_, hd⟩
    simp [OrientedGradedPoset.dim] at hd

/-- Layer 2 positive witness for `IsFlowAcyclic`: `WalkingArrow = (0 → 1)` is flow-acyclic. -/
theorem layer2_pos_isFlowAcyclic : IsFlowAcyclic WalkingArrow :=
  isFlowAcyclic_walkingArrow

/-- Layer 2 negative counter-witness for `IsFlowAcyclic`: `SteinerPushout = (0 ⇄ 1)` is NOT
flow-acyclic. -/
theorem layer2_neg_isFlowAcyclic : ¬ IsFlowAcyclic SteinerPushout :=
  steiner_cycle_obstruction.2.2.2.2.2.2.2

/-- Layer 2 positive witness for `IsClosedEmbedding`: `steinerLeft : TwoPt → WalkingArrow`. -/
theorem layer2_pos_isClosedEmbedding : IsClosedEmbedding steinerLeft :=
  isClosedEmbedding_steinerLeft

/-- Layer 2 negative counter-witness for `IsClosedEmbedding`: `topCellInclude` is NOT a closed
embedding because `.v0 ≤ .edge` has no preimage in `TopCell`. -/
theorem layer2_neg_isClosedEmbedding : ¬ IsClosedEmbedding topCellInclude := by
  intro hcl
  have hle : (WalkingArrow.v0 : WalkingArrow) ≤ topCellInclude .top := rfl
  rcases hcl.downward_closed hle with ⟨a, _, ha⟩
  cases a
  cases ha

/-- **Strict Separation 1 (`IsClosedEmbedding ∧ ¬ IsFlowReachReflecting`):**
`steinerLeft : {0, 1} ↪ (0 → 1)` is a closed cellular embedding, yet fails `IsFlowReachReflecting`
because `0 → 1` is reachable in `WalkingArrow` (`via .edge`) while `TwoPt` has no flow steps. -/
theorem layer2_sep_closed_not_flowReachReflecting :
    IsClosedEmbedding steinerLeft ∧ ¬ IsFlowReachReflecting steinerLeft := by
  refine ⟨isClosedEmbedding_steinerLeft, fun hrefl ↦ ?_⟩
  have hreachQ : FlowReach (steinerLeft .v0) (steinerLeft .v1) :=
    walkingArrow_flowReach_iff.mpr ⟨rfl, rfl⟩
  have hreachA : FlowReach (TwoPt.v0) (TwoPt.v1) := hrefl.reflect_flowReach hreachQ
  cases hreachA with
  | single hs =>
    rcases hs with ⟨_, ⟨_, hd⟩, _, _, _⟩
    simp at hd
  | tail _ hs =>
    rcases hs with ⟨_, ⟨_, hd⟩, _, _, _⟩
    simp at hd

/-- Directed graph `(0 → 1)` union an external directed 2-path `0 → m → 1`, strictly separating
`IsFlowReachReflecting` from `IsFlowConvex`. -/
inductive BypassPoset : Type
  | v0
  | v1
  | vm
  | e01
  | e0m
  | em1
  deriving DecidableEq, Repr

/-- Decidable partial order test on `BypassPoset`. -/
def bypassLEBool : BypassPoset → BypassPoset → Bool
  | .v0, .v0 | .v1, .v1 | .vm, .vm => true
  | .e01, .e01 | .e0m, .e0m | .em1, .em1 => true
  | .v0, .e01 | .v1, .e01 => true
  | .v0, .e0m | .vm, .e0m => true
  | .vm, .em1 | .v1, .em1 => true
  | _, _ => false

/-- Dimension grading on `BypassPoset`. -/
def bypassDim : BypassPoset → ℕ
  | .v0 | .v1 | .vm => 0
  | .e01 | .e0m | .em1 => 1

/-- Coface orientation sign on `BypassPoset` (`0 → 1`, `0 → m`, `m → 1`). -/
def bypassSign : BypassPoset → BypassPoset → Bool
  | .v0, .e01 => false
  | .v1, .e01 => true
  | .v0, .e0m => false
  | .vm, .e0m => true
  | .vm, .em1 => false
  | .v1, .em1 => true
  | _, _ => false

instance instOrientedGradedPosetBypassPoset : OrientedGradedPoset BypassPoset where
  le x y := bypassLEBool x y = true
  le_refl x := by cases x <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide
  dim := bypassDim
  dim_strictMono a b h := by
    rcases h with ⟨hab, hba⟩
    cases a <;> cases b <;> simp_all [bypassLEBool, bypassDim]
  sign := bypassSign

instance : DecidableLE BypassPoset :=
  fun a b ↦ inferInstanceAs (Decidable (bypassLEBool a b = true))

/-- Exact characterization of `FlowStep` in `BypassPoset`. -/
theorem bypass_flowStep_iff {x y : BypassPoset} :
    FlowStep x y ↔
      (x = .v0 ∧ y = .v1) ∨ (x = .v0 ∧ y = .vm) ∨ (x = .vm ∧ y = .v1) := by
  constructor
  · rintro ⟨w, ⟨hxle, hxdim⟩, hxs, ⟨hyle, hydim⟩, hys⟩
    cases x <;> cases y <;> cases w <;>
      revert hxle hxdim hxs hyle hydim hys <;> decide
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨.e01, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨.e0m, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨.em1, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩

/-- Upper bound on `FlowReach` in `BypassPoset`. -/
theorem bypass_flowReach_cases {x y : BypassPoset} (h : FlowReach x y) :
    (x = .v0 ∧ y = .v1) ∨ (x = .v0 ∧ y = .vm) ∨ (x = .vm ∧ y = .v1) := by
  induction h with
  | single hs => exact bypass_flowStep_iff.mp hs
  | tail _ hs ih =>
    have hs' := bypass_flowStep_iff.mp hs
    rcases ih with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hs' with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩ <;> cases hb
    · rcases hs' with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨_, rfl⟩
      · cases hb
      · cases hb
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases hs' with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩ <;> cases hb

/-- Closed embedding of the direct arrow `(0 → 1)` into `BypassPoset = (0 → 1) ∪ (0 → m → 1)`. -/
def bypassEmbed : WalkingArrow → BypassPoset
  | .v0 => .v0
  | .v1 => .v1
  | .edge => .e01

/-- `bypassEmbed` is a closed cellular embedding. -/
theorem isClosedEmbedding_bypassEmbed : IsClosedEmbedding bypassEmbed where
  mono a b h := by cases a <;> cases b <;> revert h <;> decide
  injective a b h := by cases a <;> cases b <;> cases h <;> rfl
  downward_closed x q hq := by
    cases x with
    | v0 =>
      cases q with
      | v0 => exact ⟨.v0, le_rfl, rfl⟩
      | v1 | vm | e01 | e0m | em1 => exact absurd hq (by decide)
    | v1 =>
      cases q with
      | v1 => exact ⟨.v1, le_rfl, rfl⟩
      | v0 | vm | e01 | e0m | em1 => exact absurd hq (by decide)
    | edge =>
      cases q with
      | v0 => exact ⟨.v0, rfl, rfl⟩
      | v1 => exact ⟨.v1, rfl, rfl⟩
      | e01 => exact ⟨.edge, rfl, rfl⟩
      | vm | e0m | em1 => exact absurd hq (by decide)
  map_dim a := by cases a <;> rfl
  map_sign a b h := by
    rcases h with ⟨hle, hd⟩
    cases a <;> cases b <;> revert hle hd <;> decide

/-- **Strict Separation 2 (`IsFlowReachReflecting ∧ ¬ IsFlowConvex`):**
`bypassEmbed : (0 → 1) ↪ (0 → 1) ∪ (0 → m → 1)` is `IsFlowReachReflecting` (because `0 → 1` is
already reachable inside `WalkingArrow`), yet fails `IsFlowConvex` because the external vertex `vm`
lies on the directed 2-path `bypassEmbed .v0 = .v0 → .vm → .v1 = bypassEmbed .v1` outside
`Set.range bypassEmbed`. -/
theorem layer2_sep_flowReachReflecting_not_flowConvex :
    IsFlowReachReflecting bypassEmbed ∧ ¬ IsFlowConvex bypassEmbed := by
  refine ⟨IsFlowReachReflecting.ofClosedEmbedding isClosedEmbedding_bypassEmbed ?_, ?_⟩
  · intro a b hreach
    rcases bypass_flowReach_cases hreach with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ha' : a = .v0 := by cases a <;> revert ha <;> decide
      have hb' : b = .v1 := by cases b <;> revert hb <;> decide
      subst ha' hb'
      exact walkingArrow_flowReach_iff.mpr ⟨rfl, rfl⟩
    · exfalso
      revert hb
      cases b <;> decide
    · exfalso
      revert ha
      cases a <;> decide
  · intro hconv
    have h0m : FlowReach (bypassEmbed .v0) .vm :=
      .single (bypass_flowStep_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    have hm1 : FlowReach .vm (bypassEmbed .v1) :=
      .single (bypass_flowStep_iff.mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    rcases hconv.inter_mem h0m hm1 with ⟨a, ha⟩
    revert ha
    cases a <;> decide

/-- Directed composable 2-spine `0 → 1 → 2` furnishing a non-trivial proper `IsFlowConvex`
embedding `(0 → 1) ↪ (0 → 1 → 2)`. -/
inductive ComposablePair : Type
  | v0
  | v1
  | v2
  | e01
  | e12
  deriving DecidableEq, Repr

/-- Decidable partial order test on `ComposablePair`. -/
def composableLEBool : ComposablePair → ComposablePair → Bool
  | .v0, .v0 | .v1, .v1 | .v2, .v2 => true
  | .e01, .e01 | .e12, .e12 => true
  | .v0, .e01 | .v1, .e01 => true
  | .v1, .e12 | .v2, .e12 => true
  | _, _ => false

/-- Dimension grading on `ComposablePair`. -/
def composableDim : ComposablePair → ℕ
  | .v0 | .v1 | .v2 => 0
  | .e01 | .e12 => 1

/-- Coface orientation sign on `ComposablePair` (`0 → 1 → 2`). -/
def composableSign : ComposablePair → ComposablePair → Bool
  | .v0, .e01 => false
  | .v1, .e01 => true
  | .v1, .e12 => false
  | .v2, .e12 => true
  | _, _ => false

instance instOrientedGradedPosetComposablePair : OrientedGradedPoset ComposablePair where
  le x y := composableLEBool x y = true
  le_refl x := by cases x <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide
  dim := composableDim
  dim_strictMono a b h := by
    rcases h with ⟨hab, hba⟩
    cases a <;> cases b <;> simp_all [composableLEBool, composableDim]
  sign := composableSign

instance : DecidableLE ComposablePair :=
  fun a b ↦ inferInstanceAs (Decidable (composableLEBool a b = true))

/-- Exact characterization of `FlowStep` in `ComposablePair`. -/
theorem composable_flowStep_iff {x y : ComposablePair} :
    FlowStep x y ↔ (x = .v0 ∧ y = .v1) ∨ (x = .v1 ∧ y = .v2) := by
  constructor
  · rintro ⟨w, ⟨hxle, hxdim⟩, hxs, ⟨hyle, hydim⟩, hys⟩
    cases x <;> cases y <;> cases w <;>
      revert hxle hxdim hxs hyle hydim hys <;> decide
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨.e01, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨.e12, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩

/-- Upper bound on `FlowReach` in `ComposablePair`. -/
theorem composable_flowReach_cases {x y : ComposablePair} (h : FlowReach x y) :
    (x = .v0 ∧ y = .v1) ∨ (x = .v1 ∧ y = .v2) ∨ (x = .v0 ∧ y = .v2) := by
  induction h with
  | single hs =>
    rcases composable_flowStep_iff.mp hs with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  | tail _ hs ih =>
    have hs' := composable_flowStep_iff.mp hs
    rcases ih with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hs' with ⟨hb, _⟩ | ⟨_, rfl⟩
      · cases hb
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · rcases hs' with ⟨hb, _⟩ | ⟨hb, _⟩ <;> cases hb
    · rcases hs' with ⟨hb, _⟩ | ⟨hb, _⟩ <;> cases hb

/-- Inclusion of the first edge `(0 → 1) ↪ (0 → 1 → 2)`. -/
def composableFirstEdge : WalkingArrow → ComposablePair
  | .v0 => .v0
  | .v1 => .v1
  | .edge => .e01

/-- `composableFirstEdge` is a closed cellular embedding. -/
theorem isClosedEmbedding_composableFirstEdge : IsClosedEmbedding composableFirstEdge where
  mono a b h := by cases a <;> cases b <;> revert h <;> decide
  injective a b h := by cases a <;> cases b <;> cases h <;> rfl
  downward_closed x q hq := by
    cases x with
    | v0 =>
      cases q with
      | v0 => exact ⟨.v0, le_rfl, rfl⟩
      | v1 | v2 | e01 | e12 => exact absurd hq (by decide)
    | v1 =>
      cases q with
      | v1 => exact ⟨.v1, le_rfl, rfl⟩
      | v0 | v2 | e01 | e12 => exact absurd hq (by decide)
    | edge =>
      cases q with
      | v0 => exact ⟨.v0, rfl, rfl⟩
      | v1 => exact ⟨.v1, rfl, rfl⟩
      | e01 => exact ⟨.edge, rfl, rfl⟩
      | v2 | e12 => exact absurd hq (by decide)
  map_dim a := by cases a <;> rfl
  map_sign a b h := by
    rcases h with ⟨hle, hd⟩
    cases a <;> cases b <;> revert hle hd <;> decide

/-- **Non-Trivial Positive `IsFlowConvex` Witness:** `composableFirstEdge : (0 → 1) ↪ (0 → 1 → 2)`
is `IsFlowConvex` and strictly non-surjective (`.v2 ∉ Set.range composableFirstEdge`). -/
theorem layer2_pos_isFlowConvex_nontrivial :
    IsFlowConvex composableFirstEdge ∧ ¬ Function.Surjective composableFirstEdge := by
  refine ⟨IsFlowConvex.ofClosedEmbedding isClosedEmbedding_composableFirstEdge ?_ ?_, ?_⟩
  · intro x y w hxw hsx hyw hsy
    rcases hxw with ⟨hxle, hxdim⟩
    rcases hyw with ⟨hyle, hydim⟩
    have hw : w = .e01 := by
      cases x <;> cases y <;> cases w <;>
        revert hxle hxdim hsx hyle hydim hsy <;> decide
    exact ⟨.edge, hw.symm⟩
  · intro x y u hxu huy
    rcases composable_flowReach_cases huy with ⟨hu, _⟩ | ⟨_, hy⟩ | ⟨_, hy⟩
    · subst hu
      rcases composable_flowReach_cases hxu with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    · exfalso
      revert hy
      cases y <;> decide
    · exfalso
      revert hy
      cases y <;> decide
  · intro hsurj
    rcases hsurj .v2 with ⟨a, ha⟩
    revert ha
    cases a <;> decide

/-! ### Layer 3: Projection & Derived Sanity (Stock Mathlib Projections & Boundary Lemmas) -/

/-- Layer 3 stock `PartialOrder` projection check on `WalkingArrow`. -/
def walkingArrowPartialOrderCheck : PartialOrder WalkingArrow := inferInstance

/-- Layer 3 stock `OrderEmbedding` (`↪o`) projection check on `steinerLeft`. -/
def steinerLeftOrderEmbeddingCheck : TwoPt ↪o WalkingArrow :=
  isClosedEmbedding_steinerLeft.toOrderEmbedding

/-- Layer 3 stock `OrderIso` (`≃o`) principal-closure equivalence check on `steinerLeft`. -/
noncomputable def steinerLeftClosureOrderIsoCheck (x : TwoPt) :
    cl (steinerLeft x) ≃o cl x :=
  isClosedEmbedding_steinerLeft.clOrderIso x

/-- Derived boundary sanity check 1: strict 2-step hierarchy chain
`IsFlowConvex → IsFlowReachReflecting → IsClosedEmbedding` (both arrows proved as derived lemmas,
not assumed as structure fields). -/
theorem derived_hierarchy_chain {P Q : Type*} [OrientedGradedPoset P] [OrientedGradedPoset Q]
    {f : P → Q} (hf : IsFlowConvex f) :
    IsFlowReachReflecting f ∧ IsClosedEmbedding f :=
  ⟨hf.toIsFlowReachReflecting, hf.toIsFlowReachReflecting.toIsClosedEmbedding⟩

/-- Derived boundary sanity check 2: composition closure of `IsClosedEmbedding`,
`IsFlowReachReflecting`, and `IsFlowConvex`. -/
theorem derived_composition_closure {P Q R : Type*}
    [OrientedGradedPoset P] [OrientedGradedPoset Q] [OrientedGradedPoset R]
    {f : P → Q} {g : Q → R} :
    (IsClosedEmbedding g → IsClosedEmbedding f → IsClosedEmbedding (g ∘ f)) ∧
      (IsFlowReachReflecting g → IsFlowReachReflecting f → IsFlowReachReflecting (g ∘ f)) ∧
      (IsFlowConvex g → IsFlowConvex f → IsFlowConvex (g ∘ f)) :=
  ⟨IsClosedEmbedding.comp, IsFlowReachReflecting.comp, IsFlowConvex.comp⟩

/-- Derived boundary sanity check 3: every `FlowReach` path preserves dimension (`dim x = dim y`).
-/
theorem derived_flowReach_dim_eq {P : Type*} [OrientedGradedPoset P] {x y : P}
    (h : FlowReach x y) : OrientedGradedPoset.dim x = OrientedGradedPoset.dim y :=
  h.dim_eq

/-! ### Layer 4: Kernel Axiom Gate (`#guard_msgs in #print axioms`) -/

section KernelAxiomGate

set_option linter.hashCommand false

/-- info: 'HomotopyCRM.CanonicalPushout.setPushoutSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.CanonicalPushout.setPushoutSquare

/-- info: 'HomotopyCRM.sap_closed_oriented_poset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.sap_closed_oriented_poset

/-- info: 'HomotopyCRM.steiner_cycle_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.steiner_cycle_obstruction

/-- info: 'HomotopyCRM.IsFlowReachReflecting.toIsClosedEmbedding' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.IsFlowReachReflecting.toIsClosedEmbedding

/-- info: 'HomotopyCRM.IsFlowConvex.toIsFlowReachReflecting' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.IsFlowConvex.toIsFlowReachReflecting

/-- info: 'HomotopyCRM.sap_flowReachReflecting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.sap_flowReachReflecting

/-- info: 'HomotopyCRM.sap_flowConvex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.sap_flowConvex

/-- info: 'HomotopyCRM.Checks.layer2_pos_isFlowAcyclic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_pos_isFlowAcyclic

/-- info: 'HomotopyCRM.Checks.layer2_neg_isFlowAcyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_neg_isFlowAcyclic

/-- info: 'HomotopyCRM.Checks.layer2_neg_isClosedEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_neg_isClosedEmbedding

/-- info: 'HomotopyCRM.Checks.layer2_sep_closed_not_flowReachReflecting' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_closed_not_flowReachReflecting

/-- info: 'HomotopyCRM.Checks.layer2_sep_flowReachReflecting_not_flowConvex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_flowReachReflecting_not_flowConvex

/-- info: 'HomotopyCRM.Checks.layer2_pos_isFlowConvex_nontrivial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_pos_isFlowConvex_nontrivial

end KernelAxiomGate

end Checks

end HomotopyCRM
