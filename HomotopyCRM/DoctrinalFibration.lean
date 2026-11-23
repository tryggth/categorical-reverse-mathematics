/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HomotopyCRM Formalization Team
-/
import HomotopyCRM.Basic
import HomotopyCRM.BorelTailResiduum
import HomotopyCRM.CubicalAmalgamation
import HomotopyCRM.DeltaRingPerfection
import HomotopyCRM.DirectedFraisseSAP
import HomotopyCRM.InfinityResiduum
import HomotopyCRM.NominalICaTT
import HomotopyCRM.NominalSimplicity
import HomotopyCRM.OrdinalRankCompleteness
import HomotopyCRM.SetsResiduum
import HomotopyCRM.StepProductPhantom
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Doctrinal Fibrations, Tri-Modal Obstructions, and the Formal Philosophy `𝔓 = (𝔻, 𝒫)`

This root module formalizes the unifying architectural backbone of *Categorical Reverse Mathematics*
(Waves 47A & R2):

1. **Master Square `Def(α)` & Tri-Modal Factorization Core (`Section 1`):**
   - `DoctrinalFibration` wrapping stock `Mathlib` fibered categories (`Functor.IsFibered`) and
     fiber categories (`Functor.Fiber`), and `MateDoubleSquare` wrapping `CategoryTheory.TwoSquare`,
     `mateEquiv`, and `conjugateIsoEquiv`.
   - Three derived obstruction modes:
     - **Mode (i) (`SectionObstructionMode`):** `(-1)`-connected section inhabitation strictly
       separated from `(-2)`-contractibility via `ℤ → ZMod 2` in `Type` vs. `AddCommGrpCat`.
     - **Mode (ii) (`TowerPhantomMode`):** Completion/tower phantom gaps registering
       `ProfiniteLasso` and `StepState.qFull` (`StepProductQ`) Postnikov phantoms.
     - **Mode (iii) (`ForgetfulLiftMode`):** Homotopy-fiber lift spaces and symmetry orbit quotients
       over fixed base objects.

2. **Formal `DoctrinalPhilosophy` `𝔓 = (𝔻, 𝒫)` & Finite Pareto Schism (`Section 2`):**
   - Defines `DoctrinalPhilosophy`, Galois/Moore closure (`ClosureOperator`), and minimal Pareto
     frontiers `paretoFrontier`.
   - Proves the **Inquisitor's Impossibility Lemma (`inquisitor_impossibility_casuistry`)** via
     `S4` interiors `s4Interior`, demonstrating why purely apophatic product/closure axioms collapse
     and kataphatic probe suites `𝒫` are mathematically necessary.
   - Defines genuine uniform presheaf predicates (`CatPresheafAC`, `CatPresheafIAC`,
     `CatPresheafProjSub`, `CatPresheafProj1`, `CatPresheafLocalic`) over any small category `C`
     using Choice-free `NatTrans` and `coyonedaPresheaf` combinators, and certifies the **Finite
     Pareto Schism (`pareto_incomparable_projSub_localic`)** comparing `IAC ∩ · ⊆ AC` across
     `PUnitCat`, `TwoGroupCat`, `M1Cat`, and `VPosetOpCat` (with `Classical.choice` confined to
     positive `Set ⊨ AC`, `Set^{ℤ/2ℤ} ⊨ IAC`, and `ℳ₁ ⊨ ProjSub` witnesses over `Type`, while all
     finite negative witnesses and `freydCover_dogma_banishment` on the genuine 2-object Freyd cover
     `(B(ℤ/2ℤ))_⊥` (`BZ2BotObj`) remain Choice-free):
     - `monoid_proj1_iff_rightZero` and `m1_projSub_and_not_localic` on `M1Monoid`
       (`ℳ₁ = ({e₁, 1₁}, ∧) ≃* AbsorbingMonoidCarrier 1`),
     - `vPoset_localic_not_proj1` on the 3-element V-poset `VPoset = {a > c < b}`,
     - `diamond_proj1_not_projSub` on the 4-element diamond poset `DiamondPoset`,
     - `freydCover_dogma_banishment` on the 2-object category `BZ2BotObj = (B(ℤ/2ℤ))_⊥`, and
     - **Lawvere–Tierney topology enumeration (`m1_slice_lt_count`):** `3^k * 2^m` total slice
       topologies splitting into `2^(k + m)` localic and `(3^k - 2^k) * 2^m` non-localic /
       non-Boolean topologies.

3. **Mode (iii) 2-Stage `δ`-Ring Tower (`FrobLiftRing2`) & Leray Transgression (`Section 3`):**
   - `FrobLiftRing2` (`(R, φ)` satisfying `φ(x) - x² ∈ 2R`) and `DeltaLift F`:
     - Stage-1 empty fibers over genuine `FrobLiftRing2` instances: `(ZMod 2, id)`
       (`empty_deltaLift_zmod2`), `(ZMod 4, id)` (`empty_deltaLift_zmod4`), and `(R2IdempRing, id)`
       (`empty_deltaLift_R2Idemp`).
     - Stage-2 torsor lift counts & orbit quotients: `r2_lift_card_eq_two`, `r2_lifts_non_iso`,
       `r22_lift_card_eq_sixteen`, and `r22_iso_orbits_eq_six` (`GL₂(𝔽₂)` conjugation orbits on
       `M₂(𝔽₂)`).
   - Finite group-cohomology Leray transgression witness (`sl2_f5_leray_transgression_injective`) on
     `1 → {±1} → SL(2, ZMod 5) → PSL(2, ZMod 5) → 1`.

4. **Cross-Module Witness Registration & Mandatory 4-Layer Checks (`Sections 4–5`):**
   - Clean tri-modal adapters across all existing `HomotopyCRM` witness modules (`InfinityResiduum`,
     `DeltaRingPerfection`, `BorelTailResiduum`, `StepProductPhantom`, `NominalSimplicity`,
     `CubicalAmalgamation`, `NominalICaTT`, `OrdinalRankCompleteness`, `SetsResiduum`).
   - Mandatory 4-Layer check gate (`namespace Checks`) with `30+` `#guard_msgs in #print axioms`
     checks, zero `sorry`, zero custom `axiom`, zero `opaque`.
-/

namespace HomotopyCRM

open CategoryTheory

universe u v u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

/-! ## Section 1: Master Square, `DoctrinalFibration`, `MateDoubleSquare`, & Tri-Modal Core -/

/-- A doctrinal fibration `(E --proj--> B)` wrapping stock Mathlib `Functor.IsFibered`, whose
vertical fibers `proj.Fiber b` carry canonical category structures. -/
structure DoctrinalFibration (E : Type u₁) [Category.{v₁} E]
    (B : Type u₂) [Category.{v₂} B] where
  /-- Projection functor from the richer/total doctrine `E` to the weaker/base doctrine `B`. -/
  proj : E ⥤ B
  /-- Grothendieck / Cartmell fibration witness enabling Cartesian pullback transport. -/
  [isFibered : proj.IsFibered]

attribute [instance] DoctrinalFibration.isFibered

namespace DoctrinalFibration

/-- The vertical fiber category over a base object `b : B` in a `DoctrinalFibration`. -/
abbrev fiber {E : Type u₁} [Category.{v₁} E] {B : Type u₂} [Category.{v₂} B]
    (F : DoctrinalFibration E B) (b : B) : Type u₁ :=
  F.proj.Fiber b

/-- Trivial identity fibration `B --id--> B` over any category `B`. -/
def id (B : Type u) [Category.{v} B] : DoctrinalFibration B B where
  proj := 𝟭 B
  isFibered := Functor.IsFibered.of_exists_isStronglyCartesian fun a R f ↦ by
    refine ⟨R, f, { toIsHomLift := .map f, universal_property' := fun g φ' hφ' ↦ ?_ }⟩
    have hEq : g ≫ f = φ' := IsHomLift.eq_of_isHomLift (𝟭 B) (g ≫ f) φ'
    refine ⟨g, ⟨.map g, hEq⟩, fun χ ⟨hχ, _⟩ ↦ (IsHomLift.eq_of_isHomLift (𝟭 B) g χ).symm⟩

end DoctrinalFibration

/-- Master comparison square `Def(α)` wrapping Mathlib's `CategoryTheory.TwoSquare` together with
top/bottom adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, inducing the canonical Beck–Chevalley mate square
`mateEquiv adjTop adjBot alpha`. -/
structure MateDoubleSquare
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    (G : C ⥤ E) (H : D ⥤ F)
    (L₁ : C ⥤ D) (R₁ : D ⥤ C)
    (L₂ : E ⥤ F) (R₂ : F ⥤ E) : Type (max u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄) where
  /-- Top horizontal adjunction `L₁ ⊣ R₁`. -/
  adjTop : L₁ ⊣ R₁
  /-- Bottom horizontal adjunction `L₂ ⊣ R₂`. -/
  adjBot : L₂ ⊣ R₂
  /-- Primary doctrinal comparison 2-cell `G ⋙ L₂ ⟶ L₁ ⋙ H`. -/
  alpha : CategoryTheory.TwoSquare G L₁ L₂ H

namespace MateDoubleSquare

/-- The canonical Beck–Chevalley mate 2-cell `R₁ ⋙ G ⟶ H ⋙ R₂` produced by
`CategoryTheory.mateEquiv`. -/
def beckChevalleyMate
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (S : MateDoubleSquare G H L₁ R₁ L₂ R₂) :
    CategoryTheory.TwoSquare R₁ H G R₂ :=
  CategoryTheory.mateEquiv S.adjTop S.adjBot S.alpha

/-- Beck–Chevalley exactness predicate: the mate 2-cell is a natural isomorphism. -/
def IsBeckChevalley
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (S : MateDoubleSquare G H L₁ R₁ L₂ R₂) : Prop :=
  IsIso S.beckChevalleyMate.natTrans

/-- The exactness locus on objects of `D` where the Beck–Chevalley mate component is invertible. -/
def beckChevalleyLocus
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (S : MateDoubleSquare G H L₁ R₁ L₂ R₂) : Set D :=
  { X : D | IsIso (S.beckChevalleyMate.natTrans.app X) }

/-- Morphism-property defect class of morphisms `f : X ⟶ Y` in `D` whose source and target
Beck–Chevalley mate components `(S.beckChevalleyMate.natTrans.app X)` and
`(S.beckChevalleyMate.natTrans.app Y)` are isomorphisms. Equaling `⊤` coincides with global
Beck–Chevalley exactness (`S.IsBeckChevalley`). -/
def defectMorphismProperty
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (S : MateDoubleSquare G H L₁ R₁ L₂ R₂) : CategoryTheory.MorphismProperty D :=
  fun {X Y} _f ↦
    IsIso (S.beckChevalleyMate.natTrans.app X) ∧ IsIso (S.beckChevalleyMate.natTrans.app Y)

/-- Global Beck–Chevalley exactness holds iff every morphism `f` in `D` lies in
`S.defectMorphismProperty`. -/
theorem isBeckChevalley_iff_defectMorphismProperty_all
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (S : MateDoubleSquare G H L₁ R₁ L₂ R₂) :
    S.IsBeckChevalley ↔ ∀ {X Y : D} (f : X ⟶ Y), S.defectMorphismProperty f := by
  rw [IsBeckChevalley, CategoryTheory.NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h _ _ _ ↦ ⟨h _, h _⟩, fun h X ↦ (h (𝟙 X)).1⟩

end MateDoubleSquare

/-- Mate involution symmetry: passing twice across `mateEquiv adjTop adjBot` recovers `S.alpha`. -/
theorem mateDoubleSquare_mate_involutive
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (S : MateDoubleSquare G H L₁ R₁ L₂ R₂) :
    (CategoryTheory.mateEquiv S.adjTop S.adjBot).symm S.beckChevalleyMate = S.alpha :=
  (CategoryTheory.mateEquiv S.adjTop S.adjBot).symm_apply_apply S.alpha

/-- Stock conjugate-isomorphism equivalence `(L₂ ≅ L₁) ≃ (R₁ ≅ R₂)` wrapping
`CategoryTheory.conjugateIsoEquiv`. -/
def conjugateIsoEquiv_bridge
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) :
    (L₂ ≅ L₁) ≃ (R₁ ≅ R₂) :=
  CategoryTheory.conjugateIsoEquiv adj₁ adj₂

/-! ### Tri-Modal Factorization: Mode (i) Section Obstruction -/

/-- **Mode (i) (`SectionObstructionMode`):** Horizontal section problem `s ≫ proj = 𝟙 base`
for a morphism `proj : total ⟶ base` in a category `C`. -/
structure SectionObstructionMode (C : Type u) [Category.{v} C] where
  /-- Total object covering `base`. -/
  total : C
  /-- Base object to be sectioned. -/
  base : C
  /-- Canonical projection epimorphism/fibration leg `total ⟶ base`. -/
  proj : total ⟶ base

namespace SectionObstructionMode

/-- The type of global sections `{ s : base ⟶ total // s ≫ proj = 𝟙 base }`. -/
def SectionSpace {C : Type u} [Category.{v} C] (M : SectionObstructionMode C) : Type v :=
  { s : M.base ⟶ M.total // s ≫ M.proj = 𝟙 M.base }

/-- `(-1)`-connected section inhabitation (`∃` section). -/
def IsSectionInhabited {C : Type u} [Category.{v} C] (M : SectionObstructionMode C) : Prop :=
  Nonempty M.SectionSpace

/-- `(-2)`-contractibility (`∃!` section). -/
def IsSectionContractible {C : Type u} [Category.{v} C] (M : SectionObstructionMode C) : Prop :=
  Nonempty M.SectionSpace ∧ Subsingleton M.SectionSpace

end SectionObstructionMode

/-- Quotient reduction `ℤ → ZMod 2` viewed in `Type 0`. -/
def intToZMod2TypeMode : SectionObstructionMode (Type 0) where
  total := ℤ
  base := ZMod 2
  proj := fun z ↦ (z : ZMod 2)

/-- Quotient reduction `ℤ → ZMod 2` viewed in the abelian category `AddCommGrpCat.{0}`. -/
def intToZMod2AbMode : SectionObstructionMode AddCommGrpCat.{0} where
  total := AddCommGrpCat.of ℤ
  base := AddCommGrpCat.of (ZMod 2)
  proj := AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))

private def zmod2ToIntLiftZero : ZMod 2 → ℤ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1

private def zmod2ToIntLiftThree : ZMod 2 → ℤ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 3

private lemma zmod2_three_eq_one : ((3 : ℤ) : ZMod 2) = 1 := by decide

/-- In `Type 0`, `ℤ → ZMod 2` admits at least two distinct sections (`1 ↦ 1` vs. `1 ↦ 3`),
making its section space both inhabited and non-contractible (`Nontrivial`). -/
theorem intToZMod2TypeMode_sectionSpace_nontrivial :
    Nontrivial intToZMod2TypeMode.SectionSpace := by
  let s₀ : intToZMod2TypeMode.SectionSpace :=
    ⟨zmod2ToIntLiftZero, funext fun x ↦ match x with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl⟩
  let s₁ : intToZMod2TypeMode.SectionSpace :=
    ⟨zmod2ToIntLiftThree, funext fun x ↦ match x with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => zmod2_three_eq_one⟩
  refine ⟨⟨s₀, s₁, fun h ↦ ?_⟩⟩
  have hv := congrArg (fun s : ZMod 2 → ℤ ↦ s 1) (congrArg Subtype.val h)
  change (1 : ℤ) = 3 at hv
  exact absurd hv (by decide)

/-- In `Type 0`, `ℤ → ZMod 2` is `(-1)`-inhabited (`IsSectionInhabited`). -/
theorem intToZMod2TypeMode_inhabited : intToZMod2TypeMode.IsSectionInhabited :=
  have ⟨x, _, _⟩ := intToZMod2TypeMode_sectionSpace_nontrivial
  ⟨x⟩

/-- In `Type 0`, `ℤ → ZMod 2` fails `(-2)`-contractibility (`¬ IsSectionContractible`),
separating `(-1)`-connectedness from unique splitting. -/
theorem not_intToZMod2TypeMode_contractible : ¬ intToZMod2TypeMode.IsSectionContractible := by
  rintro ⟨_, hsub⟩
  rcases intToZMod2TypeMode_sectionSpace_nontrivial with ⟨a, b, hne⟩
  exact hne (Subsingleton.elim a b)

/-- In `AddCommGrpCat`, `ℤ → ZMod 2` has **empty** section space because `ZMod 2` is
`2`-torsion while `ℤ` is torsion-free. -/
theorem isEmpty_intToZMod2AbMode_sectionSpace : IsEmpty intToZMod2AbMode.SectionSpace := by
  refine ⟨fun ⟨s, hs⟩ ↦ ?_⟩
  let x : ℤ := s.hom (1 : ZMod 2)
  have hx2 : x + x = 0 := by
    change s.hom (1 : ZMod 2) + s.hom (1 : ZMod 2) = 0
    rw [← map_add, show (1 : ZMod 2) + 1 = 0 by decide, map_zero]
  have hx0 : x = 0 := by omega
  have happ := congrArg (fun f : intToZMod2AbMode.base ⟶ intToZMod2AbMode.base ↦
    f.hom (1 : ZMod 2)) hs
  have hcast : (x : ZMod 2) = (1 : ZMod 2) := happ
  rw [hx0, Int.cast_zero] at hcast
  exact absurd hcast (by decide)

/-- In `AddCommGrpCat`, `ℤ → ZMod 2` is **not** section-inhabited. -/
theorem not_intToZMod2AbMode_inhabited : ¬ intToZMod2AbMode.IsSectionInhabited :=
  fun ⟨s⟩ ↦ isEmpty_intToZMod2AbMode_sectionSpace.false s

/-! ### Tri-Modal Factorization: Mode (ii) Completion / Tower Phantom Mode -/

/-- **Mode (ii) (`TowerPhantomMode`):** Completion/tower phantom problem comparing `source` along
`comparison : source → target`; an element outside `Set.range comparison` is a phantom tower
defect. -/
structure TowerPhantomMode where
  /-- Source elements (e.g. concrete global objects). -/
  source : Type u
  /-- Target completion/Postnikov limit objects. -/
  target : Type v
  /-- Canonical comparison map from source objects to completion tower elements. -/
  comparison : source → target

namespace TowerPhantomMode

/-- Subtype of phantom target elements outside `Set.range comparison`. -/
def PhantomSpace (M : TowerPhantomMode.{u, v}) : Type v :=
  { y : M.target // y ∉ Set.range M.comparison }

/-- Existence of at least one phantom element (`Nonempty PhantomSpace`). -/
def HasPhantom (M : TowerPhantomMode.{u, v}) : Prop :=
  Nonempty M.PhantomSpace

end TowerPhantomMode

/-- Identity comparison mode (`id : Unit → Unit`), witnessing absence of phantoms. -/
def idTowerMode : TowerPhantomMode.{0, 0} where
  source := Unit
  target := Unit
  comparison := _root_.id

theorem not_idTowerMode_hasPhantom : ¬ idTowerMode.HasPhantom := by
  rintro ⟨⟨u, hu⟩⟩
  exact hu ⟨u, rfl⟩

/-- Mode (ii) registration of the profinite lasso phantom `ℕ ↪ ℕ̂_lasso` (`InfinityResiduum`). -/
def profiniteLassoTowerMode : TowerPhantomMode.{0, 0} where
  source := ℕ
  target := ProfiniteLasso
  comparison := natToProfiniteLasso

theorem profiniteLassoTowerMode_hasPhantom : profiniteLassoTowerMode.HasPhantom :=
  ⟨⟨zHatToProfiniteLasso (-1 : ProfiniteZHat), zHatToProfiniteLasso_neg_one_not_mem_range_nat⟩⟩

/-- Compatible tower sequences along `stepProductPostnikovSystem` in `StepProductQ`. -/
structure StepPostnikovTowerElem : Type where
  /-- Choice of object in `Obj (qTrunc (n + 1))` lifted through `unit_n`. -/
  seq : ℕ → ℕ
  /-- Compatibility across transition levels `n + 1 → n`. -/
  compat : ∀ n : ℕ, ObjEquivRel
    ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
      (stepProductPostnikovSystem.{0}.level n).unitRel (seq (n + 1)))
    ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
      (stepProductPostnikovSystem.{0}.level n).unitRel (seq n))

/-- Levelwise equivalence of compatible Postnikov tower sequences on `StepProductQ`. -/
def StepPostnikovTowerElem.Eqv (s t : StepPostnikovTowerElem) : Prop :=
  ∀ n : ℕ, ObjEquivRel
    ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
      (stepProductPostnikovSystem.{0}.level n).unitRel (s.seq n))
    ((stepProductPostnikovSystem.{0}.level n).unit.mapObj
      (stepProductPostnikovSystem.{0}.level n).unitRel (t.seq n))

def stepPostnikovSetoid : Setoid StepPostnikovTowerElem where
  r := StepPostnikovTowerElem.Eqv
  iseqv :=
    { refl := fun _ _ ↦ ObjEquivRel.refl _
      symm := fun h n ↦ ObjEquivRel.symm (h n)
      trans := fun h₁ h₂ n ↦ ObjEquivRel.trans (h₁ n) (h₂ n) }

/-- The Postnikov completion limit `RL(Q)` of `StepState.qFull` up to levelwise `ObjEquivRel`. -/
abbrev StepPostnikovLimit : Type := Quotient stepPostnikovSetoid

private def qFullTowerObj (m : ℕ) : StepPostnikovTowerElem where
  seq _ := m
  compat _ := ObjEquivRel.refl _

private def qFullPhantomTower : StepPostnikovTowerElem where
  seq n := n
  compat n := (theorem12D_stepProductQ_phantom_not_realized stepProductPostnikovSystem.{0}).1 n |>.1

/-- Mode (ii) registration of the non-realized `StepProductQ` Postnikov phantom
(`StepProductPhantom`). -/
def stepProductTowerMode : TowerPhantomMode.{0, 0} where
  source := ℕ
  target := StepPostnikovLimit
  comparison := fun m ↦ Quotient.mk stepPostnikovSetoid (qFullTowerObj m)

theorem stepProductTowerMode_hasPhantom : stepProductTowerMode.HasPhantom := by
  refine ⟨⟨Quotient.mk stepPostnikovSetoid qFullPhantomTower, ?_⟩⟩
  rintro ⟨m, hm⟩
  have heqv : StepPostnikovTowerElem.Eqv (qFullTowerObj m) qFullPhantomTower :=
    Quotient.exact hm
  have h12d := (theorem12D_stepProductQ_phantom_not_realized stepProductPostnikovSystem.{0}).2.2
  refine h12d ⟨m, fun n ↦ ObjEquivRel.symm (heqv n)⟩

/-! ### Tri-Modal Factorization: Mode (iii) Forgetful / Homotopy-Fiber Lift Mode -/

/-- **Mode (iii) (`ForgetfulLiftMode`):** Classification of enriched structures lifting `targetBase`
along a forgetful projection `forget : total → base` up to an equivalence relation `fiberEquiv`. -/
structure ForgetfulLiftMode where
  /-- Richer carrier objects (e.g. `δ`-ring structures or algebras). -/
  total : Type u
  /-- Base forgetful objects (e.g. Frobenius-lift rings). -/
  base : Type v
  /-- Forgetful projection `total → base`. -/
  forget : total → base
  /-- Target base object whose lifts are classified. -/
  targetBase : base
  /-- Isomorphism relation on the fiber `{ x : total // forget x = targetBase }`. -/
  fiberEquiv : { x : total // forget x = targetBase } →
    { x : total // forget x = targetBase } → Prop
  /-- Equivalence proof for `fiberEquiv`. -/
  iseqv : Equivalence fiberEquiv

namespace ForgetfulLiftMode

/-- Concrete lift fiber over `targetBase`. -/
def LiftFiber (M : ForgetfulLiftMode.{u, v}) : Type u :=
  { x : M.total // M.forget x = M.targetBase }

/-- Setoid packaging `M.fiberEquiv` on `M.LiftFiber`. -/
def fiberSetoid (M : ForgetfulLiftMode.{u, v}) : Setoid M.LiftFiber :=
  ⟨M.fiberEquiv, M.iseqv⟩

/-- Isomorphism-orbit quotient `LiftFiber / ≃` classifying non-isomorphic lifts. -/
def IsoOrbitQuotient (M : ForgetfulLiftMode.{u, v}) : Type u :=
  Quotient M.fiberSetoid

end ForgetfulLiftMode

/-! ## Section 2: Formal `DoctrinalPhilosophy` `𝔓 = (𝔻, 𝒫)`, Anti-Casuistry,
& Finite Pareto Schism -/

/-- **Formal Philosophy `𝔓 = (𝔻, 𝒫)`:** A domain `D` of doctrinal objects paired with a suite
`P` of kataphatic probes via a satisfaction relation `sat : D → P → Prop`. -/
structure DoctrinalPhilosophy (D : Type u) (P : Type v) : Type (max u v) where
  /-- Kataphatic probe pairing `x ⊨ p`. -/
  sat : D → P → Prop

namespace DoctrinalPhilosophy

/-- The probe theory `Th_𝒫(X) = { p ∈ 𝒫 | ∀ x ∈ X, x ⊨ p }` of a class `X ⊆ 𝔻`. -/
def theoryOf {D : Type u} {P : Type v} (Φ : DoctrinalPhilosophy D P) (X : Set D) : Set P :=
  { p : P | ∀ x ∈ X, Φ.sat x p }

/-- The definable extent `Ext_𝒫(Q) = { x ∈ 𝔻 | ∀ p ∈ Q, x ⊨ p }` of a probe set `Q ⊆ 𝒫`. -/
def extentOf {D : Type u} {P : Type v} (Φ : DoctrinalPhilosophy D P) (Q : Set P) : Set D :=
  { x : D | ∀ p ∈ Q, Φ.sat x p }

/-- Galois/Moore closure `Cl_𝒫(X) = Ext_𝒫(Th_𝒫(X))`. -/
def mooreClosure {D : Type u} {P : Type v} (Φ : DoctrinalPhilosophy D P) (X : Set D) : Set D :=
  Φ.extentOf (Φ.theoryOf X)

theorem le_mooreClosure {D : Type u} {P : Type v} (Φ : DoctrinalPhilosophy D P) (X : Set D) :
    X ⊆ Φ.mooreClosure X :=
  fun x hx _ hp ↦ hp x hx

theorem mooreClosure_monotone {D : Type u} {P : Type v} (Φ : DoctrinalPhilosophy D P) :
    Monotone Φ.mooreClosure :=
  fun _ _ hXY _ hx _ hp ↦ hx _ (fun y hy ↦ hp y (hXY hy))

theorem mooreClosure_idempotent {D : Type u} {P : Type v}
    (Φ : DoctrinalPhilosophy D P) (X : Set D) :
    Φ.mooreClosure (Φ.mooreClosure X) = Φ.mooreClosure X := by
  apply Set.Subset.antisymm
  · intro x hx p hp
    exact hx p (fun y hy ↦ hy p hp)
  · exact Φ.le_mooreClosure (Φ.mooreClosure X)

/-- Stock Mathlib `ClosureOperator (Set D)` induced by a `DoctrinalPhilosophy D P`. -/
def mooreClosureOperator {D : Type u} {P : Type v} (Φ : DoctrinalPhilosophy D P) :
    ClosureOperator (Set D) where
  toFun := Φ.mooreClosure
  monotone' := Φ.mooreClosure_monotone
  le_closure' := Φ.le_mooreClosure
  idempotent' := Φ.mooreClosure_idempotent

/-- Predicate asserting that `Q ⊆ 𝒫` resolves the implication `hyp ∩ Ext_𝒫(Q) ⊆ concl`. -/
def IsSufficientProbeSet {D : Type u} {P : Type v} (Φ : DoctrinalPhilosophy D P)
    (hyp concl : Set D) (Q : Set P) : Prop :=
  hyp ∩ Φ.extentOf Q ⊆ concl

/-- Predicate asserting that `E ⊆ 𝔻` is Moore-closed (`Cl_𝒫(E) = E`). -/
def IsClosedExtent {D : Type u} {P : Type v} (Φ : DoctrinalPhilosophy D P) (E : Set D) : Prop :=
  Φ.mooreClosure E = E

/-- Minimal Pareto frontier of Moore-closed extents `E` resolving `hyp ∩ E ⊆ concl` above the
non-vacuity core `hyp ∩ concl ⊆ E`: no strictly larger (deductively weaker) Moore-closed extent
`E' ⊇ E` also resolves `hyp ∩ E' ⊆ concl`. -/
def paretoFrontier {D : Type u} {P : Type v} (Φ : DoctrinalPhilosophy D P)
    (hyp concl : Set D) : Set (Set D) :=
  { E : Set D | Φ.IsClosedExtent E ∧ hyp ∩ concl ⊆ E ∧ hyp ∩ E ⊆ concl ∧
    ∀ E' : Set D, Φ.IsClosedExtent E' → hyp ∩ concl ⊆ E' → hyp ∩ E' ⊆ concl → E ⊆ E' → E' = E }

end DoctrinalPhilosophy

/-! ### Inquisitor's Impossibility Lemma (Anti-Casuistry Collapse Without Probes) -/

/-- Product-preserving doctrinal transformation on a meet-semilattice `(D, ⊓, ⊤)` (modeling
binary products `X × Y` and terminal object `1`). -/
@[ext]
structure ProductEndo (D : Type u) [SemilatticeInf D] [OrderTop D] : Type u where
  /-- Underlying doctrinal transformation (e.g. slice or open subtopos localization). -/
  toFun : D → D
  /-- Preservation of the terminal object `⊤`. -/
  map_top : toFun ⊤ = ⊤
  /-- Preservation of binary products `x ⊓ y`. -/
  map_inf : ∀ x y : D, toFun (x ⊓ y) = toFun x ⊓ toFun y

instance {D : Type u} [SemilatticeInf D] [OrderTop D] : Monoid (ProductEndo D) where
  one := ⟨_root_.id, rfl, fun _ _ ↦ rfl⟩
  mul σ τ :=
    { toFun := σ.toFun ∘ τ.toFun
      map_top := by simp [τ.map_top, σ.map_top]
      map_inf := fun x y ↦ by simp [Function.comp_apply, τ.map_inf, σ.map_inf] }
  one_mul _ := rfl
  mul_one _ := rfl
  mul_assoc _ _ _ := rfl

/-- Product-closed class on `(D, ⊓, ⊤)`: contains `⊤` and is closed under binary products `⊓`. -/
def IsProductClosed {D : Type u} [SemilatticeInf D] [OrderTop D] (T : Set D) : Prop :=
  (⊤ : D) ∈ T ∧ ∀ ⦃x y : D⦄, x ∈ T → y ∈ T → x ⊓ y ∈ T

/-- `S`-invariance of `C ⊆ D` under a monoid `S` of doctrinal stability operations. -/
def IsSigmaClosed {D : Type u} [SemilatticeInf D] [OrderTop D]
    (S : Submonoid (ProductEndo D)) (C : Set D) : Prop :=
  ∀ σ ∈ S, ∀ ⦃x : D⦄, x ∈ C → σ.toFun x ∈ C

/-- Modal `S4`-interior `□_S(T) = { x ∈ D | ∀ σ ∈ S, σ(x) ∈ T }`. -/
def s4Interior {D : Type u} [SemilatticeInf D] [OrderTop D]
    (S : Submonoid (ProductEndo D)) (T : Set D) : Set D :=
  { x : D | ∀ σ ∈ S, σ.toFun x ∈ T }

/-- **Inquisitor's Impossibility Lemma (`inquisitor_impossibility_casuistry`):**
Purely apophatic closure under products and stability operations `S` admits a unique largest class
`s4Interior S T`:
1. Counit: `s4Interior S T ⊆ T`,
2. `S`-invariance (modal `4` axiom),
3. Product-closure preservation (`IsProductClosed T → IsProductClosed (s4Interior S T)`),
4. Unique maximality: every `S`-closed admissible subclass `C ⊆ T` satisfies `C ⊆ s4Interior S T`.
Hence without kataphatic probes `𝒫`, no apophatic casuistic filter can avoid collapsing to
`s4Interior S T`. -/
theorem inquisitor_impossibility_casuistry {D : Type u} [SemilatticeInf D] [OrderTop D]
    (S : Submonoid (ProductEndo D)) (T : Set D) :
    s4Interior S T ⊆ T ∧
      IsSigmaClosed S (s4Interior S T) ∧
      (IsProductClosed T → IsProductClosed (s4Interior S T)) ∧
      (∀ C : Set D, C ⊆ T → IsSigmaClosed S C → C ⊆ s4Interior S T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hx 1 S.one_mem
  · intro σ hσ x hx τ hτ
    exact hx (τ * σ) (S.mul_mem hτ hσ)
  · intro hT
    refine ⟨fun σ _ ↦ ?_, fun x y hx hy σ hσ ↦ ?_⟩
    · rw [σ.map_top]; exact hT.1
    · rw [σ.map_inf]; exact hT.2 (hx σ hσ) (hy σ hσ)
  · intro C hCT hCsig x hx σ hσ
    exact hCT (hCsig σ hσ hx)

/-! ### Choice-Free Presheaf Combinatorics, Genuine Presheaf Probes, & Pareto Schism -/

/-- Choice-free 2-element absorbing monoid `ℳ₁ = ({e₁, 1₁}, ∧)` (`false = e₁`, `true = 1₁`). -/
@[ext]
structure M1Monoid : Type where
  /-- Underlying toggle (`false` = absorbing zero `e₁`, `true` = identity `1₁`). -/
  val : Bool
  deriving DecidableEq

instance : CommMonoid M1Monoid where
  one := ⟨true⟩
  mul x y := ⟨x.val && y.val⟩
  mul_assoc a b c := by
    cases a
    cases b
    cases c
    exact congrArg M1Monoid.mk (Bool.and_assoc _ _ _)
  one_mul a := by
    cases a
    exact congrArg M1Monoid.mk (Bool.true_and _)
  mul_one a := by
    cases a
    exact congrArg M1Monoid.mk (Bool.and_true _)
  mul_comm a b := by
    cases a
    cases b
    exact congrArg M1Monoid.mk (Bool.and_comm _ _)

/-- Canonical monoid isomorphism identifying `M1Monoid` with `AbsorbingMonoidCarrier 1`. -/
def m1MonoidMulEquiv : M1Monoid ≃* AbsorbingMonoidCarrier 1 where
  toFun x := ⟨x.val⟩
  invFun y := ⟨y.val⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- External projectivity of `1` (`Proj₁`) in the category `Set^M` of left `M`-sets: every
non-empty left `M`-set has a fixed point. -/
def MonoidProj1 (M : Type u) [Monoid M] : Prop :=
  ∀ (X : Type u) [MulAction M X], Nonempty X → ∃ x : X, ∀ m : M, m • x = x

/-- External `Bool`-indexed empty/terminal subterminal-splitting surrogate on left `M`-sets `Set^M`:
for every `U ∈ {∅, 1}` (`Bool`) and `M`-equivariant surjection `p : X → U`, `p` admits an
`M`-equivariant section. Note that for a non-group monoid `M` (such as `M1Monoid`, whose internal
classifier `Ω_{ℳ₁}` has 3 left ideals `{∅ < {e₁} < ℳ₁}`), `Set^M` is non-Boolean; full internal
Supports Split (`CatPresheafProjSub`, Freyd–Ščedrov `SS`) quantifies over all internal subterminal
presheaves `IsSubterminalPresheaf` in Section `Genuine Category-Presheaf Probes` below. -/
def MonoidProjSub (M : Type u) [Monoid M] : Prop :=
  ∀ (X : Type u) [MulAction M X] (U : Bool) (p : X → { _u : Unit // U = true }),
    Function.Surjective p → ∃ s : { _u : Unit // U = true } → X,
      (∀ u, p (s u) = u) ∧ (∀ (m : M) u, m • s u = s u)

/-- Localic generation in `Set^M`: every element of every `M`-set lies in the image of a morphism
from the subterminal `1 = Unit`. -/
def MonoidSubterminalsGenerate (M : Type u) [Monoid M] : Prop :=
  ∀ (X : Type u) [MulAction M X] (x : X),
    ∃ f : Unit → X, (∀ m : M, m • f () = f ()) ∧ f () = x

/-- **Monoid Right-Zero Lemma (`monoid_proj1_iff_rightZero`):** Terminal `1` is externally
projective in `Set^M` iff `M` possesses a right zero `e` (`∀ m, m * e = e`). Choice-free! -/
theorem monoid_proj1_iff_rightZero (M : Type u) [Monoid M] :
    MonoidProj1 M ↔ ∃ e : M, ∀ m : M, m * e = e := by
  constructor
  · intro hProj
    exact hProj M ⟨(1 : M)⟩
  · rintro ⟨e, he⟩ X _ ⟨x₀⟩
    refine ⟨e • x₀, fun m ↦ ?_⟩
    rw [← mul_smul, he m]

/-- Localicity of `Set^M`: subterminals generate `Set^M` iff `M` is subsingleton. Choice-free! -/
theorem monoid_subterminalsGenerate_iff_subsingleton (M : Type u) [Monoid M] :
    MonoidSubterminalsGenerate M ↔ Subsingleton M := by
  constructor
  · intro hGen
    refine ⟨fun a b ↦ ?_⟩
    rcases hGen M (1 : M) with ⟨f, hf, hf1⟩
    have ha : a = 1 := by
      have h : a * f () = f () := hf a
      rw [hf1, mul_one] at h
      exact h
    have hb : b = 1 := by
      have h : b * f () = f () := hf b
      rw [hf1, mul_one] at h
      exact h
    exact ha.trans hb.symm
  · intro hSub X _ x
    refine ⟨fun _ ↦ x, fun m ↦ ?_, rfl⟩
    rw [Subsingleton.elim m 1, one_smul]

/-- Helper for choice-free equality on `M1Monoid`: any nonempty `ℳ₁`-set has a right-zero
section `x₀ ↦ ⟨false⟩ • x₀`. -/
theorem m1_proj1 : MonoidProj1 M1Monoid :=
  (monoid_proj1_iff_rightZero M1Monoid).mpr
    ⟨⟨false⟩, fun m ↦ M1Monoid.ext (Bool.and_false m.val)⟩

/-- **Constructive `ℳ₁ ∈ ProjSub \ Localic` Separation:** Presheaves on `M1Monoid` satisfy Supports
Split (`ProjSub`) constructively via `u ↦ e₁ • x₀`, yet fail localicity because `⟨false⟩ ≠ ⟨true⟩`.
Zero `Classical.choice`! -/
theorem m1_projSub_and_not_localic :
    MonoidProjSub M1Monoid ∧ ¬ MonoidSubterminalsGenerate M1Monoid := by
  constructor
  · intro X _ U p hp
    cases U
    · exact ⟨fun u ↦ False.elim (Bool.false_ne_true u.2),
        fun u ↦ False.elim (Bool.false_ne_true u.2),
        fun _ u ↦ False.elim (Bool.false_ne_true u.2)⟩
    · obtain ⟨x₀, _⟩ := hp ⟨(), rfl⟩
      refine ⟨fun _ ↦ (⟨false⟩ : M1Monoid) • x₀,
        fun u ↦ Subtype.ext rfl, fun m _ ↦ ?_⟩
      rw [← mul_smul]
      have hz : m * (⟨false⟩ : M1Monoid) = ⟨false⟩ := M1Monoid.ext (Bool.and_false m.val)
      rw [hz]
  · rw [monoid_subterminalsGenerate_iff_subsingleton]
    intro hSub
    exact Bool.false_ne_true (congrArg M1Monoid.val (hSub.elim ⟨false⟩ ⟨true⟩))

/-- Contravariant presheaves `P^op → Type` on a preorder `P`. -/
structure PosetPresheaf (P : Type) [Preorder P] : Type 1 where
  /-- Fiber set at object `p : P`. -/
  obj : P → Type
  /-- Restriction map along `p ≤ q`. -/
  res : ∀ ⦃p q : P⦄, p ≤ q → obj q → obj p
  /-- Functorial identity law. -/
  res_refl : ∀ (p : P) (x : obj p), res le_rfl x = x
  /-- Functorial composition law. -/
  res_trans : ∀ ⦃p q r : P⦄ (hpq : p ≤ q) (hqr : q ≤ r) (x : obj r),
    res hpq (res hqr x) = res (hpq.trans hqr) x

/-- Downward-closed subterminal sieve in `P` (`U ↣ 1`). -/
structure PosetSubterminal (P : Type) [Preorder P] : Type where
  /-- Membership predicate on objects `p : P`. -/
  mem : P → Prop
  /-- Downward closure of subterminals in `Set^(P^op)`. -/
  down : ∀ ⦃p q : P⦄, p ≤ q → mem q → mem p

/-- In `Set^(P^op)` for a preorder `P`, every element `x : F.obj p` is hit by the Yoneda morphism
from the principal subterminal `↓p = { q | q ≤ p }`. -/
def PosetSubterminalsGenerate (P : Type) [PartialOrder P] : Prop :=
  ∀ (F : PosetPresheaf P) (p : P) (x : F.obj p),
    ∃ (U : PosetSubterminal P) (s : (q : P) → U.mem q → F.obj q),
      (∀ q r (hqr : q ≤ r) (hr : U.mem r), F.res hqr (s r hr) = s q (U.down hqr hr)) ∧
      ∃ hp : U.mem p, s p hp = x

/-- Yoneda generation for any partial order `P`: `Set^(P^op)` is **always localic**! Choice-free! -/
theorem poset_subterminals_generate (P : Type) [PartialOrder P] :
    PosetSubterminalsGenerate P := by
  intro F p x
  let U : PosetSubterminal P := ⟨fun q ↦ q ≤ p, fun _ _ hqr hrp ↦ hqr.trans hrp⟩
  refine ⟨U, fun q hq ↦ F.res hq x, fun q r hqr hrp ↦ F.res_trans hqr hrp x, le_rfl, ?_⟩
  exact F.res_refl p x

/-- External projectivity of `1` (`Proj₁`) in `Set^(P^op)`. -/
def PosetProj1 (P : Type) [Preorder P] : Prop :=
  ∀ F : PosetPresheaf P, (∀ p : P, Nonempty (F.obj p)) →
    ∃ s : (p : P) → F.obj p, ∀ p q (hpq : p ≤ q), F.res hpq (s q) = s p

/-- Subterminal splitting (`ProjSub` = `SS`) in `Set^(P^op)`. -/
def PosetProjSub (P : Type) [Preorder P] : Prop :=
  ∀ (U : PosetSubterminal P) (F : PosetPresheaf P), (∀ p : P, U.mem p → Nonempty (F.obj p)) →
    ∃ s : (p : P) → U.mem p → F.obj p,
      ∀ p q (hpq : p ≤ q) (hq : U.mem q), F.res hpq (s q hq) = s p (U.down hpq hq)

theorem posetProjSub_imp_proj1 {P : Type} [Preorder P] (h : PosetProjSub P) : PosetProj1 P := by
  intro F hF
  rcases h ⟨fun _ ↦ True, fun _ _ _ _ ↦ trivial⟩ F (fun p _ ↦ hF p) with ⟨s, hs⟩
  exact ⟨fun p ↦ s p trivial, fun p q hpq ↦ hs p q hpq trivial⟩

/-- The 3-element V-poset `V = { a > c < b }`. -/
inductive VPoset : Type
  | c
  | a
  | b
  deriving DecidableEq

private def vPosetLE : VPoset → VPoset → Prop
  | .c, _ => True
  | .a, .a => True
  | .b, .b => True
  | _, _ => False

instance : PartialOrder VPoset where
  le := vPosetLE
  le_refl x := by cases x <;> trivial
  le_trans x y z hxy hyz := by cases x <;> cases y <;> cases z <;> simp_all [vPosetLE]
  le_antisymm x y hxy hyx := by cases x <;> cases y <;> simp_all [vPosetLE]

private def vPosetCoprodObj : VPoset → Type
  | .a => Unit
  | .b => Unit
  | .c => Bool

private def vPosetCoprodRes : ∀ ⦃p q : VPoset⦄, p ≤ q → vPosetCoprodObj q → vPosetCoprodObj p
  | .a, .a, _, x => x
  | .b, .b, _, x => x
  | .c, .c, _, x => x
  | .c, .a, _, _ => false
  | .c, .b, _, _ => true
  | .a, .c, h, _ => False.elim h
  | .a, .b, h, _ => False.elim h
  | .b, .c, h, _ => False.elim h
  | .b, .a, h, _ => False.elim h

private def vPosetCoprod : PosetPresheaf VPoset where
  obj := vPosetCoprodObj
  res := vPosetCoprodRes
  res_refl p x := by cases p <;> rfl
  res_trans p q r hpq hqr x := by
    cases p <;> cases q <;> cases r <;> first | exact False.elim hpq | exact False.elim hqr | rfl

/-- **Constructive `V ∈ Localic \ Proj₁` Separation:** Presheaves on the 3-element V-poset
are localic, yet fail `Proj₁` (hence fail `ProjSub`) via `F = y(a) ∐ y(b)`. Choice-free! -/
theorem vPoset_localic_not_proj1 :
    PosetSubterminalsGenerate VPoset ∧ ¬ PosetProj1 VPoset := by
  refine ⟨poset_subterminals_generate VPoset, fun hP ↦ ?_⟩
  have hne : ∀ p : VPoset, Nonempty (vPosetCoprod.obj p) := fun p ↦ by
    cases p
    · exact ⟨false⟩
    · exact ⟨()⟩
    · exact ⟨()⟩
  rcases hP vPosetCoprod hne with ⟨s, hs⟩
  have hca : false = s .c := hs .c .a trivial
  have hcb : true = s .c := hs .c .b trivial
  exact Bool.false_ne_true (hca.trans hcb.symm)

theorem vPoset_not_projSub : ¬ PosetProjSub VPoset :=
  fun h ↦ vPoset_localic_not_proj1.2 (posetProjSub_imp_proj1 h)

/-- The 4-element diamond poset `D₄ = { bot < left, right < top }`. -/
inductive DiamondPoset : Type
  | bot
  | left
  | right
  | top
  deriving DecidableEq

private def diamondLE : DiamondPoset → DiamondPoset → Prop
  | .bot, _ => True
  | _, .top => True
  | .left, .left => True
  | .right, .right => True
  | _, _ => False

instance : PartialOrder DiamondPoset where
  le := diamondLE
  le_refl x := by cases x <;> trivial
  le_trans x y z hxy hyz := by
    cases x <;> cases y <;> cases z <;> simp_all [diamondLE]
  le_antisymm x y hxy hyx := by
    cases x <;> cases y <;> simp_all [diamondLE]

private def diamondCoprodObj : DiamondPoset → Type
  | .top => Empty
  | .left => Unit
  | .right => Unit
  | .bot => Bool

private def diamondCoprodRes :
    ∀ ⦃p q : DiamondPoset⦄, p ≤ q → diamondCoprodObj q → diamondCoprodObj p
  | .bot, .bot, _, x => x
  | .bot, .left, _, _ => false
  | .bot, .right, _, _ => true
  | .left, .left, _, x => x
  | .right, .right, _, x => x
  | .top, .top, _, x => x
  | _, .top, _, e => Empty.elim e
  | .left, .bot, h, _ => False.elim h
  | .left, .right, h, _ => False.elim h
  | .right, .bot, h, _ => False.elim h
  | .right, .left, h, _ => False.elim h
  | .top, .bot, h, _ => False.elim h
  | .top, .left, h, _ => False.elim h
  | .top, .right, h, _ => False.elim h

private def diamondCoprod : PosetPresheaf DiamondPoset where
  obj := diamondCoprodObj
  res := diamondCoprodRes
  res_refl p x := by
    cases p
    · rfl
    · rfl
    · rfl
    · exact Empty.elim x
  res_trans p q r hpq hqr x := by
    cases p <;> cases q <;> cases r <;>
      first | exact False.elim hpq | exact False.elim hqr | exact Empty.elim x | rfl

/-- **`Proj₁` vs. `ProjSub` Separation on `DiamondPoset` (`diamond_proj1_not_projSub`):**
`Set^(D₄^op)` satisfies `Proj₁` (since `top` is greatest), yet fails `ProjSub` over the open
subterminal `U = {bot, left, right} ↣ 1`. Zero `Classical.choice`! -/
theorem diamond_proj1_not_projSub :
    PosetProj1 DiamondPoset ∧ ¬ PosetProjSub DiamondPoset := by
  constructor
  · intro F hF
    obtain ⟨xTop⟩ := hF .top
    have hle : ∀ p : DiamondPoset, p ≤ .top := fun p ↦ by cases p <;> trivial
    refine ⟨fun p ↦ F.res (hle p) xTop, fun p q hpq ↦ ?_⟩
    exact F.res_trans hpq (hle q) xTop
  · intro hSub
    let U : PosetSubterminal DiamondPoset :=
      { mem := fun p ↦ p ≠ .top
        down := fun p q hpq hq heq ↦ by
          subst heq
          cases q <;> first | exact hpq | exact absurd rfl hq }
    have hne : ∀ p, U.mem p → Nonempty (diamondCoprod.obj p) := fun p hp ↦ by
      cases p
      · exact ⟨false⟩
      · exact ⟨()⟩
      · exact ⟨()⟩
      · exact absurd rfl hp
    rcases hSub U diamondCoprod hne with ⟨s, hs⟩
    have hl : (U.mem .left) := by decide
    have hr : (U.mem .right) := by decide
    have hbl : false = s .bot (U.down (by trivial : DiamondPoset.bot ≤ .left) hl) :=
      hs .bot .left trivial hl
    have hbr : true = s .bot (U.down (by trivial : DiamondPoset.bot ≤ .right) hr) :=
      hs .bot .right trivial hr
    exact Bool.false_ne_true (hbl.trans hbr.symm)

/-- Choice-free concrete 2-element group `ℤ/2ℤ` carried on `Bool` (`false = 1`, `true = -1`,
multiplication = `xor`). -/
@[ext]
structure TwoGroup : Type where
  /-- Underlying toggle (`false` = identity, `true` = involution). -/
  val : Bool
  deriving DecidableEq

instance : CommGroup TwoGroup where
  one := ⟨false⟩
  mul x y := ⟨xor x.val y.val⟩
  inv x := x
  mul_assoc a b c := by
    rcases a with ⟨_ | _⟩ <;> rcases b with ⟨_ | _⟩ <;> rcases c with ⟨_ | _⟩ <;> rfl
  one_mul a := by rcases a with ⟨_ | _⟩ <;> rfl
  mul_one a := by rcases a with ⟨_ | _⟩ <;> rfl
  inv_mul_cancel a := by rcases a with ⟨_ | _⟩ <;> rfl
  mul_comm a b := by rcases a with ⟨_ | _⟩ <;> rcases b with ⟨_ | _⟩ <;> rfl

/-- Explicit group isomorphism `TwoGroup ≃* Multiplicative (ZMod 2)`. -/
def twoGroupMulEquivZMod2 : TwoGroup ≃* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (if x.val then 1 else 0)
  invFun y := ⟨decide (Multiplicative.toAdd y = 1)⟩
  left_inv := by
    rintro ⟨_ | _⟩ <;> rfl
  right_inv y := by
    apply Multiplicative.toAdd.injective
    dsimp only
    rcases R2Ring.zmod2_eq_zero_or_one (Multiplicative.toAdd y) with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl
  map_mul' := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ <;> decide

/-- `Set^{ℤ/2ℤ}` fails both `Proj₁` and `ProjSub` (`two_orb` fixed-point free action) and is
non-localic (`Sub(1) = {∅, 1}` fails to generate `TwoGroup`). Choice-free! -/
theorem twoGroup_not_proj1_not_localic :
    ¬ MonoidProj1 TwoGroup ∧ ¬ MonoidProjSub TwoGroup ∧ ¬ MonoidSubterminalsGenerate TwoGroup := by
  refine ⟨?_, ?_, ?_⟩
  · rw [monoid_proj1_iff_rightZero]
    rintro ⟨e, he⟩
    have h1 := he ⟨true⟩
    rcases e with ⟨_ | _⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
  · intro hSub
    rcases hSub TwoGroup true (fun _ ↦ ⟨(), rfl⟩) (fun _ ↦ ⟨⟨false⟩, rfl⟩) with ⟨s, _, hs⟩
    have hs1 : (⟨true⟩ : TwoGroup) * s ⟨(), rfl⟩ = s ⟨(), rfl⟩ := hs ⟨true⟩ ⟨(), rfl⟩
    rcases hsv : s ⟨(), rfl⟩ with ⟨_ | _⟩
    · rw [hsv] at hs1; exact absurd hs1 (by decide)
    · rw [hsv] at hs1; exact absurd hs1 (by decide)
  · rw [monoid_subterminalsGenerate_iff_subsingleton]
    intro hSub
    exact Bool.false_ne_true (congrArg TwoGroup.val (hSub.elim ⟨false⟩ ⟨true⟩))

/-! #### Uniform Categorical Presheaf Predicates on `(C : Type) [SmallCategory C]` -/

/-- Terminal presheaf `1 : C ⥤ Type` sending every object to `PUnit` (Choice-free). -/
def terminalPresheaf (C : Type) [SmallCategory C] : C ⥤ Type where
  obj _ := PUnit
  map _ _ := ()
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Explicit Choice-free product `F × G : C ⥤ Type` of presheaves over `C`. -/
def prodPresheaf {C : Type} [SmallCategory C] (F G : C ⥤ Type) : C ⥤ Type where
  obj d := F.obj d × G.obj d
  map f p := (F.map f p.1, G.map f p.2)
  map_id d := funext fun p ↦ Prod.ext (congrFun (F.map_id d) p.1) (congrFun (G.map_id d) p.2)
  map_comp f g := funext fun p ↦
    Prod.ext (congrFun (F.map_comp f g) p.1) (congrFun (G.map_comp f g) p.2)

/-- Explicit Choice-free covariant representable presheaf `Hom_C(c, -) : C ⥤ Type`. -/
def coyonedaPresheaf (C : Type) [SmallCategory C] (c : C) : C ⥤ Type where
  obj d := c ⟶ d
  map f g := g ≫ f
  map_id _ := funext fun g ↦ Category.comp_id g
  map_comp f g := funext fun h ↦ (Category.assoc h f g).symm

/-- Bridge identifying `coyonedaPresheaf C c` with Mathlib's `coyoneda.obj (Opposite.op c)`. -/
theorem coyonedaPresheaf_eq_coyoneda (C : Type) [SmallCategory C] (c : C) :
    coyonedaPresheaf C c = coyoneda.obj (Opposite.op c) :=
  rfl

/-- Bridge equating pointwise composition of `NatTrans` with `≫` in `C ⥤ Type`. -/
theorem natTrans_pointwise_comp_iff {C : Type} [SmallCategory C] {F G H : C ⥤ Type}
    (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) :
    (∀ c x, β.app c (α.app c x) = γ.app c x) ↔ α ≫ β = γ := by
  constructor
  · intro h
    exact NatTrans.ext (funext fun c ↦ funext fun x ↦ h c x)
  · intro h c x
    exact congrFun (congrFun (congrArg NatTrans.app h) c) x

/-- Pointwise epimorphism (`Surjective`) of a natural transformation `e : NatTrans X Y` in
`C ⥤ Type`. -/
def IsPointwiseSurjective {C : Type} [SmallCategory C] {X Y : C ⥤ Type} (e : NatTrans X Y) : Prop :=
  ∀ c : C, Function.Surjective (e.app c)

/-- Subterminal presheaf predicate (`∀ c, Subsingleton (U.obj c)`) in `C ⥤ Type`. -/
def IsSubterminalPresheaf {C : Type} [SmallCategory C] (U : C ⥤ Type) : Prop :=
  ∀ c : C, Subsingleton (U.obj c)

/-- External Axiom of Choice (`AC`) in the presheaf topos `C ⥤ Type`: every pointwise-surjective
morphism admits a natural section. -/
def CatPresheafAC (C : Type) [SmallCategory C] : Prop :=
  ∀ ⦃X Y : C ⥤ Type⦄ (e : NatTrans X Y), IsPointwiseSurjective e →
    ∃ s : NatTrans Y X, ∀ c y, e.app c (s.app c y) = y

/-- Internal Axiom of Choice (`IAC`) in `C ⥤ Type`: for every presheaf `Z` and pointwise-surjective
`e : X ↠ Y`, the exponential `e^Z : X^Z ⟶ Y^Z` is pointwise surjective, formulated via the Yoneda
correspondence `(Y^Z)(c) ≅ NatTrans (y(c) × Z) Y`. -/
def CatPresheafIAC (C : Type) [SmallCategory C] : Prop :=
  ∀ ⦃X Y : C ⥤ Type⦄ (Z : C ⥤ Type) (e : NatTrans X Y), IsPointwiseSurjective e →
    ∀ (c : C) (g : NatTrans (prodPresheaf (coyonedaPresheaf C c) Z) Y),
      ∃ f : NatTrans (prodPresheaf (coyonedaPresheaf C c) Z) X,
        ∀ d p, e.app d (f.app d p) = g.app d p

/-- Supports Split (`ProjSub`) in `C ⥤ Type`: every pointwise-surjective map onto a subterminal
admits a section. -/
def CatPresheafProjSub (C : Type) [SmallCategory C] : Prop :=
  ∀ ⦃U X : C ⥤ Type⦄, IsSubterminalPresheaf U → ∀ (e : NatTrans X U),
    IsPointwiseSurjective e → ∃ s : NatTrans U X, ∀ c u, e.app c (s.app c u) = u

/-- External projectivity of `1` (`Proj₁`) in `C ⥤ Type`. -/
def CatPresheafProj1 (C : Type) [SmallCategory C] : Prop :=
  ∀ ⦃X : C ⥤ Type⦄ (e : NatTrans X (terminalPresheaf C)), IsPointwiseSurjective e →
    ∃ s : NatTrans (terminalPresheaf C) X, ∀ c u, e.app c (s.app c u) = u

/-- Localicity in `C ⥤ Type`: subterminals generate every presheaf `X : C ⥤ Type`. -/
def CatPresheafLocalic (C : Type) [SmallCategory C] : Prop :=
  ∀ (X : C ⥤ Type) (c : C) (x : X.obj c),
    ∃ (U : C ⥤ Type), IsSubterminalPresheaf U ∧
      ∃ (f : NatTrans U X) (u : U.obj c), f.app c u = x

theorem catPresheafAC_imp_iac {C : Type} [SmallCategory C] (hAC : CatPresheafAC C) :
    CatPresheafIAC C := by
  intro X Y Z e he c g
  rcases hAC e he with ⟨s, hs⟩
  refine ⟨
    { app := fun d p ↦ s.app d (g.app d p)
      naturality := fun _ _ h ↦ funext fun p ↦
        (congrArg (s.app _) (congrFun (g.naturality h) p)).trans
          (congrFun (s.naturality h) (g.app _ p)) },
    fun d p ↦ hs d (g.app d p)⟩

theorem catPresheafAC_imp_projSub {C : Type} [SmallCategory C] (hAC : CatPresheafAC C) :
    CatPresheafProjSub C :=
  fun _ _ _ e he ↦ hAC e he

theorem catPresheafProjSub_imp_proj1 {C : Type} [SmallCategory C] (hSub : CatPresheafProjSub C) :
    CatPresheafProj1 C :=
  fun _ e he ↦ hSub (fun _ ↦ ⟨fun _ _ ↦ rfl⟩) e he

theorem catPresheafLocalic_imp_separating {C : Type} [SmallCategory C]
    (hLoc : CatPresheafLocalic C) {X Y : C ⥤ Type} (g₁ g₂ : NatTrans X Y)
    (hEq : ∀ U : C ⥤ Type, IsSubterminalPresheaf U → ∀ f : NatTrans U X, ∀ c u,
      g₁.app c (f.app c u) = g₂.app c (f.app c u)) :
    g₁ = g₂ := by
  apply NatTrans.ext
  funext c x
  rcases hLoc X c x with ⟨U, hU, f, u, rfl⟩
  exact hEq U hU f c u

/-- Choice-free terminal 1-object category representing `Set`. -/
inductive PUnitCat : Type
  | star
  deriving DecidableEq

instance : SmallCategory PUnitCat where
  Hom _ _ := PUnit
  id _ := ()
  comp _ _ := ()
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Single-object category `B(ℤ/2ℤ)` whose presheaves are `Set^{ℤ/2ℤ}`. -/
abbrev TwoGroupCat : Type := SingleObj TwoGroup

/-- Single-object category `B(ℳ₁)` whose presheaves are `Set^{ℳ₁}`. -/
abbrev M1Cat : Type := SingleObj M1Monoid

/-- Opposite category `VPosetᵒᵖ` whose covariant functors `VPosetᵒᵖ ⥤ Type` are `Set^{V^op}`. -/
abbrev VPosetOpCat : Type := Opposite VPoset

/-! #### Genuine 2-Object Freyd Cover Category `(B(ℤ/2ℤ))_⊥` (`BZ2BotObj`) -/

/-- Objects of the genuine 2-object Freyd cover / cone-adjoined category `(B(ℤ/2ℤ))_⊥`: a new
initial cone vertex `bot` adjoined to the single object `star` of `B(ℤ/2ℤ)`. -/
inductive BZ2BotObj : Type
  | bot
  | star
  deriving DecidableEq

/-- Hom-sets of `(B(ℤ/2ℤ))_⊥`: unique morphism `bot ⟶ star` and `bot ⟶ bot`, `PEmpty` for
`star ⟶ bot`, and `TwoGroup ≅ ℤ/2ℤ` for `star ⟶ star`. -/
@[reducible]
def BZ2BotHom : BZ2BotObj → BZ2BotObj → Type
  | .bot, .bot => PUnit
  | .bot, .star => PUnit
  | .star, .bot => PEmpty
  | .star, .star => TwoGroup

private def bz2BotComp :
    ∀ {X Y Z : BZ2BotObj}, BZ2BotHom X Y → BZ2BotHom Y Z → BZ2BotHom X Z
  | .bot, .bot, .bot, _, _ => ()
  | .bot, .bot, .star, _, _ => ()
  | .bot, .star, .star, _, _ => ()
  | .star, .star, .star, (f : TwoGroup), (g : TwoGroup) => g * f
  | .bot, .star, .bot, _, h => PEmpty.elim h
  | .star, .bot, _, f, _ => PEmpty.elim f
  | .star, .star, .bot, _, g => PEmpty.elim g

instance : SmallCategory BZ2BotObj where
  Hom := BZ2BotHom
  id
    | .bot => ()
    | .star => (1 : TwoGroup)
  comp := bz2BotComp
  id_comp {X Y} f := by
    cases X <;> cases Y
    · rcases f with ⟨⟩; rfl
    · rcases f with ⟨⟩; rfl
    · exact PEmpty.elim f
    · exact mul_one (f : TwoGroup)
  comp_id {X Y} f := by
    cases X <;> cases Y
    · rcases f with ⟨⟩; rfl
    · rcases f with ⟨⟩; rfl
    · exact PEmpty.elim f
    · exact one_mul (f : TwoGroup)
  assoc {W X Y Z} f g h := by
    cases W <;> cases X <;> cases Y <;> cases Z
    all_goals
      first
      | rfl
      | exact PEmpty.elim f
      | exact PEmpty.elim g
      | exact PEmpty.elim h
      | exact (mul_assoc (h : TwoGroup) (g : TwoGroup) (f : TwoGroup)).symm

/-- Unique terminal projection functor `! : E ⥤ PUnitCat` from any category `E` to the
terminal 1-object category `PUnitCat`. -/
def toPUnitCatFunctor (E : Type u₁) [Category.{v₁} E] : E ⥤ PUnitCat where
  obj _ := PUnitCat.star
  map _ := ()

/-- Non-trivial doctrinal fibration `! : E ⥤ PUnitCat` induced by the terminal functor on any
category `E` (specializing e.g. to `BZ2BotObj` and `TwoGroupCat`, whose object/morphism structure
does not collapse to `PUnitCat`). -/
def DoctrinalFibration.toTerminal (E : Type u₁) [Category.{v₁} E] :
    DoctrinalFibration E PUnitCat where
  proj := toPUnitCatFunctor E
  isFibered := Functor.IsFibered.of_exists_isStronglyCartesian fun a R f ↦ by
    cases R
    cases f
    refine ⟨a, 𝟙 a, { toIsHomLift := .map (𝟙 a), universal_property' := fun {a'} g φ' _ ↦ ?_ }⟩
    cases g
    exact ⟨φ', ⟨.map φ', Category.comp_id φ'⟩, fun χ ⟨_, hχ⟩ ↦ (Category.comp_id χ).symm.trans hχ⟩

/-- Inclusion `PUnitCat ⥤ BZ2BotObj` sending `.star ↦ .star`. -/
def bz2BotStarIncl : PUnitCat ⥤ BZ2BotObj where
  obj _ := .star
  map _ := (1 : TwoGroup)
  map_id _ := rfl
  map_comp _ _ := (mul_one (1 : TwoGroup)).symm

/-- Negative `Functor.IsFibered` witness: `bz2BotStarIncl : PUnitCat ⥤ BZ2BotObj` fails to be
fibered because `.bot ⟶ .star` admits no domain lift over `.bot` (and `BZ2BotHom .star .bot` is
empty). -/
theorem not_isFibered_bz2BotStarIncl : ¬ bz2BotStarIncl.IsFibered := by
  intro hFib
  let f : BZ2BotObj.bot ⟶ bz2BotStarIncl.obj PUnitCat.star := ()
  rcases @CategoryTheory.Functor.IsPreFibered.exists_isCartesian'
      BZ2BotObj PUnitCat _ _ bz2BotStarIncl hFib.toIsPreFibered PUnitCat.star .bot f with
    ⟨b, φ, hCart⟩
  haveI := hCart.toIsHomLift
  have hb : bz2BotStarIncl.obj b = BZ2BotObj.bot :=
    CategoryTheory.IsHomLift.domain_eq bz2BotStarIncl f φ
  cases hb

/-- Non-trivial vs. negative `DoctrinalFibration` separation on `BZ2BotObj`. -/
theorem doctrinalFibration_nontrivial_sep :
    Nontrivial BZ2BotObj ∧
      Nonempty (DoctrinalFibration BZ2BotObj PUnitCat) ∧
      ¬ bz2BotStarIncl.IsFibered :=
  ⟨⟨⟨.bot, .star, fun h ↦ by cases h⟩⟩, ⟨DoctrinalFibration.toTerminal BZ2BotObj⟩,
    not_isFibered_bz2BotStarIncl⟩

/-- Terminal projection functor `Bool ⥤ PUnitCat` from the preorder category `(Bool, ≤)`. -/
def boolBangFunctor : Bool ⥤ PUnitCat :=
  toPUnitCatFunctor Bool

/-- Constant `true : PUnitCat ⥤ Bool` functor picking the top object of `(Bool, ≤)`. -/
def punitTrueFunctor : PUnitCat ⥤ Bool where
  obj _ := true
  map _ := CategoryTheory.homOfLE le_rfl

/-- Canonical non-identity adjunction `boolBangFunctor ⊣ punitTrueFunctor` (`Bool ⇄ PUnitCat`),
exhibiting `.star ⟶ .star` against `b ⟶ true` in `(Bool, ≤)`. -/
def boolBangAdjTrue : boolBangFunctor ⊣ punitTrueFunctor where
  unit :=
    { app := fun b ↦ CategoryTheory.homOfLE (by cases b <;> decide)
      naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  counit :=
    { app := fun _ ↦ ()
      naturality := fun _ _ _ ↦ rfl }
  left_triangle_components _ := rfl
  right_triangle_components _ := Subsingleton.elim _ _

/-- Constant `false : Bool ⥤ Bool` endofunctor, breaking `punitTrueFunctor` compatibility on
Beck–Chevalley mates. -/
def boolConstFalseFunctor : Bool ⥤ Bool where
  obj _ := false
  map _ := CategoryTheory.homOfLE le_rfl

/-- Non-identity `MateDoubleSquare` witness with `adjTop = adjBot = boolBangAdjTrue` and
vertical functors `(𝟭 Bool, 𝟭 PUnitCat)`, satisfying `IsBeckChevalley`. -/
def nonIdBeckChevalleyPosSq :
    MateDoubleSquare (𝟭 Bool) (𝟭 PUnitCat)
      boolBangFunctor punitTrueFunctor boolBangFunctor punitTrueFunctor where
  adjTop := boolBangAdjTrue
  adjBot := boolBangAdjTrue
  alpha := CategoryTheory.TwoSquare.mk _ _ _ _ { app := fun _ ↦ () }

/-- Non-identity `MateDoubleSquare` witness with `adjTop = adjBot = boolBangAdjTrue` and
`G = boolConstFalseFunctor`: `alpha` is a natural isomorphism, yet its Beck–Chevalley mate
`(false ⟶ true)` in `(Bool, ≤)` is non-invertible. -/
def nonIdBeckChevalleyNegSq :
    MateDoubleSquare boolConstFalseFunctor (𝟭 PUnitCat)
      boolBangFunctor punitTrueFunctor boolBangFunctor punitTrueFunctor where
  adjTop := boolBangAdjTrue
  adjBot := boolBangAdjTrue
  alpha := CategoryTheory.TwoSquare.mk _ _ _ _ { app := fun _ ↦ () }

/-- Strict separation on non-identity `MateDoubleSquare` witnesses (`boolBangAdjTrue`):
the compatible square is Beck–Chevalley with `defectMorphismProperty (𝟙 PUnitCat.star)`,
whereas `nonIdBeckChevalleyNegSq` has invertible primary `alpha` yet refutes both
`IsBeckChevalley` and `defectMorphismProperty (𝟙 PUnitCat.star)`. -/
theorem nonId_mateDoubleSquare_beckChevalley_sep :
    (nonIdBeckChevalleyPosSq.IsBeckChevalley ∧
        nonIdBeckChevalleyPosSq.defectMorphismProperty (𝟙 PUnitCat.star)) ∧
      (IsIso nonIdBeckChevalleyNegSq.alpha.natTrans ∧
        ¬ nonIdBeckChevalleyNegSq.IsBeckChevalley ∧
        ¬ nonIdBeckChevalleyNegSq.defectMorphismProperty (𝟙 PUnitCat.star)) := by
  have hPosApp : IsIso (nonIdBeckChevalleyPosSq.beckChevalleyMate.natTrans.app PUnitCat.star) := by
    have hEq :
        nonIdBeckChevalleyPosSq.beckChevalleyMate.natTrans.app PUnitCat.star = 𝟙 (true : Bool) :=
      Subsingleton.elim _ _
    rw [hEq]
    infer_instance
  have hPosAll : nonIdBeckChevalleyPosSq.IsBeckChevalley := by
    change IsIso nonIdBeckChevalleyPosSq.beckChevalleyMate.natTrans
    rw [CategoryTheory.NatTrans.isIso_iff_isIso_app]
    intro X
    cases X
    exact hPosApp
  have hAlphaIso : IsIso nonIdBeckChevalleyNegSq.alpha.natTrans := by
    rw [CategoryTheory.NatTrans.isIso_iff_isIso_app]
    intro b
    exact ⟨(), rfl, rfl⟩
  have hNegApp :
      ¬ IsIso (nonIdBeckChevalleyNegSq.beckChevalleyMate.natTrans.app PUnitCat.star) := by
    intro hIso
    have hle : (true : Bool) ≤ false :=
      CategoryTheory.leOfHom
        (@CategoryTheory.inv _ _ _ _
          (nonIdBeckChevalleyNegSq.beckChevalleyMate.natTrans.app PUnitCat.star) hIso)
    exact (by decide : ¬ ((true : Bool) ≤ false)) hle
  refine ⟨⟨hPosAll, ⟨hPosApp, hPosApp⟩⟩, ⟨hAlphaIso, ?_, ?_⟩⟩
  · intro hBC
    have hApp : IsIso (nonIdBeckChevalleyNegSq.beckChevalleyMate.natTrans.app PUnitCat.star) := by
      haveI : IsIso nonIdBeckChevalleyNegSq.beckChevalleyMate.natTrans := hBC
      infer_instance
    exact hNegApp hApp
  · intro hDef
    exact hNegApp hDef.1

/-- Open subterminal `U_⋆ : BZ2BotObj ⥤ Type` (`U_⋆(.bot) = PEmpty`, `U_⋆(.star) = PUnit`),
whose open slice is equivalent to `Set^{ℤ/2ℤ}`. -/
def bz2BotOpenSubterminal : BZ2BotObj ⥤ Type where
  obj
    | .bot => PEmpty
    | .star => PUnit
  map {X Y} f x :=
    match X, Y with
    | .bot, _ => PEmpty.elim x
    | .star, .bot => PEmpty.elim f
    | .star, .star => ()
  map_id X := funext fun x ↦ by
    cases X
    · exact PEmpty.elim x
    · rcases x with ⟨⟩; rfl
  map_comp {X Y Z} f g := funext fun x ↦ by
    cases X <;> cases Y <;> cases Z <;>
      first | exact PEmpty.elim x | exact PEmpty.elim f | exact PEmpty.elim g | rfl

theorem isSubterminalPresheaf_bz2BotOpenSubterminal :
    IsSubterminalPresheaf bz2BotOpenSubterminal := by
  intro c
  cases c
  · exact ⟨fun x ↦ PEmpty.elim x⟩
  · exact ⟨fun _ _ ↦ rfl⟩

/-- Extend a `ℤ/2ℤ`-set `A : TwoGroupCat ⥤ Type` by empty fiber at `.bot` into `BZ2BotObj ⥤ Type`,
identifying `Set^{ℤ/2ℤ}` with the open slice over `bz2BotOpenSubterminal`. -/
def bz2BotExtendFromStar (A : TwoGroupCat ⥤ Type) : BZ2BotObj ⥤ Type where
  obj
    | .bot => PEmpty
    | .star => A.obj (SingleObj.star TwoGroup)
  map {X Y} f x :=
    match X, Y with
    | .bot, _ => PEmpty.elim x
    | .star, .bot => PEmpty.elim f
    | .star, .star => A.map (f : SingleObj.star TwoGroup ⟶ SingleObj.star TwoGroup) x
  map_id X := funext fun x ↦ by
    cases X
    · exact PEmpty.elim x
    · exact congrFun (A.map_id (SingleObj.star TwoGroup)) x
  map_comp {X Y Z} f g := funext fun x ↦ by
    cases X <;> cases Y <;> cases Z <;>
      first
      | exact PEmpty.elim x
      | exact PEmpty.elim f
      | exact PEmpty.elim g
      | exact congrFun
          (A.map_comp (f : SingleObj.star TwoGroup ⟶ SingleObj.star TwoGroup)
            (g : SingleObj.star TwoGroup ⟶ SingleObj.star TwoGroup)) x

/-- Restriction functor from `BZ2BotObj ⥤ Type` to the open subtopos `TwoGroupCat ⥤ Type`
(`Set^{ℤ/2ℤ}`). -/
def bz2BotRestrictToStar (F : BZ2BotObj ⥤ Type) : TwoGroupCat ⥤ Type where
  obj _ := F.obj .star
  map {X Y} f x := F.map (f : BZ2BotObj.star ⟶ BZ2BotObj.star) x
  map_id _ := funext fun x ↦ congrFun (F.map_id .star) x
  map_comp {X Y Z} f g := funext fun x ↦ by
    let f' : BZ2BotObj.star ⟶ BZ2BotObj.star := f
    let g' : BZ2BotObj.star ⟶ BZ2BotObj.star := g
    exact congrFun (F.map_comp f' g') x

theorem bz2BotRestrictToStar_extend (A : TwoGroupCat ⥤ Type) :
    bz2BotRestrictToStar (bz2BotExtendFromStar A) = A :=
  CategoryTheory.Functor.hext
    (fun X ↦ by rcases X with ⟨⟩; rfl)
    (fun X Y _ ↦ by rcases X with ⟨⟩; rcases Y with ⟨⟩; rfl)

/-- Global sections over `BZ2BotObj` evaluate via the unique arrow `.bot ⟶ .star`, so `Proj₁`
holds constructively! -/
theorem catPresheafProj1_bz2Bot : CatPresheafProj1 BZ2BotObj := by
  intro X _ he
  obtain ⟨x₀, _⟩ := he .bot ()
  let toStar : BZ2BotObj.bot ⟶ BZ2BotObj.star := ()
  refine ⟨
    { app := fun c _ ↦ match c with
        | .bot => x₀
        | .star => X.map toStar x₀
      naturality := fun c d h ↦ funext fun _ ↦ by
        cases c <;> cases d
        · rcases h with ⟨⟩
          exact (congrFun (X.map_id .bot) x₀).symm
        · rcases h with ⟨⟩
          rfl
        · exact PEmpty.elim h
        · exact congrFun (X.map_comp toStar h) x₀ },
    fun _ _ ↦ rfl⟩

/-- `Set^{ℤ/2ℤ}` (`TwoGroupCat`) fails `Proj₁` via the regular `ℤ/2ℤ`-torsor (Choice-free!). -/
theorem not_catPresheafProj1_twoGroupCat : ¬ CatPresheafProj1 TwoGroupCat := by
  intro hP
  let star : TwoGroupCat := SingleObj.star TwoGroup
  let X := coyonedaPresheaf TwoGroupCat star
  let e : NatTrans X (terminalPresheaf TwoGroupCat) :=
    { app := fun _ _ ↦ (), naturality := fun _ _ _ ↦ rfl }
  have he : IsPointwiseSurjective e := fun _ _ ↦ ⟨(1 : TwoGroup), rfl⟩
  rcases hP e he with ⟨s, _⟩
  let neg : star ⟶ star := (⟨true⟩ : TwoGroup)
  let y : TwoGroup := s.app star ()
  have hnat := (congrFun (s.naturality neg) ()).symm
  change (⟨true⟩ : TwoGroup) * y = y at hnat
  rcases y with ⟨_ | _⟩
  · exact absurd hnat (by decide)
  · exact absurd hnat (by decide)

theorem not_catPresheafProjSub_twoGroupCat : ¬ CatPresheafProjSub TwoGroupCat :=
  fun h ↦ not_catPresheafProj1_twoGroupCat (catPresheafProjSub_imp_proj1 h)

theorem not_catPresheafAC_twoGroupCat : ¬ CatPresheafAC TwoGroupCat :=
  fun h ↦ not_catPresheafProjSub_twoGroupCat (catPresheafAC_imp_projSub h)

/-- Over `(B(ℤ/2ℤ))_⊥`, the open subterminal `U_⋆` recovers the regular `ℤ/2ℤ`-torsor with no
section, refuting `ProjSub` (`CatPresheafProjSub BZ2BotObj`). Choice-free! -/
theorem not_catPresheafProjSub_bz2Bot : ¬ CatPresheafProjSub BZ2BotObj := by
  intro hSub
  let X := bz2BotExtendFromStar (coyonedaPresheaf TwoGroupCat (SingleObj.star TwoGroup))
  let e : NatTrans X bz2BotOpenSubterminal :=
    { app := fun c x ↦ match c with
        | .bot => PEmpty.elim x
        | .star => ()
      naturality := fun c d h ↦ funext fun x ↦ by
        cases c <;> cases d <;> first | exact PEmpty.elim x | exact PEmpty.elim h | rfl }
  have he : IsPointwiseSurjective e := by
    intro c u
    cases c
    · exact PEmpty.elim u
    · exact ⟨(1 : TwoGroup), rfl⟩
  rcases hSub isSubterminalPresheaf_bz2BotOpenSubterminal e he with ⟨s, _⟩
  let neg : BZ2BotObj.star ⟶ BZ2BotObj.star := (⟨true⟩ : TwoGroup)
  let y : TwoGroup := s.app .star ()
  have hnat := (congrFun (s.naturality neg) ()).symm
  change (⟨true⟩ : TwoGroup) * y = y at hnat
  rcases y with ⟨_ | _⟩
  · exact absurd hnat (by decide)
  · exact absurd hnat (by decide)

/-- Diaconescu pushout over `U_⋆` refutes internal choice `CatPresheafIAC BZ2BotObj`:
`(B(ℤ/2ℤ))_⊥` is non-Boolean (`∅ < U_⋆ < 1`) and drops `IAC`. Choice-free! -/
theorem not_catPresheafIAC_bz2Bot : ¬ CatPresheafIAC BZ2BotObj := by
  intro hIAC
  let X : BZ2BotObj ⥤ Type :=
    { obj := fun _ ↦ Bool, map := fun _ x ↦ x, map_id := fun _ ↦ rfl, map_comp := fun _ _ ↦ rfl }
  let Y : BZ2BotObj ⥤ Type :=
    { obj := fun c ↦ match c with | .bot => Bool | .star => PUnit
      map := fun {c d} h x ↦ match c, d with
        | .bot, .bot => x
        | .bot, .star => ()
        | .star, .bot => PEmpty.elim h
        | .star, .star => ()
      map_id := fun c ↦ funext fun x ↦ by
        cases c
        · rfl
        · rcases x with ⟨⟩; rfl
      map_comp := fun {c d e'} h₁ h₂ ↦ funext fun x ↦ by
        cases c <;> cases d <;> cases e' <;>
          first | exact PEmpty.elim h₁ | exact PEmpty.elim h₂ | rfl }
  let e : NatTrans X Y :=
    { app := fun c x ↦ match c with | .bot => x | .star => ()
      naturality := fun c d h ↦ funext fun x ↦ by
        cases c <;> cases d <;> first | exact PEmpty.elim h | rfl }
  have he : IsPointwiseSurjective e := fun c y ↦ by
    cases c
    · exact ⟨y, rfl⟩
    · exact ⟨false, rfl⟩
  let g : NatTrans (prodPresheaf (coyonedaPresheaf BZ2BotObj .bot) Y) Y :=
    { app := fun _ p ↦ p.2, naturality := fun _ _ _ ↦ rfl }
  rcases hIAC Y e he .bot g with ⟨f, hf⟩
  have hFalseEq := hf .bot ((𝟙 BZ2BotObj.bot, false) :
    (prodPresheaf (coyonedaPresheaf BZ2BotObj .bot) Y).obj .bot)
  have hTrueEq := hf .bot ((𝟙 BZ2BotObj.bot, true) :
    (prodPresheaf (coyonedaPresheaf BZ2BotObj .bot) Y).obj .bot)
  let toStar : BZ2BotObj.bot ⟶ BZ2BotObj.star := ()
  have hnatF := (congrFun (f.naturality toStar) (𝟙 BZ2BotObj.bot, false)).symm
  have hnatT := (congrFun (f.naturality toStar) (𝟙 BZ2BotObj.bot, true)).symm
  change f.app .bot (𝟙 BZ2BotObj.bot, false) = f.app .star ((), ()) at hnatF
  change f.app .bot (𝟙 BZ2BotObj.bot, true) = f.app .star ((), ()) at hnatT
  have hfbot : f.app .bot (𝟙 BZ2BotObj.bot, false) = f.app .bot (𝟙 BZ2BotObj.bot, true) :=
    hnatF.trans hnatT.symm
  have hft : (false : Bool) = true := hFalseEq.symm.trans (by rw [hfbot]; exact hTrueEq)
  exact Bool.false_ne_true hft

/-- **Freyd-Cover Dogma-Banishment Witness (`freydCover_dogma_banishment`):**
On the genuine 2-object Freyd cover `(B(ℤ/2ℤ))_⊥` (`BZ2BotObj`):
- `Proj₁` holds globally (`CatPresheafProj1 BZ2BotObj`),
- `ProjSub` fails over the open subterminal `U_⋆` (`¬ CatPresheafProjSub BZ2BotObj`),
- `IAC` fails (`¬ CatPresheafIAC BZ2BotObj`), so `(B(ℤ/2ℤ))_⊥ ∈ Mod(IAC → AC)` vacuously while its
  open slice `Set^{ℤ/2ℤ}` (`TwoGroupCat`) satisfies `IAC` yet fails `Proj₁` and `AC`.
Zero `Classical.choice`! -/
theorem freydCover_dogma_banishment :
    CatPresheafProj1 BZ2BotObj ∧
      ¬ CatPresheafProjSub BZ2BotObj ∧
      ¬ CatPresheafIAC BZ2BotObj ∧
      ¬ CatPresheafProj1 TwoGroupCat :=
  ⟨catPresheafProj1_bz2Bot, not_catPresheafProjSub_bz2Bot, not_catPresheafIAC_bz2Bot,
    not_catPresheafProj1_twoGroupCat⟩

/-! ### Finite Pareto Schism on Genuine Presheaf Topoi -/

/-- Finite witness suite of four canonical presheaf topoi grounding the `IAC ∩ · ⊆ AC` split. -/
inductive TestTopos : Type
  | setTopos
  | setZ2
  | setM1
  | setVPoset
  deriving DecidableEq

/-- The three kataphatic probes `𝒫` comparing `IAC`, `ProjSub` (`= SS`), and `Localic`. -/
inductive ChoiceProbe : Type
  | IAC
  | ProjSub
  | Localic
  deriving DecidableEq

/-- Underlying small site category of each witness presheaf topos. -/
def testSite : TestTopos → Type
  | .setTopos => PUnitCat
  | .setZ2 => TwoGroupCat
  | .setM1 => M1Cat
  | .setVPoset => VPosetOpCat

instance (t : TestTopos) : SmallCategory (testSite t) :=
  match t with
  | .setTopos => inferInstanceAs (SmallCategory PUnitCat)
  | .setZ2 => inferInstanceAs (SmallCategory TwoGroupCat)
  | .setM1 => inferInstanceAs (SmallCategory M1Cat)
  | .setVPoset => inferInstanceAs (SmallCategory VPosetOpCat)

/-! #### 4-Element V-Maker Cover Refuting `IAC` on `M1Cat` (`Set^{ℳ₁}`) -/

private inductive M1VBase : Type
  | x1
  | x2
  | y
  deriving DecidableEq

private def m1VBaseAct : M1Monoid → M1VBase → M1VBase
  | ⟨true⟩, s => s
  | ⟨false⟩, _ => .y

private inductive M1VTotal : Type
  | x1_0
  | x2_1
  | y0
  | y1
  deriving DecidableEq

private def m1VTotalAct : M1Monoid → M1VTotal → M1VTotal
  | ⟨true⟩, s => s
  | ⟨false⟩, .x1_0 => .y0
  | ⟨false⟩, .y0 => .y0
  | ⟨false⟩, .x2_1 => .y1
  | ⟨false⟩, .y1 => .y1

private def m1VProj : M1VTotal → M1VBase
  | .x1_0 => .x1
  | .x2_1 => .x2
  | .y0 => .y
  | .y1 => .y

private def m1VBaseFunctor : M1Cat ⥤ Type where
  obj _ := M1VBase
  map m s := m1VBaseAct m s
  map_id _ := rfl
  map_comp m₁ m₂ := funext fun s ↦ by
    rcases m₁ with ⟨_ | _⟩ <;> rcases m₂ with ⟨_ | _⟩ <;> cases s <;> rfl

private def m1VTotalFunctor : M1Cat ⥤ Type where
  obj _ := M1VTotal
  map m s := m1VTotalAct m s
  map_id _ := rfl
  map_comp m₁ m₂ := funext fun s ↦ by
    rcases m₁ with ⟨_ | _⟩ <;> rcases m₂ with ⟨_ | _⟩ <;> cases s <;> rfl

/-- Constructive 4-element V-maker counterexample proving `¬ CatPresheafIAC M1Cat`. Zero
`Classical.choice`! -/
theorem not_catPresheafIAC_m1Cat : ¬ CatPresheafIAC M1Cat := by
  intro hIAC
  let star : M1Cat := SingleObj.star M1Monoid
  let e : NatTrans m1VTotalFunctor m1VBaseFunctor :=
    { app := fun _ t ↦ m1VProj t
      naturality := fun _ _ m ↦ funext fun t ↦ by
        rcases m with ⟨_ | _⟩ <;> cases t <;> rfl }
  have he : IsPointwiseSurjective e := by
    intro _ b
    cases b
    · exact ⟨.x1_0, rfl⟩
    · exact ⟨.x2_1, rfl⟩
    · exact ⟨.y0, rfl⟩
  let g : NatTrans (prodPresheaf (coyonedaPresheaf M1Cat star) m1VBaseFunctor) m1VBaseFunctor :=
    { app := fun _ p ↦ p.2, naturality := fun _ _ _ ↦ rfl }
  rcases hIAC m1VBaseFunctor e he star g with ⟨f, hf⟩
  let e0 : star ⟶ star := (⟨false⟩ : M1Monoid)
  have hn1 := (congrFun (f.naturality e0) ((𝟙 star, M1VBase.x1) :
    (prodPresheaf (coyonedaPresheaf M1Cat star) m1VBaseFunctor).obj star)).symm
  have hn2 := (congrFun (f.naturality e0) ((𝟙 star, M1VBase.x2) :
    (prodPresheaf (coyonedaPresheaf M1Cat star) m1VBaseFunctor).obj star)).symm
  change m1VTotalAct e0 (f.app star (𝟙 star, .x1)) = f.app star (e0, .y) at hn1
  change m1VTotalAct e0 (f.app star (𝟙 star, .x2)) = f.app star (e0, .y) at hn2
  have hp1 : m1VProj (f.app star (𝟙 star, .x1)) = .x1 := hf star (𝟙 star, .x1)
  have hp2 : m1VProj (f.app star (𝟙 star, .x2)) = .x2 := hf star (𝟙 star, .x2)
  have hf1 : m1VTotalAct e0 (f.app star (𝟙 star, .x1)) = .y0 := by
    cases h : f.app star (𝟙 star, .x1)
    · rfl
    all_goals rw [h] at hp1; cases hp1
  have hf2 : m1VTotalAct e0 (f.app star (𝟙 star, .x2)) = .y1 := by
    cases h : f.app star (𝟙 star, .x2)
    · rw [h] at hp2; cases hp2
    · rfl
    all_goals rw [h] at hp2; cases hp2
  have hy : (M1VTotal.y0 : M1VTotal) = .y1 := hf1.symm.trans (hn1.trans (hn2.symm.trans hf2))
  cases hy

private def vPosetOpBoolObj : VPosetOpCat → Type
  | .op .a => Bool
  | .op .b => Bool
  | .op .c => PUnit

private def vPosetOpBoolMap :
    ∀ ⦃p q : VPosetOpCat⦄, (p ⟶ q) → vPosetOpBoolObj p → vPosetOpBoolObj q
  | .op .a, .op .a, _, x => x
  | .op .b, .op .b, _, x => x
  | .op .c, .op .c, _, _ => ()
  | .op .a, .op .c, _, _ => ()
  | .op .b, .op .c, _, _ => ()
  | .op .a, .op .b, h, _ => False.elim h.unop.le
  | .op .b, .op .a, h, _ => False.elim h.unop.le
  | .op .c, .op .a, h, _ => False.elim h.unop.le
  | .op .c, .op .b, h, _ => False.elim h.unop.le

private def vPosetOpBoolFunctor : VPosetOpCat ⥤ Type where
  obj := vPosetOpBoolObj
  map {p q} h x := vPosetOpBoolMap h x
  map_id p := funext fun x ↦ by
    rcases p with ⟨_ | _ | _⟩
    · rcases x with ⟨⟩; rfl
    · rfl
    · rfl
  map_comp {p q r} f g := funext fun x ↦ by
    rcases p with ⟨_ | _ | _⟩ <;> rcases q with ⟨_ | _ | _⟩ <;> rcases r with ⟨_ | _ | _⟩ <;>
      first | exact False.elim f.unop.le | exact False.elim g.unop.le | rfl

/-- Constructive Diaconescu pushout proving `¬ CatPresheafIAC VPosetOpCat`. Zero `Classical.choice`!
-/
theorem not_catPresheafIAC_vPosetOpCat : ¬ CatPresheafIAC VPosetOpCat := by
  intro hIAC
  let X : VPosetOpCat ⥤ Type :=
    { obj := fun _ ↦ Bool, map := fun _ x ↦ x, map_id := fun _ ↦ rfl, map_comp := fun _ _ ↦ rfl }
  let e : NatTrans X vPosetOpBoolFunctor :=
    { app := fun p x ↦ match p with | .op .c => () | .op .a => x | .op .b => x
      naturality := fun p q h ↦ funext fun x ↦ by
        rcases p with ⟨_ | _ | _⟩ <;> rcases q with ⟨_ | _ | _⟩ <;>
          first | exact False.elim h.unop.le | rfl }
  have he : IsPointwiseSurjective e := fun p y ↦ by
    rcases p with ⟨_ | _ | _⟩
    · exact ⟨false, rfl⟩
    · exact ⟨y, rfl⟩
    · exact ⟨y, rfl⟩
  let c₀ : VPosetOpCat := .op .a
  let g : NatTrans (prodPresheaf (coyonedaPresheaf VPosetOpCat c₀) vPosetOpBoolFunctor)
      vPosetOpBoolFunctor :=
    { app := fun _ p ↦ p.2, naturality := fun _ _ _ ↦ rfl }
  rcases hIAC vPosetOpBoolFunctor e he c₀ g with ⟨f, hf⟩
  have hFalseEq := hf c₀ (𝟙 c₀, false)
  have hTrueEq := hf c₀ (𝟙 c₀, true)
  let k : c₀ ⟶ .op .c := Opposite.op (homOfLE (show VPoset.c ≤ .a from trivial))
  have hnatF := (congrFun (f.naturality k) (𝟙 c₀, false)).symm
  have hnatT := (congrFun (f.naturality k) (𝟙 c₀, true)).symm
  change f.app c₀ (𝟙 c₀, false) = f.app (.op .c) (𝟙 c₀ ≫ k, ()) at hnatF
  change f.app c₀ (𝟙 c₀, true) = f.app (.op .c) (𝟙 c₀ ≫ k, ()) at hnatT
  have hfbot : f.app c₀ (𝟙 c₀, false) = f.app c₀ (𝟙 c₀, true) := hnatF.trans hnatT.symm
  have hft : (false : Bool) = true := hFalseEq.symm.trans (by rw [hfbot]; exact hTrueEq)
  exact Bool.false_ne_true hft

theorem catPresheafLocalic_punitCat : CatPresheafLocalic PUnitCat := by
  intro X c x
  refine ⟨coyonedaPresheaf PUnitCat c, fun d ↦ ⟨fun u v ↦ ?_⟩,
    { app := fun _ h ↦ X.map h x
      naturality := fun _ _ k ↦ funext fun h ↦ congrFun (X.map_comp h k) x },
    𝟙 c, congrFun (X.map_id c) x⟩
  rcases u with ⟨⟩; rcases v with ⟨⟩; rfl

theorem catPresheafLocalic_vPosetOpCat : CatPresheafLocalic VPosetOpCat := by
  intro X c x
  refine ⟨coyonedaPresheaf VPosetOpCat c, fun d ↦ ⟨fun u v ↦ ?_⟩,
    { app := fun _ h ↦ X.map h x
      naturality := fun _ _ k ↦ funext fun h ↦ congrFun (X.map_comp h k) x },
    𝟙 c, congrFun (X.map_id c) x⟩
  cases u
  cases v
  congr 1
  exact Subsingleton.elim _ _

theorem not_catPresheafLocalic_twoGroupCat : ¬ CatPresheafLocalic TwoGroupCat := by
  intro hLoc
  let star : TwoGroupCat := SingleObj.star TwoGroup
  rcases hLoc (coyonedaPresheaf TwoGroupCat star) star (1 : TwoGroup) with ⟨U, hU, f, u, hfu⟩
  let neg : star ⟶ star := (⟨true⟩ : TwoGroup)
  let y : TwoGroup := f.app star u
  have hy : y = 1 := hfu
  have hnat := congrFun (f.naturality neg) u
  have hu : U.map neg u = u := (hU star).elim _ u
  change f.app star (U.map neg u) = (⟨true⟩ : TwoGroup) * y at hnat
  rw [hu] at hnat
  change y = (⟨true⟩ : TwoGroup) * y at hnat
  rw [hy, mul_one] at hnat
  exact absurd hnat (by decide)

theorem not_catPresheafLocalic_m1Cat : ¬ CatPresheafLocalic M1Cat := by
  intro hLoc
  let star : M1Cat := SingleObj.star M1Monoid
  rcases hLoc (coyonedaPresheaf M1Cat star) star (1 : M1Monoid) with ⟨U, hU, f, u, hfu⟩
  let e0 : star ⟶ star := (⟨false⟩ : M1Monoid)
  let y : M1Monoid := f.app star u
  have hy : y = 1 := hfu
  have hnat := congrFun (f.naturality e0) u
  have hu : U.map e0 u = u := (hU star).elim _ u
  change f.app star (U.map e0 u) = (⟨false⟩ : M1Monoid) * y at hnat
  rw [hu] at hnat
  change y = (⟨false⟩ : M1Monoid) * y at hnat
  rw [hy, mul_one] at hnat
  exact absurd hnat (by decide)

theorem not_catPresheafProj1_vPosetOpCat : ¬ CatPresheafProj1 VPosetOpCat := by
  intro hP
  let F : VPosetOpCat ⥤ Type :=
    { obj := fun p ↦ vPosetCoprod.obj p.unop
      map := fun f x ↦ vPosetCoprod.res f.unop.le x
      map_id := fun p ↦ funext fun x ↦ vPosetCoprod.res_refl p.unop x
      map_comp := fun {p q r} f g ↦ funext fun x ↦
        (vPosetCoprod.res_trans g.unop.le f.unop.le x).symm }
  let e : NatTrans F (terminalPresheaf VPosetOpCat) :=
    { app := fun _ _ ↦ (), naturality := fun _ _ _ ↦ rfl }
  have he : IsPointwiseSurjective e := by
    intro p _
    rcases p with ⟨_ | _ | _⟩
    · exact ⟨false, rfl⟩
    · exact ⟨(), rfl⟩
    · exact ⟨(), rfl⟩
  rcases hP e he with ⟨s, _⟩
  let ka : Opposite.op VPoset.a ⟶ .op .c := Opposite.op (homOfLE (show VPoset.c ≤ .a from trivial))
  let kb : Opposite.op VPoset.b ⟶ .op .c := Opposite.op (homOfLE (show VPoset.c ≤ .b from trivial))
  have ha := (congrFun (s.naturality ka) ()).symm
  have hb := (congrFun (s.naturality kb) ()).symm
  change false = s.app (.op .c) () at ha
  change true = s.app (.op .c) () at hb
  exact Bool.false_ne_true (ha.trans hb.symm)

theorem not_catPresheafProjSub_vPosetOpCat : ¬ CatPresheafProjSub VPosetOpCat :=
  fun h ↦ not_catPresheafProj1_vPosetOpCat (catPresheafProjSub_imp_proj1 h)

/-- Classical positive witness over `Type`: `Set` (`PUnitCat ⥤ Type`) satisfies `CatPresheafAC`. -/
theorem catPresheafAC_punitCat : CatPresheafAC PUnitCat := by
  intro X Y e he
  refine ⟨
    { app := fun c y ↦ match c with
        | .star => Classical.choose (he .star y)
      naturality := fun c d h ↦ funext fun y ↦ by
        cases c
        cases d
        rcases h with ⟨⟩
        have hy : Y.map (𝟙 PUnitCat.star) y = y := congrFun (Y.map_id PUnitCat.star) y
        have hx : ∀ x : X.obj PUnitCat.star, X.map (𝟙 PUnitCat.star) x = x :=
          congrFun (X.map_id PUnitCat.star)
        change Classical.choose (he .star (Y.map (𝟙 PUnitCat.star) y)) =
          X.map (𝟙 PUnitCat.star) (Classical.choose (he .star y))
        rw [hy, hx] },
    fun c y ↦ by cases c; exact Classical.choose_spec (he .star y)⟩

theorem catPresheafIAC_punitCat : CatPresheafIAC PUnitCat :=
  catPresheafAC_imp_iac catPresheafAC_punitCat

theorem catPresheafProjSub_punitCat : CatPresheafProjSub PUnitCat :=
  catPresheafAC_imp_projSub catPresheafAC_punitCat

private def twoGroupHomInv {a b : TwoGroupCat} (u : a ⟶ b) : b ⟶ a :=
  @Inv.inv TwoGroup _ u

/-- Classical positive witness over `Type`: `Set^{ℤ/2ℤ}` (`TwoGroupCat ⥤ Type`) satisfies `IAC`
because every morphism in `TwoGroupCat` is an isomorphism (free transitive equivariant extension
from `u = 1`). -/
theorem catPresheafIAC_twoGroupCat : CatPresheafIAC TwoGroupCat := by
  intro X Y Z e he c g
  rcases c with ⟨⟩
  let star : TwoGroupCat := SingleObj.star TwoGroup
  let s : Z.obj star → X.obj star := fun z ↦
    Classical.choose (he star (g.app star ((1 : TwoGroup), z)))
  refine ⟨
    { app := fun d p ↦ X.map p.1 (s (Z.map (twoGroupHomInv p.1) p.2))
      naturality := fun {d₁ d₂} k ↦ funext fun p ↦ by
        rcases d₁ with ⟨⟩
        rcases d₂ with ⟨⟩
        rcases p with ⟨u, z⟩
        let u' : TwoGroup := u
        let k' : TwoGroup := k
        have hcomp : twoGroupHomInv (u ≫ k) = k'⁻¹ * u'⁻¹ := by
          change (k' * u')⁻¹ = k'⁻¹ * u'⁻¹
          exact (mul_inv_rev k' u').trans (mul_comm u'⁻¹ k'⁻¹)
        have hkz : Z.map (twoGroupHomInv (u ≫ k)) (Z.map k z) =
            Z.map (twoGroupHomInv u) z := by
          let kiui : star ⟶ star := k'⁻¹ * u'⁻¹
          have hc1 : Z.map (k ≫ kiui) z = Z.map kiui (Z.map k z) := congrFun (Z.map_comp k kiui) z
          have hkinv : (k ≫ kiui : TwoGroup) = (twoGroupHomInv u : TwoGroup) := by
            change (k'⁻¹ * u'⁻¹) * k' = u'⁻¹
            rw [mul_comm k'⁻¹ u'⁻¹, mul_assoc, inv_mul_cancel, mul_one]
          rw [hcomp]
          exact hc1.symm.trans (congrArg (fun m : star ⟶ star ↦ Z.map m z) hkinv)
        change X.map (u ≫ k) (s (Z.map (twoGroupHomInv (u ≫ k)) (Z.map k z))) =
          X.map k (X.map u (s (Z.map (twoGroupHomInv u) z)))
        rw [hkz]
        exact congrFun (X.map_comp u k) (s (Z.map (twoGroupHomInv u) z)) },
    fun d p ↦ ?_⟩
  rcases d with ⟨⟩
  rcases p with ⟨u, z⟩
  let u' : TwoGroup := u
  have henat := congrFun (e.naturality (u : star ⟶ star)) (s (Z.map (twoGroupHomInv u) z))
  have hspec := Classical.choose_spec
    (he star (g.app star ((1 : TwoGroup), Z.map (twoGroupHomInv u) z)))
  change e.app star (X.map u (s (Z.map (twoGroupHomInv u) z))) =
    Y.map u (e.app star (s (Z.map (twoGroupHomInv u) z))) at henat
  have hgnat := (congrFun (g.naturality (u : star ⟶ star))
    (((1 : TwoGroup), Z.map (twoGroupHomInv u) z) :
      (prodPresheaf (coyonedaPresheaf TwoGroupCat star) Z).obj star)).symm
  change Y.map u (g.app star ((1 : TwoGroup), Z.map (twoGroupHomInv u) z)) =
    g.app star ((𝟙 star : star ⟶ star) ≫ u, Z.map u (Z.map (twoGroupHomInv u) z)) at hgnat
  have h1u : (𝟙 star : star ⟶ star) ≫ u = u := Category.id_comp u
  have huinv : twoGroupHomInv u ≫ u = 𝟙 star := by
    change u' * u'⁻¹ = 1
    exact mul_inv_cancel u'
  have hzu : Z.map u (Z.map (twoGroupHomInv u) z) = z := by
    have hc := congrFun (Z.map_comp (twoGroupHomInv u) u) z
    exact hc.symm.trans (by rw [huinv]; exact congrFun (Z.map_id star) z)
  calc
    e.app star (X.map u (s (Z.map (twoGroupHomInv u) z)))
      = Y.map u (e.app star (s (Z.map (twoGroupHomInv u) z))) := henat
    _ = Y.map u (g.app star ((1 : TwoGroup), Z.map (twoGroupHomInv u) z)) := by rw [hspec]
    _ = g.app star ((𝟙 star : star ⟶ star) ≫ u, Z.map u (Z.map (twoGroupHomInv u) z)) := hgnat
    _ = g.app star (u, z) := by rw [h1u, hzu]

/-- Separation of `IAC` and `AC` on `Set^{ℤ/2ℤ}` (`TwoGroupCat`): `IAC` holds while `AC` fails. -/
theorem twoGroupCat_iac_and_not_ac :
    CatPresheafIAC TwoGroupCat ∧ ¬ CatPresheafAC TwoGroupCat :=
  ⟨catPresheafIAC_twoGroupCat, not_catPresheafAC_twoGroupCat⟩

/-- Classical positive witness over `Type`: `Set^{ℳ₁}` (`M1Cat`) satisfies `ProjSub`. -/
theorem catPresheafProjSub_m1Cat : CatPresheafProjSub M1Cat := by
  intro U X hU e he
  let star : M1Cat := SingleObj.star M1Monoid
  let e0 : ∀ d : M1Cat, d ⟶ d := fun _ ↦ (⟨false⟩ : M1Monoid)
  let sApp : ∀ d : M1Cat, U.obj d → X.obj d := fun d u ↦
    X.map (e0 d) (Classical.choose (he d u))
  refine ⟨
    { app := sApp
      naturality := fun d₁ d₂ k ↦ funext fun u ↦ by
        rcases d₁ with ⟨⟩
        rcases d₂ with ⟨⟩
        change sApp star (U.map k u) = X.map k (sApp star u)
        rw [(hU star).elim (U.map k u) u]
        dsimp only [sApp]
        have hc := congrFun (X.map_comp (e0 star) k) (Classical.choose (he star u))
        have hm : e0 star ≫ k = e0 star := M1Monoid.ext (Bool.and_false k.val)
        rw [hm] at hc
        exact hc },
    fun d u ↦ by
      dsimp only [sApp]
      have henat := congrFun (e.naturality (e0 d)) (Classical.choose (he d u))
      have hspec := Classical.choose_spec (he d u)
      change e.app d (X.map (e0 d) (Classical.choose (he d u))) =
        U.map (e0 d) (e.app d (Classical.choose (he d u))) at henat
      rw [henat, hspec]
      exact (hU d).elim _ u⟩

/-- Uniform satisfaction relation `testToposSat t p` grounded directly in the categorical
presheaf properties `CatPresheafIAC`, `CatPresheafProjSub`, and `CatPresheafLocalic`. -/
def testToposSat (t : TestTopos) : ChoiceProbe → Prop
  | .IAC => CatPresheafIAC (testSite t)
  | .ProjSub => CatPresheafProjSub (testSite t)
  | .Localic => CatPresheafLocalic (testSite t)

/-- Honest conclusion predicate `Mod(AC)` (`CatPresheafAC`), strictly stronger than `ProjSub`
(`setM1 ∈ Ext(ProjSub) \ Mod(AC)`). -/
def testToposAC (t : TestTopos) : Prop :=
  CatPresheafAC (testSite t)

/-- Finite `DoctrinalPhilosophy TestTopos ChoiceProbe` for choice-residuum incomparability. -/
def choicePhilosophy : DoctrinalPhilosophy TestTopos ChoiceProbe where
  sat := testToposSat

/-- Strict separation of `concl = Mod(AC)` from `Ext(ProjSub)` on `TestTopos`, witnessed by `ℳ₁`. -/
theorem choiceConcl_ne_extProj :
    { t : TestTopos | testToposAC t } ≠ choicePhilosophy.extentOf {ChoiceProbe.ProjSub} := by
  intro heq
  have hm1_ext : TestTopos.setM1 ∈ choicePhilosophy.extentOf {ChoiceProbe.ProjSub} := by
    intro p hp
    rw [Set.mem_singleton_iff.mp hp]
    exact catPresheafProjSub_m1Cat
  rw [← heq] at hm1_ext
  exact not_catPresheafIAC_m1Cat (catPresheafAC_imp_iac hm1_ext)

/-- **Finite Pareto Schism (`pareto_incomparable_projSub_localic`):**
For the implication `(IAC ∩ · ⊆ Mod(AC))` over `TestTopos` (`concl = { t | testToposAC t }`,
strictly distinct from `Ext({ProjSub})`), both the Supports-Split class `Ext({ProjSub})` and the
Localic class `Ext({Localic})` sit on the minimal Pareto frontier `paretoFrontier`, and neither is
contained in the other (`ℳ₁ ∈ Ext({ProjSub}) \ Ext({Localic})` while
`V ∈ Ext({Localic}) \ Ext({ProjSub})`).

*(Axiom note: over `Type`, `catPresheafAC_punitCat`, `catPresheafIAC_twoGroupCat`, and
`catPresheafProjSub_m1Cat` legitimately invoke `Classical.choice`; all four negative witnesses
(`not_catPresheafAC_twoGroupCat`, `not_catPresheafIAC_m1Cat`, `not_catPresheafIAC_vPosetOpCat`,
`not_catPresheafProjSub_vPosetOpCat`) and `freydCover_dogma_banishment` remain Choice-free.)* -/
theorem pareto_incomparable_projSub_localic :
    let hyp := choicePhilosophy.extentOf {ChoiceProbe.IAC}
    let concl := { t : TestTopos | testToposAC t }
    let extProj := choicePhilosophy.extentOf {ChoiceProbe.ProjSub}
    let extLoc := choicePhilosophy.extentOf {ChoiceProbe.Localic}
    extProj ∈ choicePhilosophy.paretoFrontier hyp concl ∧
      extLoc ∈ choicePhilosophy.paretoFrontier hyp concl ∧
      ¬ (extProj ⊆ extLoc) ∧
      ¬ (extLoc ⊆ extProj) := by
  dsimp only
  have hClosed : ∀ Q : Set ChoiceProbe,
      choicePhilosophy.IsClosedExtent (choicePhilosophy.extentOf Q) := by
    intro Q
    apply Set.Subset.antisymm
    · intro x hx p hp
      exact hx p (fun y hy ↦ hy p hp)
    · exact choicePhilosophy.le_mooreClosure _
  have hAC_iff : ∀ t : TestTopos, testToposAC t ↔ t = .setTopos := fun t ↦ by
    cases t
    · exact ⟨fun _ ↦ rfl, fun _ ↦ catPresheafAC_punitCat⟩
    · exact ⟨fun h ↦ False.elim (not_catPresheafAC_twoGroupCat h), fun h ↦ by cases h⟩
    · exact ⟨fun h ↦ False.elim (not_catPresheafIAC_m1Cat (catPresheafAC_imp_iac h)),
        fun h ↦ by cases h⟩
    · exact ⟨fun h ↦ False.elim (not_catPresheafIAC_vPosetOpCat (catPresheafAC_imp_iac h)),
        fun h ↦ by cases h⟩
  have hIAC_iff : ∀ t : TestTopos,
      choicePhilosophy.sat t .IAC ↔ (t = .setTopos ∨ t = .setZ2) := fun t ↦ by
    cases t
    · exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ catPresheafIAC_punitCat⟩
    · exact ⟨fun _ ↦ Or.inr rfl, fun _ ↦ catPresheafIAC_twoGroupCat⟩
    · exact ⟨fun h ↦ False.elim (not_catPresheafIAC_m1Cat h), by rintro (h | h) <;> cases h⟩
    · exact ⟨fun h ↦ False.elim (not_catPresheafIAC_vPosetOpCat h), by rintro (h | h) <;> cases h⟩
  have hProj_iff : ∀ t : TestTopos,
      choicePhilosophy.sat t .ProjSub ↔ (t = .setTopos ∨ t = .setM1) := fun t ↦ by
    cases t
    · exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ catPresheafProjSub_punitCat⟩
    · exact ⟨fun h ↦ False.elim (not_catPresheafProjSub_twoGroupCat h),
        by rintro (h | h) <;> cases h⟩
    · exact ⟨fun _ ↦ Or.inr rfl, fun _ ↦ catPresheafProjSub_m1Cat⟩
    · exact ⟨fun h ↦ False.elim (not_catPresheafProjSub_vPosetOpCat h),
        by rintro (h | h) <;> cases h⟩
  have hLoc_iff : ∀ t : TestTopos,
      choicePhilosophy.sat t .Localic ↔ (t = .setTopos ∨ t = .setVPoset) := fun t ↦ by
    cases t
    · exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ catPresheafLocalic_punitCat⟩
    · exact ⟨fun h ↦ False.elim (not_catPresheafLocalic_twoGroupCat h),
        by rintro (h | h) <;> cases h⟩
    · exact ⟨fun h ↦ False.elim (not_catPresheafLocalic_m1Cat h),
        by rintro (h | h) <;> cases h⟩
    · exact ⟨fun _ ↦ Or.inr rfl, fun _ ↦ catPresheafLocalic_vPosetOpCat⟩
  have hParetoExt : ∀ E' : Set TestTopos,
      choicePhilosophy.IsClosedExtent E' →
      (choicePhilosophy.extentOf {ChoiceProbe.IAC} ∩ E' ⊆ { t : TestTopos | testToposAC t }) →
      .setZ2 ∉ E' := by
    intro E' _ hsub hz2
    have hmem : TestTopos.setZ2 ∈ choicePhilosophy.extentOf {ChoiceProbe.IAC} ∩ E' := by
      refine ⟨fun p hp ↦ ?_, hz2⟩
      rw [Set.mem_singleton_iff.mp hp]
      exact (hIAC_iff .setZ2).mpr (Or.inr rfl)
    have hcon := hsub hmem
    have heq := (hAC_iff .setZ2).mp hcon
    cases heq
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hClosed _, fun t ⟨_, htAC⟩ p hp ↦ ?_, fun t ⟨htIAC, htProj⟩ ↦ ?_,
      fun E' hCE' _ hsubE' hsub ↦ ?_⟩
    · rw [(hAC_iff t).mp htAC, Set.mem_singleton_iff.mp hp]
      exact (hProj_iff .setTopos).mpr (Or.inl rfl)
    · have h1 := (hIAC_iff t).mp (htIAC .IAC rfl)
      have h2 := (hProj_iff t).mp (htProj .ProjSub rfl)
      rcases h1 with rfl | rfl
      · exact (hAC_iff .setTopos).mpr rfl
      · rcases h2 with h | h <;> cases h
    · apply Set.Subset.antisymm _ hsub
      intro t htE'
      cases t
      · intro p hp
        rw [Set.mem_singleton_iff.mp hp]
        exact (hProj_iff .setTopos).mpr (Or.inl rfl)
      · exact False.elim (hParetoExt E' hCE' hsubE' htE')
      · intro p hp
        rw [Set.mem_singleton_iff.mp hp]
        exact (hProj_iff .setM1).mpr (Or.inr rfl)
      · exfalso
        have hm1 : TestTopos.setM1 ∈ E' := hsub (fun p hp ↦ by
          rw [Set.mem_singleton_iff.mp hp]; exact (hProj_iff .setM1).mpr (Or.inr rfl))
        have hz2cl : TestTopos.setZ2 ∈ choicePhilosophy.mooreClosure E' := by
          intro p hp
          cases p
          · exfalso
            have := (hIAC_iff .setM1).mp (hp .setM1 hm1)
            rcases this with h | h <;> cases h
          · exfalso
            have := (hProj_iff .setVPoset).mp (hp .setVPoset htE')
            rcases this with h | h <;> cases h
          · exfalso
            have := (hLoc_iff .setM1).mp (hp .setM1 hm1)
            rcases this with h | h <;> cases h
        rw [hCE'] at hz2cl
        exact hParetoExt E' hCE' hsubE' hz2cl
  · refine ⟨hClosed _, fun t ⟨_, htAC⟩ p hp ↦ ?_, fun t ⟨htIAC, htLoc⟩ ↦ ?_,
      fun E' hCE' _ hsubE' hsub ↦ ?_⟩
    · rw [(hAC_iff t).mp htAC, Set.mem_singleton_iff.mp hp]
      exact (hLoc_iff .setTopos).mpr (Or.inl rfl)
    · have h1 := (hIAC_iff t).mp (htIAC .IAC rfl)
      have h2 := (hLoc_iff t).mp (htLoc .Localic rfl)
      rcases h1 with rfl | rfl
      · exact (hAC_iff .setTopos).mpr rfl
      · rcases h2 with h | h <;> cases h
    · apply Set.Subset.antisymm _ hsub
      intro t htE'
      cases t
      · intro p hp
        rw [Set.mem_singleton_iff.mp hp]
        exact (hLoc_iff .setTopos).mpr (Or.inl rfl)
      · exact False.elim (hParetoExt E' hCE' hsubE' htE')
      · exfalso
        have hv : TestTopos.setVPoset ∈ E' := hsub (fun p hp ↦ by
          rw [Set.mem_singleton_iff.mp hp]; exact (hLoc_iff .setVPoset).mpr (Or.inr rfl))
        have hz2cl : TestTopos.setZ2 ∈ choicePhilosophy.mooreClosure E' := by
          intro p hp
          cases p
          · exfalso
            have := (hIAC_iff .setM1).mp (hp .setM1 htE')
            rcases this with h | h <;> cases h
          · exfalso
            have := (hProj_iff .setVPoset).mp (hp .setVPoset hv)
            rcases this with h | h <;> cases h
          · exfalso
            have := (hLoc_iff .setM1).mp (hp .setM1 htE')
            rcases this with h | h <;> cases h
        rw [hCE'] at hz2cl
        exact hParetoExt E' hCE' hsubE' hz2cl
      · intro p hp
        rw [Set.mem_singleton_iff.mp hp]
        exact (hLoc_iff .setVPoset).mpr (Or.inr rfl)
  · intro h
    have hm1 : TestTopos.setM1 ∈ choicePhilosophy.extentOf {ChoiceProbe.ProjSub} :=
      fun p hp ↦ by rw [Set.mem_singleton_iff.mp hp]; exact (hProj_iff .setM1).mpr (Or.inr rfl)
    have hdisj := (hLoc_iff .setM1).mp (h hm1 .Localic rfl)
    rcases hdisj with h1 | h1 <;> cases h1
  · intro h
    have hv : TestTopos.setVPoset ∈ choicePhilosophy.extentOf {ChoiceProbe.Localic} :=
      fun p hp ↦ by rw [Set.mem_singleton_iff.mp hp]; exact (hLoc_iff .setVPoset).mpr (Or.inr rfl)
    have hdisj := (hProj_iff .setVPoset).mp (h hv .ProjSub rfl)
    rcases hdisj with h1 | h1 <;> cases h1

/-! ### `ℳ₁`-Slice Lawvere–Tierney Topology Enumeration (`3^k · 2^m`) -/

/-- The 3-element subobject classifier `Ω_{ℳ₁} = {∅ < {e₁} < {e₁, 1₁}}` of `Set^{ℳ₁}`. -/
inductive OmegaM1 : Type
  | bot
  | mid
  | top
  deriving DecidableEq

namespace OmegaM1

instance : Fintype OmegaM1 where
  elems := {.bot, .mid, .top}
  complete x := by cases x <;> simp

/-- Linear order `bot ≤ mid ≤ top` on `Ω_{ℳ₁}`. -/
private def le : OmegaM1 → OmegaM1 → Prop
  | .bot, _ => True
  | .mid, .mid => True
  | .mid, .top => True
  | .top, .top => True
  | _, _ => False

private def decLE : (x y : OmegaM1) → Decidable (le x y)
  | .bot, _ => isTrue trivial
  | .mid, .mid => isTrue trivial
  | .mid, .top => isTrue trivial
  | .top, .top => isTrue trivial
  | .mid, .bot => isFalse False.elim
  | .top, .bot => isFalse False.elim
  | .top, .mid => isFalse False.elim

instance : LinearOrder OmegaM1 where
  le := le
  le_refl x := by cases x <;> trivial
  le_trans x y z hxy hyz := by cases x <;> cases y <;> cases z <;> simp_all [le]
  le_antisymm x y hxy hyx := by cases x <;> cases y <;> simp_all [le]
  le_total x y := by cases x <;> cases y <;> simp [le]
  toDecidableLE := decLE

/-- Canonical `e₁`-action on `Ω_{ℳ₁}` (`e₁ · ∅ = ∅`, `e₁ · {e₁} = 1`, `e₁ · 1 = 1`). -/
def eAct : OmegaM1 → OmegaM1
  | .bot => .bot
  | .mid => .top
  | .top => .top

end OmegaM1

/-- Lawvere–Tierney topology on the slice topos `(Set^{ℳ₁})/X` for an idempotent `ℳ₁`-set
`(X, ρ)` (`ρ ∘ ρ = ρ`), represented by its `ℳ₁`-equivariant modal operator
`j : X → Ω_{ℳ₁} → Ω_{ℳ₁}`. -/
@[ext]
structure M1SliceLTT {X : Type} (rho : X → X) : Type where
  /-- Fiberwise Lawvere–Tierney closure map at `x : X`. -/
  j : X → OmegaM1 → OmegaM1
  /-- Preserves truth `j_x(top) = top`. -/
  map_top : ∀ x : X, j x .top = .top
  /-- Preserves finite meets (equivalently monotone on the 3-element chain). -/
  monotone : ∀ x : X, Monotone (j x)
  /-- Idempotence `j_x(j_x(ω)) = j_x(ω)`. -/
  idem : ∀ (x : X) (ω : OmegaM1), j x (j x ω) = j x ω
  /-- `ℳ₁`-equivariance `j_{ρ(x)}(e₁ · ω) = e₁ · j_x(ω)`. -/
  equivariant : ∀ (x : X) (ω : OmegaM1), j (rho x) (OmegaM1.eAct ω) = OmegaM1.eAct (j x ω)

namespace M1SliceLTT

/-- Localic slice subtopoi kill all non-posetal `ℳ₁`-isotropy at fixed points `ρ(a) = a` by
enforcing `j_a({e₁}) = 1`. -/
def IsLocalic {X : Type} {rho : X → X} (J : M1SliceLTT rho) : Prop :=
  ∀ x : X, rho x = x → J.j x .mid = .top

/-- Non-localic slice subtopoi retain the 3-valued truth algebra at some fixed point `a`, and are
therefore simultaneously non-Boolean. -/
def IsNonBooleanAtFixed {X : Type} {rho : X → X} (J : M1SliceLTT rho) : Prop :=
  ∃ x : X, rho x = x ∧ J.j x .mid = .mid

private def fixedChoiceMap : Fin 3 → OmegaM1 → OmegaM1
  | ⟨0, _⟩, ω => ω
  | ⟨1, _⟩, .bot => .bot
  | ⟨1, _⟩, .mid => .top
  | ⟨1, _⟩, .top => .top
  | ⟨2, _⟩, _ => .top

private def nonFixedChoiceMap (baseBot : OmegaM1) (b : Bool) (ω : OmegaM1) : OmegaM1 :=
  match baseBot, b, ω with
  | .bot, false, ω => ω
  | .bot, true, .bot => .bot
  | .bot, true, .mid => .top
  | .bot, true, .top => .top
  | _, false, .bot => .mid
  | _, false, .mid => .mid
  | _, false, .top => .top
  | _, true, _ => .top

private lemma fixedChoiceMap_top (i : Fin 3) : fixedChoiceMap i .top = .top := by
  rcases i with ⟨_ | _ | _ | k, hk⟩
  · rfl
  · rfl
  · rfl
  · exfalso; omega

private lemma fixedChoiceMap_monotone (i : Fin 3) : Monotone (fixedChoiceMap i) := by
  intro ω₁ ω₂ hω
  rcases i with ⟨_ | _ | _ | k, hk⟩
  · exact hω
  · cases ω₁ <;> cases ω₂ <;> first | exact hω | exact trivial
  · exact le_rfl
  · exfalso; omega

private lemma fixedChoiceMap_idem (i : Fin 3) (ω : OmegaM1) :
    fixedChoiceMap i (fixedChoiceMap i ω) = fixedChoiceMap i ω := by
  rcases i with ⟨_ | _ | _ | k, hk⟩ <;> cases ω <;> first | rfl | (exfalso; omega)

private lemma fixedChoiceMap_eAct (i : Fin 3) (ω : OmegaM1) :
    fixedChoiceMap i (OmegaM1.eAct ω) = OmegaM1.eAct (fixedChoiceMap i ω) := by
  rcases i with ⟨_ | _ | _ | k, hk⟩ <;> cases ω <;> first | rfl | (exfalso; omega)

private lemma nonFixedChoiceMap_top (u : OmegaM1) (b : Bool) :
    nonFixedChoiceMap u b .top = .top := by
  cases u <;> cases b <;> rfl

private lemma nonFixedChoiceMap_monotone (u : OmegaM1) (b : Bool) :
    Monotone (nonFixedChoiceMap u b) := by
  intro ω₁ ω₂ hω
  cases u <;> cases b <;> cases ω₁ <;> cases ω₂ <;> first | exact hω | exact trivial

private lemma nonFixedChoiceMap_idem (u : OmegaM1) (b : Bool) (ω : OmegaM1) :
    nonFixedChoiceMap u b (nonFixedChoiceMap u b ω) = nonFixedChoiceMap u b ω := by
  cases u <;> cases b <;> cases ω <;> rfl

private lemma nonFixedChoiceMap_eAct (i : Fin 3) (b : Bool) (ω : OmegaM1) :
    fixedChoiceMap i (OmegaM1.eAct ω) =
      OmegaM1.eAct (nonFixedChoiceMap (fixedChoiceMap i .bot) b ω) := by
  rcases i with ⟨_ | _ | _ | k, hk⟩ <;> cases b <;> cases ω <;> first | rfl | (exfalso; omega)

/-- Classification of the 3 valid maps on a fixed point `a = ρ a` and the 2 valid extensions on a
non-fixed point `b ≠ ρ b`. -/
private lemma m1Slice_fixed_bot_cases {X : Type} {rho : X → X} (J : M1SliceLTT rho)
    {a : X} (ha : rho a = a) :
    (J.j a .bot = .bot ∧ J.j a .mid = .mid ∧ J.j a .top = .top) ∨
      (J.j a .bot = .bot ∧ J.j a .mid = .top ∧ J.j a .top = .top) ∨
      (J.j a .bot = .top ∧ J.j a .mid = .top ∧ J.j a .top = .top) := by
  have ht : J.j a .top = .top := J.map_top a
  have heq0 := J.equivariant a .bot
  have heq1 := J.equivariant a .mid
  rw [ha] at heq0 heq1
  change J.j a .top = OmegaM1.eAct (J.j a .mid) at heq1
  rw [ht] at heq1
  have hle : J.j a .bot ≤ J.j a .mid := J.monotone a (show OmegaM1.bot ≤ .mid from trivial)
  cases h0 : J.j a .bot <;> cases h1 : J.j a .mid
  all_goals simp only [h0, h1, OmegaM1.eAct] at heq0 heq1
  all_goals first
    | exact Or.inl ⟨rfl, rfl, ht⟩
    | exact Or.inr (Or.inl ⟨rfl, rfl, ht⟩)
    | exact Or.inr (Or.inr ⟨rfl, rfl, ht⟩)
    | exact absurd heq0 (by decide)
    | exact absurd heq1 (by decide)
    | exact False.elim (by rw [h0, h1] at hle; exact hle)

private lemma m1Slice_nonFixed_cases {X : Type} {rho : X → X}
    (hrho : ∀ x, rho (rho x) = rho x) (J : M1SliceLTT rho) (x : X) :
    (J.j (rho x) .bot = .bot ∧
      ((J.j x .bot = .bot ∧ J.j x .mid = .mid ∧ J.j x .top = .top) ∨
       (J.j x .bot = .bot ∧ J.j x .mid = .top ∧ J.j x .top = .top))) ∨
    (J.j (rho x) .bot = .top ∧
      ((J.j x .bot = .mid ∧ J.j x .mid = .mid ∧ J.j x .top = .top) ∨
       (J.j x .bot = .top ∧ J.j x .mid = .top ∧ J.j x .top = .top))) := by
  rcases m1Slice_fixed_bot_cases J (hrho x) with ⟨h0, _, _⟩ | ⟨h0, _, _⟩ | ⟨h0, _, _⟩
  all_goals
    have ht : J.j x .top = .top := J.map_top x
    have heq0 : J.j (rho x) .bot = OmegaM1.eAct (J.j x .bot) := J.equivariant x .bot
    have heq1 : J.j (rho x) .top = OmegaM1.eAct (J.j x .mid) := J.equivariant x .mid
    have hle01 : J.j x .bot ≤ J.j x .mid := J.monotone x (show OmegaM1.bot ≤ .mid from trivial)
    have hle12 : J.j x .mid ≤ J.j x .top := J.monotone x (show OmegaM1.mid ≤ .top from trivial)
    have hidem := J.idem x .bot
    have hfix1 : J.j (rho x) .top = .top := J.map_top (rho x)
    rw [h0] at heq0
    rw [hfix1] at heq1
  · left
    refine ⟨h0, ?_⟩
    cases hb : J.j x .bot <;> cases hm : J.j x .mid
    all_goals simp only [hb, hm, OmegaM1.eAct] at heq0 heq1
    all_goals first
      | exact Or.inl ⟨rfl, rfl, ht⟩
      | exact Or.inr ⟨rfl, rfl, ht⟩
      | exact absurd heq0 (by decide)
      | exact absurd heq1 (by decide)
  · left
    refine ⟨h0, ?_⟩
    cases hb : J.j x .bot <;> cases hm : J.j x .mid
    all_goals simp only [hb, hm, OmegaM1.eAct] at heq0 heq1
    all_goals first
      | exact Or.inl ⟨rfl, rfl, ht⟩
      | exact Or.inr ⟨rfl, rfl, ht⟩
      | exact absurd heq0 (by decide)
      | exact absurd heq1 (by decide)
  · right
    refine ⟨h0, ?_⟩
    cases hb : J.j x .bot <;> cases hm : J.j x .mid
    all_goals simp only [hb, hm, OmegaM1.eAct] at heq0 heq1 hidem
    all_goals first
      | exact Or.inl ⟨rfl, rfl, ht⟩
      | exact Or.inr ⟨rfl, rfl, ht⟩
      | exact absurd heq0 (by decide)
      | exact absurd hidem (by decide)
      | exact False.elim (by rw [hb, hm] at hle01; exact hle01)

/-- Explicit bijection classifying every `M1SliceLTT rho` by `Fin 3` on fixed points `ρ(a) = a` and
`Bool` on non-fixed points `b ≠ ρ(b)`. -/
def equivProd {X : Type} [DecidableEq X] {rho : X → X} (hrho : ∀ x, rho (rho x) = rho x) :
    M1SliceLTT rho ≃ (({ x : X // rho x = x } → Fin 3) × ({ x : X // rho x ≠ x } → Bool)) where
  toFun J :=
    (fun a ↦ match J.j a.1 .bot, J.j a.1 .mid with
      | .bot, .mid => 0
      | .bot, .top => 1
      | _, _ => 2,
     fun b ↦ decide (J.j b.1 .mid = .top))
  invFun p :=
    { j := fun x ω ↦
        if hx : rho x = x then fixedChoiceMap (p.1 ⟨x, hx⟩) ω
        else nonFixedChoiceMap ((fixedChoiceMap (p.1 ⟨rho x, hrho x⟩)) .bot) (p.2 ⟨x, hx⟩) ω
      map_top := fun x ↦ by
        by_cases hx : rho x = x
        · simp only [dif_pos hx]; exact fixedChoiceMap_top _
        · simp only [dif_neg hx]; exact nonFixedChoiceMap_top _ _
      monotone := fun x _ _ hω ↦ by
        by_cases hx : rho x = x
        · simp only [dif_pos hx]; exact fixedChoiceMap_monotone _ hω
        · simp only [dif_neg hx]; exact nonFixedChoiceMap_monotone _ _ hω
      idem := fun x ω ↦ by
        by_cases hx : rho x = x
        · simp only [dif_pos hx]; exact fixedChoiceMap_idem _ _
        · simp only [dif_neg hx]; exact nonFixedChoiceMap_idem _ _ _
      equivariant := fun x ω ↦ by
        by_cases hx : rho x = x
        · have hxx : rho (rho x) = rho x := hrho x
          rw [dif_pos hxx, dif_pos hx]
          have hsub : (⟨rho x, hxx⟩ : { y : X // rho y = y }) = ⟨x, hx⟩ := Subtype.ext hx
          rw [hsub]
          exact fixedChoiceMap_eAct _ _
        · have hrx : rho (rho x) = rho x := hrho x
          simp only [dif_neg hx, dif_pos hrx]
          exact nonFixedChoiceMap_eAct _ _ _ }
  left_inv J := by
    apply M1SliceLTT.ext
    funext x ω
    by_cases hx : rho x = x
    · simp only [dif_pos hx]
      rcases m1Slice_fixed_bot_cases J hx with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
      · cases ω <;> simp [h0, h1, h2, fixedChoiceMap]
      · cases ω <;> simp [h0, h1, h2, fixedChoiceMap]
      · cases ω <;> simp [h0, h1, h2, fixedChoiceMap]
    · simp only [dif_neg hx]
      have hrx : rho (rho x) = rho x := hrho x
      rcases m1Slice_fixed_bot_cases J hrx with ⟨hb0, hb1, _⟩ | ⟨hb0, hb1, _⟩ | ⟨hb0, hb1, _⟩
      all_goals
        rcases m1Slice_nonFixed_cases hrho J x with
          ⟨hfb, ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩⟩ | ⟨hfb, ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩⟩
        · all_goals try (rw [hb0] at hfb; cases hfb)
          all_goals cases ω <;> simp [hb0, hb1, h0, h1, h2, fixedChoiceMap, nonFixedChoiceMap]
        · all_goals try (rw [hb0] at hfb; cases hfb)
          all_goals cases ω <;> simp [hb0, hb1, h0, h1, h2, fixedChoiceMap, nonFixedChoiceMap]
        · all_goals try (rw [hb0] at hfb; cases hfb)
          all_goals cases ω <;> simp [hb0, hb1, h0, h1, h2, fixedChoiceMap, nonFixedChoiceMap]
        · all_goals try (rw [hb0] at hfb; cases hfb)
          all_goals cases ω <;> simp [hb0, hb1, h0, h1, h2, fixedChoiceMap, nonFixedChoiceMap]
  right_inv p := by
    ext x
    · simp only [dif_pos x.2]
      rcases hp : p.1 x with ⟨_ | _ | _ | k, hk⟩
      · rfl
      · rfl
      · rfl
      · exact False.elim (Nat.not_lt_zero k
          (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk))))
    · simp only [dif_neg x.2]
      cases fixedChoiceMap (p.1 ⟨rho x.1, hrho x.1⟩) .bot <;> cases h : p.2 x <;> rfl

/-- Characterization of `IsLocalic`: restricts the `Fin 3` choice on fixed points to `Bool`
(`{1, 2}`, killing `0 = id`), leaving all `Bool` choices on non-fixed points intact! -/
theorem isLocalic_iff_equivProd_ne_zero {X : Type} [DecidableEq X] {rho : X → X}
    (hrho : ∀ x, rho (rho x) = rho x) (J : M1SliceLTT rho) :
    J.IsLocalic ↔ ∀ a : { x : X // rho x = x }, (equivProd hrho J).1 a ≠ 0 := by
  constructor
  · intro hLoc ⟨a, ha⟩
    have hm : J.j a .mid = .top := hLoc a ha
    dsimp [equivProd]
    cases hb : J.j a .bot <;> simp [hm]
  · intro hne a ha
    have h0 := hne ⟨a, ha⟩
    rcases m1Slice_fixed_bot_cases J ha with ⟨hb, hm, _⟩ | ⟨hb, hm, _⟩ | ⟨hb, hm, _⟩
    · exfalso; apply h0; simp [equivProd, hb, hm]
    · exact hm
    · exact hm

instance instDecidablePredIsLocalic {X : Type} [Fintype X] [DecidableEq X] (rho : X → X) :
    DecidablePred (fun J : M1SliceLTT rho ↦ J.IsLocalic) :=
  fun _ ↦ Fintype.decidableForallFintype

/-- **Lawvere–Tierney Slice Enumeration (`m1_slice_lt_count`):** For every finite idempotent
`ℳ₁`-set `(X, ρ)` with `k` fixed points and `m` non-fixed points:
1. Total Lawvere–Tierney topologies on `(Set^{ℳ₁})/X` = `3^k * 2^m`,
2. Localic slice subtopoi = `2^(k + m)`,
3. Non-localic (hence non-Boolean) slice subtopoi = `(3^k - 2^k) * 2^m`. -/
theorem m1_slice_lt_count {X : Type} [Fintype X] [DecidableEq X]
    {rho : X → X} (hrho : ∀ x, rho (rho x) = rho x) :
    let k := Fintype.card { x : X // rho x = x }
    let m := Fintype.card { x : X // rho x ≠ x }
    letI : Fintype (M1SliceLTT rho) := Fintype.ofEquiv _ (equivProd hrho).symm
    Fintype.card (M1SliceLTT rho) = 3 ^ k * 2 ^ m ∧
      Fintype.card { J : M1SliceLTT rho // J.IsLocalic } = 2 ^ (k + m) ∧
      Fintype.card { J : M1SliceLTT rho // ¬ J.IsLocalic } = (3 ^ k - 2 ^ k) * 2 ^ m := by
  dsimp only
  set A := { x : X // rho x = x }
  set B := { x : X // rho x ≠ x }
  letI instFin : Fintype (M1SliceLTT rho) := Fintype.ofEquiv _ (equivProd hrho).symm
  have hTotal :
      @Fintype.card (M1SliceLTT rho) instFin = 3 ^ Fintype.card A * 2 ^ Fintype.card B := by
    rw [@Fintype.card_congr _ _ instFin _ (equivProd hrho), Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  let fin3NonZeroEquivBool : { z : Fin 3 // z ≠ 0 } ≃ Bool :=
    { toFun := fun ⟨z, _⟩ ↦ decide (z = 1)
      invFun := fun b ↦ if b then ⟨1, by decide⟩ else ⟨2, by decide⟩
      left_inv := fun ⟨z, hz⟩ ↦ by fin_cases z <;> simp at hz ⊢
      right_inv := fun b ↦ by cases b <;> rfl }
  have hLocEquiv : { J : M1SliceLTT rho // J.IsLocalic } ≃
      ((A → Bool) × (B → Bool)) := by
    refine
      { toFun := fun ⟨J, hJ⟩ ↦
          (fun a ↦ fin3NonZeroEquivBool ⟨(equivProd hrho J).1 a,
            (isLocalic_iff_equivProd_ne_zero hrho J).mp hJ a⟩,
           (equivProd hrho J).2)
        invFun := fun p ↦
          ⟨(equivProd hrho).symm (fun a ↦ (fin3NonZeroEquivBool.symm (p.1 a)).1, p.2),
           (isLocalic_iff_equivProd_ne_zero hrho _).mpr fun a ↦ by
             rw [Equiv.apply_symm_apply]
             exact (fin3NonZeroEquivBool.symm (p.1 a)).2⟩
        left_inv := fun ⟨J, hJ⟩ ↦ Subtype.ext <| by
          have heq :
              (fun a ↦ (fin3NonZeroEquivBool.symm
                (fin3NonZeroEquivBool ⟨(equivProd hrho J).1 a,
                  (isLocalic_iff_equivProd_ne_zero hrho J).mp hJ a⟩)).1,
               (equivProd hrho J).2) = equivProd hrho J := by
            ext a
            · simp
            · rfl
          exact (congrArg (equivProd hrho).symm heq).trans ((equivProd hrho).symm_apply_apply J)
        right_inv := fun p ↦ by
          have hpair : equivProd hrho ((equivProd hrho).symm
              (fun a ↦ (fin3NonZeroEquivBool.symm (p.1 a)).1, p.2)) =
              (fun a ↦ (fin3NonZeroEquivBool.symm (p.1 a)).1, p.2) :=
            (equivProd hrho).apply_symm_apply _
          ext a
          · exact (congrArg fin3NonZeroEquivBool
              (Subtype.ext (congrArg (fun q ↦ q.1 a) hpair))).trans
              (fin3NonZeroEquivBool.apply_symm_apply (p.1 a))
          · exact congrArg (fun q ↦ q.2 a) hpair }
  have hLoc : Fintype.card { J : M1SliceLTT rho // J.IsLocalic } =
      2 ^ (Fintype.card A + Fintype.card B) := by
    rw [Fintype.card_congr hLocEquiv, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fun, Fintype.card_bool, pow_add]
  have hCompl : Fintype.card { J : M1SliceLTT rho // ¬ J.IsLocalic } =
      (3 ^ Fintype.card A - 2 ^ Fintype.card A) * 2 ^ Fintype.card B := by
    letI : Fintype (M1SliceLTT rho) := instFin
    have hsplit := Fintype.card_subtype_compl (fun J : M1SliceLTT rho ↦ J.IsLocalic)
    have hpow : 2 ^ (Fintype.card A + Fintype.card B) =
        2 ^ Fintype.card A * 2 ^ Fintype.card B := pow_add 2 _ _
    rw [hTotal, hLoc, hpow] at hsplit
    rw [Nat.sub_mul]
    omega
  exact ⟨hTotal, hLoc, hCompl⟩

end M1SliceLTT

/-! ## Section 3: Mode (iii) 2-Stage `δ`-Ring Obstruction Tower & Finite Leray Transgression -/

section DeltaObstructionTower

/-- Stage-0 identity `p * δ(p) = φ(p) - p^p` for any `p`-derivation lifting `φ`. -/
theorem delta_mul_p_eq_frob_sub (p : ℕ) {A : Type u} [CommRing A]
    (phi d : A → A) (hphi : ∀ x : A, phi x = x ^ p + (p : A) * d x) :
    (p : A) * d (p : A) = phi (p : A) - (p : A) ^ p := by
  have h := hphi (p : A)
  calc
    (p : A) * d (p : A) = ((p : A) ^ p + (p : A) * d (p : A)) - (p : A) ^ p := by ring
    _ = phi (p : A) - (p : A) ^ p := by rw [h]

/-- Specialization of `delta_mul_p_eq_frob_sub` to `DeltaStructure p A`. -/
theorem deltaStructure_delta_mul_p {p : ℕ} [Fact (Nat.Prime p)]
    {A : Type u} [CommRing A] (dA : DeltaStructure p A) :
    (p : A) * dA.delta (p : A) = dA.phi (p : A) - (p : A) ^ p :=
  delta_mul_p_eq_frob_sub p dA.phi dA.delta dA.phi_spec

/-- Commutative ring `R` equipped with a Frobenius-lift candidate ring endomorphism `φ : R →+* R`
satisfying pointwise Fermat congruence `∀ x, ∃ y, φ(x) - x² = 2y` (`p = 2`). -/
structure FrobLiftRing2 : Type (u + 1) where
  /-- Underlying commutative ring. -/
  R : Type u
  /-- Commutative ring structure on `R`. -/
  [commRing : CommRing R]
  /-- Frobenius-lift candidate ring endomorphism `φ : R →+* R`. -/
  phi : R →+* R
  /-- Fermat congruence `φ(x) ≡ x² (mod 2R)` (`Stage 0`). -/
  frob_congr : ∀ x : R, ∃ y : R, phi x - x ^ 2 = 2 * y

attribute [instance] FrobLiftRing2.commRing

/-- **Stage-1 Fiber (`DeltaLift F`):** The type of `p = 2` Joyal `δ`-ring structures on `F.R`
whose Frobenius lift `x ↦ x² + 2 δ(x)` equals `F.phi` pointwise. -/
def DeltaLift (F : FrobLiftRing2.{u}) : Type u :=
  { inst : DeltaRing2 F.R // ∀ x : F.R, x ^ 2 + 2 * inst.delta x = F.phi x }

/-- Stage-2 torsor difference on `DeltaLift F`: any two lifts in `DeltaLift F` differ by a
`2`-torsion `φ`-derivation `FrobDerivation2 F.R F.phi`. -/
def deltaLift_sub_frobDerivation2 {F : FrobLiftRing2.{u}} (L₀ L₁ : DeltaLift F) :
    FrobDerivation2 F.R F.phi :=
  deltaRing2_sub_frobDerivation2 L₀.1 L₁.1 L₀.2 L₁.2

/-- Stage-2 torsor action on `DeltaLift F`: translating a lift by `D ∈ Der_φ(R, Ann_R(2))`. -/
def deltaLift_add_frobDerivation2 {F : FrobLiftRing2.{u}} (L₀ : DeltaLift F)
    (D : FrobDerivation2 F.R F.phi) : DeltaLift F :=
  ⟨deltaRing2_add_frobDerivation2 L₀.1 D L₀.2,
   deltaRing2_add_frobDerivation2_lift L₀.1 D L₀.2⟩

/-- `ℤ` with `φ = id` as a canonical `FrobLiftRing2`. -/
def intFrobLift : FrobLiftRing2.{0} where
  R := ℤ
  phi := RingHom.id ℤ
  frob_congr x := ⟨intDelta x, (two_mul_intDelta x).symm⟩

private lemma int_delta_lift (x : ℤ) : x ^ 2 + 2 * intDelta x = x :=
  (add_comm (x ^ 2) (2 * intDelta x)).trans (eq_sub_iff_add_eq.mp (two_mul_intDelta x))

theorem nonempty_deltaLift_int : Nonempty (DeltaLift intFrobLift) :=
  ⟨⟨instDeltaRing2Int, int_delta_lift⟩⟩

/-- `(ZMod 2, id)` as an authentic `FrobLiftRing2`: `x² = x` for all `x : ZMod 2`. -/
def zmod2FrobLift : FrobLiftRing2.{0} where
  R := ZMod 2
  phi := RingHom.id (ZMod 2)
  frob_congr x := ⟨0, by
    rcases R2Ring.zmod2_eq_zero_or_one x with rfl | rfl <;> decide⟩

/-- No `DeltaRing2` structure exists on `ZMod 2` (`0 = δ(1 + 1) = 2δ(1) - 1 = 1 ≠ 0`). -/
theorem isEmpty_deltaRing2_zmod2 : IsEmpty (DeltaRing2 (ZMod 2)) := by
  refine ⟨fun inst ↦ ?_⟩
  have h11 := inst.delta_add (1 : ZMod 2) 1
  have h10 : (1 : ZMod 2) + 1 = 0 := rfl
  have hmul : (1 : ZMod 2) * 1 = 1 := rfl
  have hsub : (0 : ZMod 2) + 0 - 1 = 1 := rfl
  rw [inst.delta_one, hmul, h10, inst.delta_zero, hsub] at h11
  exact Nat.zero_ne_one (congrArg Fin.val h11)

/-- **Stage-1 Empty Fiber Witness 1 (`empty_deltaLift_zmod2`):** `(ZMod 2, id) : FrobLiftRing2` has
empty `DeltaLift` fiber (`δ(1 + 1) = -1 ≠ 0`). -/
theorem empty_deltaLift_zmod2 : IsEmpty (DeltaLift zmod2FrobLift) :=
  ⟨fun L ↦ isEmpty_deltaRing2_zmod2.false L.1⟩

private lemma zmod4_cases (x : ZMod 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  rcases x with ⟨n, hn⟩
  match n with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | 2 => exact Or.inr (Or.inr (Or.inl rfl))
  | 3 => exact Or.inr (Or.inr (Or.inr rfl))
  | n + 4 => exact False.elim (Nat.not_le_of_gt hn (Nat.le_add_left 4 n))

/-- `(ZMod 4, id)` as an authentic `FrobLiftRing2`: `x - x²` is even for all `x : ZMod 4`. -/
def zmod4FrobLift : FrobLiftRing2.{0} where
  R := ZMod 4
  phi := RingHom.id (ZMod 4)
  frob_congr x := by
    rcases zmod4_cases x with rfl | rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨1, by decide⟩

/-- No `DeltaRing2` structure exists on `ZMod 4` (`0 = δ(2 + 2) = 2δ(2) - 4 = -2 ≠ 0`). -/
theorem isEmpty_deltaRing2_zmod4 : IsEmpty (DeltaRing2 (ZMod 4)) := by
  refine ⟨fun inst ↦ ?_⟩
  have h2 : inst.delta (2 : ZMod 4) = -1 := by
    have h11 := inst.delta_add 1 1
    rw [inst.delta_one, one_mul] at h11
    simpa using h11
  have h4 : inst.delta ((2 : ZMod 4) + 2) = 0 := by
    have hz : (2 : ZMod 4) + 2 = 0 := by decide
    rw [hz, inst.delta_zero]
  have hadd := inst.delta_add (2 : ZMod 4) 2
  rw [h4, h2] at hadd
  exact absurd hadd (by decide)

/-- **Stage-1 Empty Fiber Witness 2 (`empty_deltaLift_zmod4`):** `(ZMod 4, id) : FrobLiftRing2` has
empty `DeltaLift` fiber (`δ(2 + 2) = -2 ≠ 0`). -/
theorem empty_deltaLift_zmod4 : IsEmpty (DeltaLift zmod4FrobLift) :=
  ⟨fun L ↦ isEmpty_deltaRing2_zmod4.false L.1⟩

/-- Auxiliary quotient ring `R_{2,2,0}^{\mathrm{id}} = ℤ[η]/(2η, η² - η) ≅ ℤ × 𝔽₂`, where
`φ = id` IS a ring endomorphism AND satisfies pointwise Fermat congruence `x - x² ∈ 2A`, yet
STILL admits zero `DeltaRing2` structures via the additive cocycle `δ(2η) = 0`. -/
@[ext]
structure R2IdempRing : Type where
  /-- Integer part `a` of `a + bη`. -/
  a : ℤ
  /-- Idempotent `2`-torsion coefficient `b ∈ 𝔽₂` of `a + bη` (`η² = η`). -/
  b : ZMod 2
  deriving DecidableEq

namespace R2IdempRing

def eta : R2IdempRing := ⟨0, 1⟩

instance : Zero R2IdempRing := ⟨⟨0, 0⟩⟩
instance : One R2IdempRing := ⟨⟨1, 0⟩⟩
instance : Add R2IdempRing := ⟨fun x y ↦ ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg R2IdempRing := ⟨fun x ↦ ⟨-x.a, -x.b⟩⟩
instance : Sub R2IdempRing := ⟨fun x y ↦ ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Mul R2IdempRing :=
  ⟨fun x y ↦ ⟨x.a * y.a, (x.a : ZMod 2) * y.b + (y.a : ZMod 2) * x.b + x.b * y.b⟩⟩
instance : NatCast R2IdempRing := ⟨fun n ↦ ⟨n, 0⟩⟩
instance : IntCast R2IdempRing := ⟨fun z ↦ ⟨z, 0⟩⟩

@[simp] lemma zero_a : (0 : R2IdempRing).a = 0 := rfl
@[simp] lemma zero_b : (0 : R2IdempRing).b = 0 := rfl
@[simp] lemma one_a : (1 : R2IdempRing).a = 1 := rfl
@[simp] lemma one_b : (1 : R2IdempRing).b = 0 := rfl
@[simp] lemma add_a (x y : R2IdempRing) : (x + y).a = x.a + y.a := rfl
@[simp] lemma add_b (x y : R2IdempRing) : (x + y).b = x.b + y.b := rfl
@[simp] lemma neg_a (x : R2IdempRing) : (-x).a = -x.a := rfl
@[simp] lemma neg_b (x : R2IdempRing) : (-x).b = -x.b := rfl
@[simp] lemma sub_a (x y : R2IdempRing) : (x - y).a = x.a - y.a := rfl
@[simp] lemma sub_b (x y : R2IdempRing) : (x - y).b = x.b - y.b := rfl
@[simp] lemma mul_a (x y : R2IdempRing) : (x * y).a = x.a * y.a := rfl
@[simp] lemma mul_b (x y : R2IdempRing) :
    (x * y).b = (x.a : ZMod 2) * y.b + (y.a : ZMod 2) * x.b + x.b * y.b := rfl
@[simp] lemma natCast_a (n : ℕ) : (n : R2IdempRing).a = n := rfl
@[simp] lemma natCast_b (n : ℕ) : (n : R2IdempRing).b = 0 := rfl
@[simp] lemma intCast_a (z : ℤ) : (z : R2IdempRing).a = z := rfl
@[simp] lemma intCast_b (z : ℤ) : (z : R2IdempRing).b = 0 := rfl

instance instCommRing : CommRing R2IdempRing where
  add := (· + ·)
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero := 0
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  nsmul := @nsmulRec R2IdempRing ⟨0⟩ ⟨(· + ·)⟩
  neg := Neg.neg
  sub := (· - ·)
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]
  zsmul := @zsmulRec R2IdempRing ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec R2IdempRing ⟨0⟩ ⟨(· + ·)⟩)
  neg_add_cancel _ := by apply R2IdempRing.ext <;> exact neg_add_cancel _
  add_comm _ _ := by ext <;> simp [add_comm]
  mul := (· * ·)
  left_distrib _ _ _ := by ext <;> simp [Int.cast_add] <;> ring
  right_distrib _ _ _ := by ext <;> simp [Int.cast_add] <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp [Int.cast_mul] <;> ring
  one := 1
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  natCast n := n
  natCast_zero := by ext <;> simp
  natCast_succ _ := by ext <;> simp
  intCast z := z
  intCast_ofNat _ := by ext <;> simp
  intCast_negSucc _ := by ext <;> simp [Int.negSucc_eq]
  npow := @npowRec R2IdempRing ⟨1⟩ ⟨(· * ·)⟩
  mul_comm _ _ := by ext <;> simp [mul_comm, add_comm]

@[simp] lemma ofNat_two_a : ((2 : R2IdempRing)).a = 2 := rfl
@[simp] lemma ofNat_two_b : ((2 : R2IdempRing)).b = 0 := rfl

theorem id_fermat_congr (x : R2IdempRing) : ∃ u : R2IdempRing, x - x ^ 2 = 2 * u := by
  refine ⟨⟨intDelta x.a, 0⟩, ?_⟩
  ext
  · simp only [sub_a, mul_a, ofNat_two_a, sq]
    rw [← sq]
    exact (two_mul_intDelta x.a).symm
  · rcases R2Ring.zmod2_eq_zero_or_one x.b with hb | hb <;>
      simp [sub_b, mul_b, ofNat_two_a, ofNat_two_b, sq, hb, R2Ring.zmod2_add_self]

end R2IdempRing

/-- `(ℤ × 𝔽₂, id)` (`R2IdempRing`) packaged as a genuine `FrobLiftRing2`. -/
def r2IdempFrobLift : FrobLiftRing2.{0} where
  R := R2IdempRing
  phi := RingHom.id R2IdempRing
  frob_congr := R2IdempRing.id_fermat_congr

/-- Stage-1 additive cocycle impossibility on `R2IdempRing` (`ℤ × 𝔽₂`): even though `φ = id` is a
ring automorphism satisfying Fermat congruence `x ≡ x² (mod 2)` everywhere, `δ(2η) = 0` yields
`2 δ(η) - η² = -η ≠ 0`, making `DeltaRing2 R2IdempRing` empty. -/
theorem isEmpty_deltaRing2_r2Idemp : IsEmpty (DeltaRing2 R2IdempRing) := by
  refine ⟨fun inst ↦ ?_⟩
  have h2eta : R2IdempRing.eta + R2IdempRing.eta = 0 := by decide
  have hadd := inst.delta_add R2IdempRing.eta R2IdempRing.eta
  rw [h2eta, inst.delta_zero] at hadd
  have hb := congrArg R2IdempRing.b hadd
  simp only [R2IdempRing.zero_b, R2IdempRing.sub_b, R2IdempRing.add_b, R2IdempRing.mul_b,
    R2IdempRing.eta, R2Ring.zmod2_add_self, zero_add] at hb
  exact absurd hb (by decide)

/-- **Stage-1 Empty Fiber Witness 3 (`empty_deltaLift_R2Idemp`):** `r2IdempFrobLift` has empty
`DeltaLift` fiber (`IsEmpty (DeltaLift r2IdempFrobLift)`). -/
theorem empty_deltaLift_R2Idemp : IsEmpty (DeltaLift r2IdempFrobLift) :=
  ⟨fun L ↦ isEmpty_deltaRing2_r2Idemp.false L.1⟩

/-! ### Stage 2: Lift Counts (`|Fib(R₂)| = 2`, `|Fib(R_{2,2})| = 16`, `6` Orbits) -/

/-- `(R₂, r2AugFrob)` packaged as a `FrobLiftRing2`. -/
def r2AugFrobLift : FrobLiftRing2.{0} where
  R := R2Ring
  phi := r2AugFrob
  frob_congr x := ⟨instDeltaRing2R2_zero.delta x, by
    have h := r2Delta0Map_frobeniusLift x
    rw [← h]
    ring⟩

/-- Type of `DeltaRing2` structures on `R₂` lifting the augmentation Frobenius `r2AugFrob`,
canonically identified with `DeltaLift r2AugFrobLift`. -/
abbrev R2AugLift : Type :=
  { inst : DeltaRing2 R2Ring // ∀ x : R2Ring, x ^ 2 + 2 * inst.delta x = r2AugFrob x }

/-- Canonical equivalence identifying `R2AugLift` with the Stage-1 fiber
`DeltaLift r2AugFrobLift`. -/
def r2AugLiftEquivDeltaLift : R2AugLift ≃ DeltaLift r2AugFrobLift := Equiv.refl _

private lemma deltaRing2_ext {R : Type u} [CommRing R] {d₁ d₂ : DeltaRing2 R}
    (h : d₁.delta = d₂.delta) : d₁ = d₂ := by
  cases d₁
  cases d₂
  cases h
  rfl

private lemma frobDerivation2_map_natCast {R : Type u} [CommRing R] {phi : R →+* R}
    (D : FrobDerivation2 R phi) (n : ℕ) : D.toFun (n : R) = 0 := by
  induction n with
  | zero => simp [D.map_zero]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, D.map_add, ih, D.map_one, add_zero]

private lemma frobDerivation2_map_intCast {R : Type u} [CommRing R] {phi : R →+* R}
    (D : FrobDerivation2 R phi) (z : ℤ) : D.toFun (z : R) = 0 := by
  cases z with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact frobDerivation2_map_natCast D n
  | negSucc n =>
    have hsum : D.toFun ((Int.negSucc n : ℤ) : R) + D.toFun (((n + 1 : ℕ) : ℤ) : R) = 0 := by
      rw [← D.map_add]
      have h0 : ((Int.negSucc n : ℤ) : R) + (((n + 1 : ℕ) : ℤ) : R) = 0 := by
        push_cast
        ring
      rw [h0, D.map_zero]
    rw [Int.cast_natCast, frobDerivation2_map_natCast, add_zero] at hsum
    exact hsum

/-- Explicit bijection `R2AugLift ≃ ZMod 2` sending `δ ↦ (δ η).b` (with `0 ↦ δ₀`, `1 ↦ δ₁`). -/
def r2AugLiftEquivZMod2 : R2AugLift ≃ ZMod 2 where
  toFun L := (L.1.delta R2Ring.eta).b
  invFun b :=
    match b with
    | ⟨0, _⟩ => ⟨instDeltaRing2R2_zero, r2Delta0Map_frobeniusLift⟩
    | ⟨1, _⟩ => ⟨instDeltaRing2R2_one, r2Delta1Map_frobeniusLift⟩
  left_inv L := by
    let D := deltaRing2_sub_frobDerivation2 instDeltaRing2R2_zero L.1
      r2Delta0Map_frobeniusLift L.2
    have hDeta_a : (D.toFun R2Ring.eta).a = 0 :=
      (R2Ring.two_mul_eq_zero_iff _).mp (D.two_torsion R2Ring.eta)
    have hD_eq : ∀ x : R2Ring, D.toFun x = if x.b = 0 then 0 else D.toFun R2Ring.eta := by
      intro x
      rcases R2Ring.zmod2_eq_zero_or_one x.b with hb | hb
      · have hx : x = (x.a : R2Ring) := R2Ring.ext rfl hb
        simp only [hb, ↓reduceIte]
        rw [hx, frobDerivation2_map_intCast]
      · have hx : x = (x.a : R2Ring) + R2Ring.eta :=
          R2Ring.ext (by simp [R2Ring.eta]) (by simp [R2Ring.eta, hb])
        have hbne : x.b ≠ 0 := by rw [hb]; decide
        simp only [hbne, ↓reduceIte]
        rw [hx, D.map_add, frobDerivation2_map_intCast, zero_add]
    have hL_val : ∀ x : R2Ring,
        L.1.delta x = instDeltaRing2R2_zero.delta x + D.toFun x := fun x ↦ by
      change L.1.delta x =
        instDeltaRing2R2_zero.delta x + (L.1.delta x - instDeltaRing2R2_zero.delta x)
      ring
    have hEtaB : (D.toFun R2Ring.eta).b = (L.1.delta R2Ring.eta).b := by
      simp [D, deltaRing2_sub_frobDerivation2, instDeltaRing2R2_zero, r2Delta0Map_eta]
    rcases R2Ring.zmod2_eq_zero_or_one (L.1.delta R2Ring.eta).b with hz | hz <;> simp only [hz]
    · apply Subtype.ext
      apply deltaRing2_ext
      funext x
      rw [hL_val x, hD_eq x]
      have hD0 : D.toFun R2Ring.eta = 0 := by
        apply R2Ring.ext hDeta_a
        rw [hEtaB, hz]; rfl
      rw [hD0]
      split_ifs <;> simp
    · apply Subtype.ext
      apply deltaRing2_ext
      funext x
      rw [hL_val x, hD_eq x]
      have hD1 : D.toFun R2Ring.eta = R2Ring.eta := by
        apply R2Ring.ext hDeta_a
        rw [hEtaB, hz]; rfl
      rw [hD1]
      rcases R2Ring.zmod2_eq_zero_or_one x.b with hb | hb
      · simp [hb, instDeltaRing2R2_one, r2Delta1Map, instDeltaRing2R2_zero, r2Delta0Map]
      · have hbne : x.b ≠ 0 := by rw [hb]; decide
        simp only [hbne, ↓reduceIte]
        ext
        · simp [instDeltaRing2R2_one, r2Delta1Map, instDeltaRing2R2_zero, r2Delta0Map, R2Ring.eta]
        · simp only [instDeltaRing2R2_one, r2Delta1Map, instDeltaRing2R2_zero, r2Delta0Map,
            R2Ring.eta, R2Ring.add_b, hb, mul_one]
  right_inv b := by
    rcases b with ⟨_ | _ | n, hn⟩
    · rfl
    · rfl
    · exact False.elim (Nat.not_lt_zero n
        (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hn)))

/-- Stage-3 cardinality over `R₂`: `|Fib(R₂, φ_aug)| = 2`. -/
theorem r2_lift_card_eq_two :
    letI : Fintype R2AugLift := Fintype.ofEquiv _ r2AugLiftEquivZMod2.symm
    Fintype.card R2AugLift = 2 := by
  letI instFin : Fintype R2AugLift := Fintype.ofEquiv _ r2AugLiftEquivZMod2.symm
  exact (@Fintype.card_congr _ _ instFin _ r2AugLiftEquivZMod2).trans (ZMod.card 2)

/-- Stage-3 non-isomorphism: the two lifts `r2AugLiftEquivZMod2.symm 0` and
`r2AugLiftEquivZMod2.symm 1` are non-isomorphic in `DeltaRing2Cat`. -/
theorem r2_lifts_non_iso : IsEmpty (DeltaRing2Cat.of R2Delta0 ≅ DeltaRing2Cat.of R2Delta1) :=
  r2Delta0_not_iso_r2Delta1

/-- Concrete rank-2 `2`-torsion nilpotent ring `R_{2,2} = ℤ[η₁, η₂]/(2η_i, η_i η_j)`
represented as triples `⟨a, b₁, b₂⟩ : ℤ × ZMod 2 × ZMod 2`. -/
@[ext]
structure R22Ring : Type where
  /-- Integer part `a`. -/
  a : ℤ
  /-- Coefficient `b₁ ∈ 𝔽₂` of `η₁`. -/
  b1 : ZMod 2
  /-- Coefficient `b₂ ∈ 𝔽₂` of `η₂`. -/
  b2 : ZMod 2
  deriving DecidableEq, Repr

namespace R22Ring

def eta1 : R22Ring := ⟨0, 1, 0⟩
def eta2 : R22Ring := ⟨0, 0, 1⟩

instance : Zero R22Ring := ⟨⟨0, 0, 0⟩⟩
instance : One R22Ring := ⟨⟨1, 0, 0⟩⟩
instance : Add R22Ring := ⟨fun x y ↦ ⟨x.a + y.a, x.b1 + y.b1, x.b2 + y.b2⟩⟩
instance : Neg R22Ring := ⟨fun x ↦ ⟨-x.a, -x.b1, -x.b2⟩⟩
instance : Sub R22Ring := ⟨fun x y ↦ ⟨x.a - y.a, x.b1 - y.b1, x.b2 - y.b2⟩⟩
instance : Mul R22Ring :=
  ⟨fun x y ↦ ⟨x.a * y.a,
    (x.a : ZMod 2) * y.b1 + (y.a : ZMod 2) * x.b1,
    (x.a : ZMod 2) * y.b2 + (y.a : ZMod 2) * x.b2⟩⟩
instance : NatCast R22Ring := ⟨fun n ↦ ⟨n, 0, 0⟩⟩
instance : IntCast R22Ring := ⟨fun z ↦ ⟨z, 0, 0⟩⟩

@[simp] lemma zero_a : (0 : R22Ring).a = 0 := rfl
@[simp] lemma zero_b1 : (0 : R22Ring).b1 = 0 := rfl
@[simp] lemma zero_b2 : (0 : R22Ring).b2 = 0 := rfl
@[simp] lemma one_a : (1 : R22Ring).a = 1 := rfl
@[simp] lemma one_b1 : (1 : R22Ring).b1 = 0 := rfl
@[simp] lemma one_b2 : (1 : R22Ring).b2 = 0 := rfl
@[simp] lemma add_a (x y : R22Ring) : (x + y).a = x.a + y.a := rfl
@[simp] lemma add_b1 (x y : R22Ring) : (x + y).b1 = x.b1 + y.b1 := rfl
@[simp] lemma add_b2 (x y : R22Ring) : (x + y).b2 = x.b2 + y.b2 := rfl
@[simp] lemma neg_a (x : R22Ring) : (-x).a = -x.a := rfl
@[simp] lemma neg_b1 (x : R22Ring) : (-x).b1 = -x.b1 := rfl
@[simp] lemma neg_b2 (x : R22Ring) : (-x).b2 = -x.b2 := rfl
@[simp] lemma sub_a (x y : R22Ring) : (x - y).a = x.a - y.a := rfl
@[simp] lemma sub_b1 (x y : R22Ring) : (x - y).b1 = x.b1 - y.b1 := rfl
@[simp] lemma sub_b2 (x y : R22Ring) : (x - y).b2 = x.b2 - y.b2 := rfl
@[simp] lemma mul_a (x y : R22Ring) : (x * y).a = x.a * y.a := rfl
@[simp] lemma mul_b1 (x y : R22Ring) :
    (x * y).b1 = (x.a : ZMod 2) * y.b1 + (y.a : ZMod 2) * x.b1 := rfl
@[simp] lemma mul_b2 (x y : R22Ring) :
    (x * y).b2 = (x.a : ZMod 2) * y.b2 + (y.a : ZMod 2) * x.b2 := rfl
@[simp] lemma natCast_a (n : ℕ) : (n : R22Ring).a = n := rfl
@[simp] lemma natCast_b1 (n : ℕ) : (n : R22Ring).b1 = 0 := rfl
@[simp] lemma natCast_b2 (n : ℕ) : (n : R22Ring).b2 = 0 := rfl
@[simp] lemma intCast_a (z : ℤ) : (z : R22Ring).a = z := rfl
@[simp] lemma intCast_b1 (z : ℤ) : (z : R22Ring).b1 = 0 := rfl
@[simp] lemma intCast_b2 (z : ℤ) : (z : R22Ring).b2 = 0 := rfl

instance instCommRing : CommRing R22Ring where
  add := (· + ·)
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero := 0
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  nsmul := @nsmulRec R22Ring ⟨0⟩ ⟨(· + ·)⟩
  neg := Neg.neg
  sub := (· - ·)
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]
  zsmul := @zsmulRec R22Ring ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec R22Ring ⟨0⟩ ⟨(· + ·)⟩)
  neg_add_cancel _ := by apply R22Ring.ext <;> exact neg_add_cancel _
  add_comm _ _ := by ext <;> simp [add_comm]
  mul := (· * ·)
  left_distrib _ _ _ := by ext <;> simp [Int.cast_add] <;> ring
  right_distrib _ _ _ := by ext <;> simp [Int.cast_add] <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp [Int.cast_mul] <;> ring
  one := 1
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  natCast n := n
  natCast_zero := by ext <;> simp
  natCast_succ _ := by ext <;> simp
  intCast z := z
  intCast_ofNat _ := by ext <;> simp
  intCast_negSucc _ := by ext <;> simp [Int.negSucc_eq]
  npow := @npowRec R22Ring ⟨1⟩ ⟨(· * ·)⟩
  mul_comm _ _ := by ext <;> simp [mul_comm, add_comm]

@[simp] lemma ofNat_two_a : ((2 : R22Ring)).a = 2 := rfl
@[simp] lemma ofNat_two_b1 : ((2 : R22Ring)).b1 = 0 := rfl
@[simp] lemma ofNat_two_b2 : ((2 : R22Ring)).b2 = 0 := rfl

theorem two_mul_eq_zero_iff (x : R22Ring) : (2 : R22Ring) * x = 0 ↔ x.a = 0 := by
  constructor
  · intro h
    have ha := congrArg R22Ring.a h
    change 2 * x.a = 0 at ha
    omega
  · intro ha
    ext <;> simp [ha, R2Ring.two_mul_zmod2]

end R22Ring

/-- Augmentation Frobenius `φ(a + b₁ η₁ + b₂ η₂) = a` on `R_{2,2}`. -/
def r22AugFrob : R22Ring →+* R22Ring where
  toFun x := ⟨x.a, 0, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

@[simp] theorem r22AugFrob_apply (x : R22Ring) : r22AugFrob x = ⟨x.a, 0, 0⟩ := rfl

private def r22BaseDeltaMap (x : R22Ring) : R22Ring :=
  ⟨intDelta x.a, (x.a : ZMod 2) * x.b1, (x.a : ZMod 2) * x.b2⟩

private def r22BaseDelta : DeltaRing2 R22Ring where
  delta := r22BaseDeltaMap
  delta_zero := by decide
  delta_one := by decide
  delta_add x y := by
    ext
    · exact instDeltaRing2Int.delta_add x.a y.a
    · simp only [r22BaseDeltaMap, R22Ring.add_a, R22Ring.add_b1, R22Ring.sub_b1, R22Ring.mul_b1,
        Int.cast_add]
      rw [sub_eq_add_neg, CharTwo.neg_eq]
      ring
    · simp only [r22BaseDeltaMap, R22Ring.add_a, R22Ring.add_b2, R22Ring.sub_b2, R22Ring.mul_b2,
        Int.cast_add]
      rw [sub_eq_add_neg, CharTwo.neg_eq]
      ring
  delta_mul x y := by
    ext
    · have h := instDeltaRing2Int.delta_mul x.a y.a
      dsimp only [instDeltaRing2Int, intDelta] at h
      simp only [r22BaseDeltaMap, intDelta, R22Ring.add_a, R22Ring.mul_a, R22Ring.ofNat_two_a,
        sq] at h ⊢
      exact h
    · have hx2 : ((x ^ 2).a : ZMod 2) = (x.a : ZMod 2) ^ 2 := by simp [sq]
      have hx2b : (x ^ 2).b1 = 0 := by simp [sq, R2Ring.zmod2_add_self]
      have hy2 : ((y ^ 2).a : ZMod 2) = (y.a : ZMod 2) ^ 2 := by simp [sq]
      have hy2b : (y ^ 2).b1 = 0 := by simp [sq, R2Ring.zmod2_add_self]
      simp only [r22BaseDeltaMap, R22Ring.mul_a, R22Ring.mul_b1, R22Ring.add_b1, Int.cast_mul,
        R22Ring.ofNat_two_a, R22Ring.ofNat_two_b1, R2Ring.intCast_two_zmod2, zero_mul, mul_zero,
        add_zero]
      rw [hx2, hx2b, hy2, hy2b, mul_zero, add_zero, mul_zero, add_zero]
      ring
    · have hx2 : ((x ^ 2).a : ZMod 2) = (x.a : ZMod 2) ^ 2 := by simp [sq]
      have hx2b : (x ^ 2).b2 = 0 := by simp [sq, R2Ring.zmod2_add_self]
      have hy2 : ((y ^ 2).a : ZMod 2) = (y.a : ZMod 2) ^ 2 := by simp [sq]
      have hy2b : (y ^ 2).b2 = 0 := by simp [sq, R2Ring.zmod2_add_self]
      simp only [r22BaseDeltaMap, R22Ring.mul_a, R22Ring.mul_b2, R22Ring.add_b2, Int.cast_mul,
        R22Ring.ofNat_two_a, R22Ring.ofNat_two_b2, R2Ring.intCast_two_zmod2, zero_mul, mul_zero,
        add_zero]
      rw [hx2, hx2b, hy2, hy2b, mul_zero, add_zero, mul_zero, add_zero]
      ring

private theorem r22BaseDelta_lift (x : R22Ring) :
    x ^ 2 + 2 * r22BaseDelta.delta x = r22AugFrob x := by
  ext
  · simp only [sq, r22BaseDelta, r22BaseDeltaMap, r22AugFrob, R22Ring.add_a, R22Ring.mul_a,
      R22Ring.ofNat_two_a, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    have h2 := two_mul_intDelta x.a
    linarith [h2]
  · simp only [sq, r22BaseDelta, r22BaseDeltaMap, r22AugFrob, R22Ring.add_b1, R22Ring.mul_b1,
      R22Ring.ofNat_two_a, R22Ring.ofNat_two_b1, R2Ring.intCast_two_zmod2,
      R2Ring.zmod2_add_self, zero_mul, mul_zero, add_zero, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
  · simp only [sq, r22BaseDelta, r22BaseDeltaMap, r22AugFrob, R22Ring.add_b2, R22Ring.mul_b2,
      R22Ring.ofNat_two_a, R22Ring.ofNat_two_b2, R2Ring.intCast_two_zmod2,
      R2Ring.zmod2_add_self, zero_mul, mul_zero, add_zero, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]

private def r22MatDer (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    FrobDerivation2 R22Ring r22AugFrob where
  toFun x := ⟨0, M 0 0 * x.b1 + M 0 1 * x.b2, M 1 0 * x.b1 + M 1 1 * x.b2⟩
  two_torsion x := by
    have h2z : (2 : ZMod 2) = 0 := by decide
    ext
    · simp [R22Ring.mul_a, R22Ring.ofNat_two_a]
    · simp [R22Ring.mul_b1, R22Ring.ofNat_two_a, R22Ring.ofNat_two_b1, Int.cast_ofNat, h2z]
    · simp [R22Ring.mul_b2, R22Ring.ofNat_two_a, R22Ring.ofNat_two_b2, Int.cast_ofNat, h2z]
  map_add x y := by
    ext <;> simp <;> ring
  leibniz x y := by
    ext
    · simp
    · simp; ring
    · simp; ring

/-- `(R_{2,2}, r22AugFrob)` packaged as a `FrobLiftRing2`. -/
def r22AugFrobLift : FrobLiftRing2.{0} where
  R := R22Ring
  phi := r22AugFrob
  frob_congr x := ⟨r22BaseDelta.delta x, by
    have h := r22BaseDelta_lift x
    rw [← h]
    ring⟩

/-- The `16`-element fiber `{ inst : DeltaRing2 R22Ring // ∀ x, x² + 2 δ(x) = r22AugFrob x }`,
canonically identified with `DeltaLift r22AugFrobLift`. -/
abbrev R22AugLift : Type :=
  { inst : DeltaRing2 R22Ring // ∀ x : R22Ring, x ^ 2 + 2 * inst.delta x = r22AugFrob x }

/-- Canonical equivalence identifying `R22AugLift` with `DeltaLift r22AugFrobLift`. -/
def r22AugLiftEquivDeltaLift : R22AugLift ≃ DeltaLift r22AugFrobLift := Equiv.refl _

/-- Explicit bijection `R22AugLift ≃ Matrix (Fin 2) (Fin 2) (ZMod 2)`. -/
def r22AugLiftEquivMatrix : R22AugLift ≃ Matrix (Fin 2) (Fin 2) (ZMod 2) where
  toFun L := !![(L.1.delta R22Ring.eta1).b1, (L.1.delta R22Ring.eta2).b1;
                 (L.1.delta R22Ring.eta1).b2, (L.1.delta R22Ring.eta2).b2]
  invFun M :=
    ⟨deltaRing2_add_frobDerivation2 r22BaseDelta (r22MatDer M) r22BaseDelta_lift,
     deltaRing2_add_frobDerivation2_lift r22BaseDelta (r22MatDer M) r22BaseDelta_lift⟩
  left_inv L := by
    let D := deltaRing2_sub_frobDerivation2 r22BaseDelta L.1 r22BaseDelta_lift L.2
    have hD1a : (D.toFun R22Ring.eta1).a = 0 :=
      (R22Ring.two_mul_eq_zero_iff _).mp (D.two_torsion R22Ring.eta1)
    have hD2a : (D.toFun R22Ring.eta2).a = 0 :=
      (R22Ring.two_mul_eq_zero_iff _).mp (D.two_torsion R22Ring.eta2)
    have hD_eq : ∀ x : R22Ring, D.toFun x =
        (if x.b1 = 0 then 0 else D.toFun R22Ring.eta1) +
        (if x.b2 = 0 then 0 else D.toFun R22Ring.eta2) := by
      intro x
      rcases R2Ring.zmod2_eq_zero_or_one x.b1 with hb1 | hb1 <;>
        rcases R2Ring.zmod2_eq_zero_or_one x.b2 with hb2 | hb2
      · have hx : x = (x.a : R22Ring) := R22Ring.ext rfl hb1 hb2
        simp only [hb1, hb2, ↓reduceIte, add_zero]
        rw [hx, frobDerivation2_map_intCast]
      · have hx : x = (x.a : R22Ring) + R22Ring.eta2 := by
          ext <;> simp [R22Ring.eta2, hb1, hb2]
        have hne : x.b2 ≠ 0 := by rw [hb2]; decide
        simp only [hb1, hne, ↓reduceIte, zero_add]
        rw [hx, D.map_add, frobDerivation2_map_intCast, zero_add]
      · have hx : x = (x.a : R22Ring) + R22Ring.eta1 := by
          ext <;> simp [R22Ring.eta1, hb1, hb2]
        have hne : x.b1 ≠ 0 := by rw [hb1]; decide
        simp only [hne, hb2, ↓reduceIte, add_zero]
        rw [hx, D.map_add, frobDerivation2_map_intCast, zero_add]
      · have hx : x = (x.a : R22Ring) + R22Ring.eta1 + R22Ring.eta2 := by
          ext <;> simp [R22Ring.eta1, R22Ring.eta2, hb1, hb2]
        have hne1 : x.b1 ≠ 0 := by rw [hb1]; decide
        have hne2 : x.b2 ≠ 0 := by rw [hb2]; decide
        simp only [hne1, hne2, ↓reduceIte]
        rw [hx, D.map_add, D.map_add, frobDerivation2_map_intCast, zero_add]
    apply Subtype.ext
    apply deltaRing2_ext
    funext x
    have hLval : L.1.delta x = r22BaseDelta.delta x + D.toFun x := by
      change L.1.delta x = r22BaseDelta.delta x + (L.1.delta x - r22BaseDelta.delta x)
      ring
    change _ = L.1.delta x
    rw [hLval, hD_eq x]
    have hB0 : r22BaseDelta.delta R22Ring.eta1 = 0 := by decide
    have hB1 : r22BaseDelta.delta R22Ring.eta2 = 0 := by decide
    ext
    · split_ifs <;> simp [deltaRing2_add_frobDerivation2, r22MatDer, R22Ring.add_a, hD1a, hD2a]
    · rcases R2Ring.zmod2_eq_zero_or_one x.b1 with hb1 | hb1 <;>
        rcases R2Ring.zmod2_eq_zero_or_one x.b2 with hb2 | hb2 <;>
        simp [deltaRing2_add_frobDerivation2, r22MatDer, D, deltaRing2_sub_frobDerivation2,
          R22Ring.eta1, R22Ring.eta2, hb1, hb2, r22BaseDelta, r22BaseDeltaMap]
    · rcases R2Ring.zmod2_eq_zero_or_one x.b1 with hb1 | hb1 <;>
        rcases R2Ring.zmod2_eq_zero_or_one x.b2 with hb2 | hb2 <;>
        simp [deltaRing2_add_frobDerivation2, r22MatDer, D, deltaRing2_sub_frobDerivation2,
          R22Ring.eta1, R22Ring.eta2, hb1, hb2, r22BaseDelta, r22BaseDeltaMap]
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [deltaRing2_add_frobDerivation2, r22MatDer, r22BaseDelta, r22BaseDeltaMap,
        R22Ring.eta1, R22Ring.eta2]

/-- Stage-3 cardinality over `R_{2,2}`: `|Fib(R_{2,2}, φ_aug)| = 16`. -/
theorem r22_lift_card_eq_sixteen :
    letI : Fintype R22AugLift := Fintype.ofEquiv _ r22AugLiftEquivMatrix.symm
    Fintype.card R22AugLift = 16 := by
  letI instFin : Fintype R22AugLift := Fintype.ofEquiv _ r22AugLiftEquivMatrix.symm
  have hMat : Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod 2)) = 16 := by decide
  exact (@Fintype.card_congr _ _ instFin _ r22AugLiftEquivMatrix).trans hMat

/-- Equivalence relation of `DeltaRing2` isomorphism on `R22AugLift`: `L₁ ~ L₂` iff there exists
`e : R22Ring ≃+* R22Ring` intertwining `L₁.1.delta` and `L₂.1.delta`. -/
def R22LiftIso (L₁ L₂ : R22AugLift) : Prop :=
  ∃ e : R22Ring ≃+* R22Ring, ∀ x : R22Ring, e (L₁.1.delta x) = L₂.1.delta (e x)

def r22IsoSetoid : Setoid R22AugLift where
  r := R22LiftIso
  iseqv :=
    { refl := fun _ ↦ ⟨RingEquiv.refl R22Ring, fun _ ↦ rfl⟩
      symm := fun ⟨e, he⟩ ↦ ⟨e.symm, fun x ↦ by
        have h := congrArg e.symm (he (e.symm x))
        simpa using h.symm⟩
      trans := fun ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ ↦ ⟨e₁.trans e₂, fun x ↦ by
        simp only [RingEquiv.coe_trans, Function.comp_apply, h₁, h₂]⟩ }

private def mat2RingEquiv (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :
    R22Ring ≃+* R22Ring :=
  { toFun := fun x ↦ ⟨x.a,
      g.val 0 0 * x.b1 + g.val 0 1 * x.b2,
      g.val 1 0 * x.b1 + g.val 1 1 * x.b2⟩
    invFun := fun y ↦ ⟨y.a,
      (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val 0 0 * y.b1 +
        (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val 0 1 * y.b2,
      (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val 1 0 * y.b1 +
        (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val 1 1 * y.b2⟩
    left_inv := fun x ↦ by
      have hmul : (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val * g.val = 1 :=
        g.inv_mul
      have h00 := congrFun (congrFun hmul 0) 0
      have h01 := congrFun (congrFun hmul 0) 1
      have h10 := congrFun (congrFun hmul 1) 0
      have h11 := congrFun (congrFun hmul 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        ↓reduceIte] at h00 h01 h10 h11
      rw [if_neg (by decide : (0 : Fin 2) ≠ 1)] at h01
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)] at h10
      let gi : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
        (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val
      ext
      · rfl
      · change gi 0 0 * (g.val 0 0 * x.b1 + g.val 0 1 * x.b2) +
            gi 0 1 * (g.val 1 0 * x.b1 + g.val 1 1 * x.b2) = x.b1
        calc
          _ = (gi 0 0 * g.val 0 0 + gi 0 1 * g.val 1 0) * x.b1 +
                (gi 0 0 * g.val 0 1 + gi 0 1 * g.val 1 1) * x.b2 := by ring
          _ = 1 * x.b1 + 0 * x.b2 := by rw [h00, h01]
          _ = x.b1 := by ring
      · change gi 1 0 * (g.val 0 0 * x.b1 + g.val 0 1 * x.b2) +
            gi 1 1 * (g.val 1 0 * x.b1 + g.val 1 1 * x.b2) = x.b2
        calc
          _ = (gi 1 0 * g.val 0 0 + gi 1 1 * g.val 1 0) * x.b1 +
                (gi 1 0 * g.val 0 1 + gi 1 1 * g.val 1 1) * x.b2 := by ring
          _ = 0 * x.b1 + 1 * x.b2 := by rw [h10, h11]
          _ = x.b2 := by ring
    right_inv := fun y ↦ by
      have hmul : g.val * (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val = 1 :=
        g.mul_inv
      have h00 := congrFun (congrFun hmul 0) 0
      have h01 := congrFun (congrFun hmul 0) 1
      have h10 := congrFun (congrFun hmul 1) 0
      have h11 := congrFun (congrFun hmul 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        ↓reduceIte] at h00 h01 h10 h11
      rw [if_neg (by decide : (0 : Fin 2) ≠ 1)] at h01
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)] at h10
      let gi : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
        (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val
      ext
      · rfl
      · change g.val 0 0 * (gi 0 0 * y.b1 + gi 0 1 * y.b2) +
            g.val 0 1 * (gi 1 0 * y.b1 + gi 1 1 * y.b2) = y.b1
        calc
          _ = (g.val 0 0 * gi 0 0 + g.val 0 1 * gi 1 0) * y.b1 +
                (g.val 0 0 * gi 0 1 + g.val 0 1 * gi 1 1) * y.b2 := by ring
          _ = 1 * y.b1 + 0 * y.b2 := by rw [h00, h01]
          _ = y.b1 := by ring
      · change g.val 1 0 * (gi 0 0 * y.b1 + gi 0 1 * y.b2) +
            g.val 1 1 * (gi 1 0 * y.b1 + gi 1 1 * y.b2) = y.b2
        calc
          _ = (g.val 1 0 * gi 0 0 + g.val 1 1 * gi 1 0) * y.b1 +
                (g.val 1 0 * gi 0 1 + g.val 1 1 * gi 1 1) * y.b2 := by ring
          _ = 0 * y.b1 + 1 * y.b2 := by rw [h10, h11]
          _ = y.b2 := by ring
    map_mul' := fun x y ↦ by
      ext
      · rfl
      · simp [R22Ring.mul_b1, R22Ring.mul_b2]; ring
      · simp [R22Ring.mul_b1, R22Ring.mul_b2]; ring
    map_add' := fun x y ↦ by
      ext <;> simp <;> ring }

private def ringAutToMat (e : R22Ring ≃+* R22Ring) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![(e R22Ring.eta1).b1, (e R22Ring.eta2).b1;
     (e R22Ring.eta1).b2, (e R22Ring.eta2).b2]

private lemma r22_aut_eta_fst_zero (e : R22Ring ≃+* R22Ring) :
    (e R22Ring.eta1).a = 0 ∧ (e R22Ring.eta2).a = 0 := by
  constructor
  · exact (R22Ring.two_mul_eq_zero_iff _).mp <| by
      calc
        (2 : R22Ring) * e R22Ring.eta1 = e 2 * e R22Ring.eta1 := by rw [map_ofNat e 2]
        _ = e (2 * R22Ring.eta1) := (map_mul e 2 R22Ring.eta1).symm
        _ = e 0 := by rw [show (2 : R22Ring) * R22Ring.eta1 = 0 by decide]
        _ = 0 := map_zero e
  · exact (R22Ring.two_mul_eq_zero_iff _).mp <| by
      calc
        (2 : R22Ring) * e R22Ring.eta2 = e 2 * e R22Ring.eta2 := by rw [map_ofNat e 2]
        _ = e (2 * R22Ring.eta2) := (map_mul e 2 R22Ring.eta2).symm
        _ = e 0 := by rw [show (2 : R22Ring) * R22Ring.eta2 = 0 by decide]
        _ = 0 := map_zero e

private lemma r22_aut_eq_mat (e : R22Ring ≃+* R22Ring) (x : R22Ring) :
    e x = ⟨x.a,
      ringAutToMat e 0 0 * x.b1 + ringAutToMat e 0 1 * x.b2,
      ringAutToMat e 1 0 * x.b1 + ringAutToMat e 1 1 * x.b2⟩ := by
  obtain ⟨h1a, h2a⟩ := r22_aut_eta_fst_zero e
  rcases R2Ring.zmod2_eq_zero_or_one x.b1 with hb1 | hb1 <;>
    rcases R2Ring.zmod2_eq_zero_or_one x.b2 with hb2 | hb2
  · have hx : x = (x.a : R22Ring) := R22Ring.ext rfl hb1 hb2
    conv_lhs => rw [hx, map_intCast]
    ext <;> simp [ringAutToMat, hb1, hb2]
  · have hx : x = (x.a : R22Ring) + R22Ring.eta2 := by ext <;> simp [R22Ring.eta2, hb1, hb2]
    conv_lhs => rw [hx, map_add, map_intCast]
    ext <;> simp [ringAutToMat, h2a, hb1, hb2]
  · have hx : x = (x.a : R22Ring) + R22Ring.eta1 := by ext <;> simp [R22Ring.eta1, hb1, hb2]
    conv_lhs => rw [hx, map_add, map_intCast]
    ext <;> simp [ringAutToMat, h1a, hb1, hb2]
  · have hx : x = (x.a : R22Ring) + R22Ring.eta1 + R22Ring.eta2 := by
      ext <;> simp [R22Ring.eta1, R22Ring.eta2, hb1, hb2]
    conv_lhs => rw [hx, map_add, map_add, map_intCast]
    ext <;> simp [ringAutToMat, h1a, h2a, hb1, hb2]

/-- Group isomorphism `(R_{2,2} ≃+* R_{2,2}) ≃* GL₂(𝔽₂)` (`|Aut(R_{2,2})| = 6`). -/
def r22AutEquivGL2 : (R22Ring ≃+* R22Ring) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) where
  toFun e :=
    ⟨ringAutToMat e, ringAutToMat e.symm,
      by
        have he1 := r22_aut_eq_mat e (e.symm R22Ring.eta1)
        have he2 := r22_aut_eq_mat e (e.symm R22Ring.eta2)
        rw [e.apply_symm_apply] at he1 he2
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
            ringAutToMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_fin_one, Matrix.cons_val_one]
        · split_ifs with h
          · exact (congrArg R22Ring.b1 he1).symm
          · exact False.elim (h trivial)
        · split_ifs with h
          · cases h
          · exact (congrArg R22Ring.b1 he2).symm
        · split_ifs with h
          · cases h
          · exact (congrArg R22Ring.b2 he1).symm
        · split_ifs with h
          · exact (congrArg R22Ring.b2 he2).symm
          · exact False.elim (h trivial),
      by
        have he1 := r22_aut_eq_mat e.symm (e R22Ring.eta1)
        have he2 := r22_aut_eq_mat e.symm (e R22Ring.eta2)
        rw [e.symm_apply_apply] at he1 he2
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
            ringAutToMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_fin_one, Matrix.cons_val_one]
        · split_ifs with h
          · exact (congrArg R22Ring.b1 he1).symm
          · exact False.elim (h trivial)
        · split_ifs with h
          · cases h
          · exact (congrArg R22Ring.b1 he2).symm
        · split_ifs with h
          · cases h
          · exact (congrArg R22Ring.b2 he1).symm
        · split_ifs with h
          · exact (congrArg R22Ring.b2 he2).symm
          · exact False.elim (h trivial)⟩
  invFun g := mat2RingEquiv g
  left_inv e := by
    apply RingEquiv.ext
    intro x
    exact (r22_aut_eq_mat e x).symm
  right_inv g := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat2RingEquiv, ringAutToMat, R22Ring.eta1, R22Ring.eta2]
  map_mul' e₁ e₂ := by
    ext i j
    have hm := r22_aut_eq_mat e₁ (e₂ R22Ring.eta1)
    have hn := r22_aut_eq_mat e₁ (e₂ R22Ring.eta2)
    fin_cases i <;> fin_cases j <;>
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ringAutToMat,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
        Matrix.cons_val_one]
    · exact congrArg R22Ring.b1 hm
    · exact congrArg R22Ring.b1 hn
    · exact congrArg R22Ring.b2 hm
    · exact congrArg R22Ring.b2 hn

theorem r22LiftIso_iff_gl2_conj (M N : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    R22LiftIso (r22AugLiftEquivMatrix.symm M) (r22AugLiftEquivMatrix.symm N) ↔
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2), g.val * M = N * g.val := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨r22AutEquivGL2 e, ?_⟩
    obtain ⟨h1a, h2a⟩ := r22_aut_eta_fst_zero e
    have h1 := he R22Ring.eta1
    have h2 := he R22Ring.eta2
    have hL1 : (r22AugLiftEquivMatrix.symm M).1.delta R22Ring.eta1 = ⟨0, M 0 0, M 1 0⟩ := by
      ext <;> simp [r22AugLiftEquivMatrix, deltaRing2_add_frobDerivation2, r22BaseDelta,
        r22BaseDeltaMap, intDelta, r22MatDer, R22Ring.eta1]
    have hL2 : (r22AugLiftEquivMatrix.symm M).1.delta R22Ring.eta2 = ⟨0, M 0 1, M 1 1⟩ := by
      ext <;> simp [r22AugLiftEquivMatrix, deltaRing2_add_frobDerivation2, r22BaseDelta,
        r22BaseDeltaMap, intDelta, r22MatDer, R22Ring.eta2]
    rw [hL1, r22_aut_eq_mat e ⟨0, M 0 0, M 1 0⟩] at h1
    rw [hL2, r22_aut_eq_mat e ⟨0, M 0 1, M 1 1⟩] at h2
    have h1' := r22_aut_eq_mat e R22Ring.eta1
    have h2' := r22_aut_eq_mat e R22Ring.eta2
    have hm11 : (r22AugLiftEquivMatrix.symm N).1.delta (e R22Ring.eta1) =
        ⟨0, N 0 0 * ringAutToMat e 0 0 + N 0 1 * ringAutToMat e 1 0,
            N 1 0 * ringAutToMat e 0 0 + N 1 1 * ringAutToMat e 1 0⟩ := by
      rw [h1']
      ext <;> simp [r22AugLiftEquivMatrix, deltaRing2_add_frobDerivation2, r22BaseDelta,
        r22BaseDeltaMap, intDelta, r22MatDer, R22Ring.eta1]
    have hm22 : (r22AugLiftEquivMatrix.symm N).1.delta (e R22Ring.eta2) =
        ⟨0, N 0 0 * ringAutToMat e 0 1 + N 0 1 * ringAutToMat e 1 1,
            N 1 0 * ringAutToMat e 0 1 + N 1 1 * ringAutToMat e 1 1⟩ := by
      rw [h2']
      ext <;> simp [r22AugLiftEquivMatrix, deltaRing2_add_frobDerivation2, r22BaseDelta,
        r22BaseDeltaMap, intDelta, r22MatDer, R22Ring.eta2]
    rw [hm11] at h1
    rw [hm22] at h2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, r22AutEquivGL2,
        MulEquiv.coe_mk, Equiv.coe_fn_mk, Units.val_mk]
    · exact congrArg R22Ring.b1 h1
    · exact congrArg R22Ring.b1 h2
    · exact congrArg R22Ring.b2 h1
    · exact congrArg R22Ring.b2 h2
  · rintro ⟨g, hg⟩
    refine ⟨mat2RingEquiv g, fun x ↦ ?_⟩
    have h00 := congrFun (congrFun hg 0) 0
    have h01 := congrFun (congrFun hg 0) 1
    have h10 := congrFun (congrFun hg 1) 0
    have h11 := congrFun (congrFun hg 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    ext
    · rfl
    · simp only [mat2RingEquiv, r22AugLiftEquivMatrix, deltaRing2_add_frobDerivation2,
        r22BaseDelta, r22BaseDeltaMap, r22MatDer]
      calc
        g.val 0 0 * ((x.a : ZMod 2) * x.b1 + (M 0 0 * x.b1 + M 0 1 * x.b2)) +
            g.val 0 1 * ((x.a : ZMod 2) * x.b2 + (M 1 0 * x.b1 + M 1 1 * x.b2))
            = (x.a : ZMod 2) * (g.val 0 0 * x.b1 + g.val 0 1 * x.b2) +
                ((g.val 0 0 * M 0 0 + g.val 0 1 * M 1 0) * x.b1 +
                  (g.val 0 0 * M 0 1 + g.val 0 1 * M 1 1) * x.b2) := by ring
        _ = (x.a : ZMod 2) * (g.val 0 0 * x.b1 + g.val 0 1 * x.b2) +
              ((N 0 0 * g.val 0 0 + N 0 1 * g.val 1 0) * x.b1 +
                (N 0 0 * g.val 0 1 + N 0 1 * g.val 1 1) * x.b2) := by rw [h00, h01]
        _ = (x.a : ZMod 2) * (g.val 0 0 * x.b1 + g.val 0 1 * x.b2) +
              (N 0 0 * (g.val 0 0 * x.b1 + g.val 0 1 * x.b2) +
                N 0 1 * (g.val 1 0 * x.b1 + g.val 1 1 * x.b2)) := by ring
    · simp only [mat2RingEquiv, r22AugLiftEquivMatrix, deltaRing2_add_frobDerivation2,
        r22BaseDelta, r22BaseDeltaMap, r22MatDer]
      calc
        g.val 1 0 * ((x.a : ZMod 2) * x.b1 + (M 0 0 * x.b1 + M 0 1 * x.b2)) +
            g.val 1 1 * ((x.a : ZMod 2) * x.b2 + (M 1 0 * x.b1 + M 1 1 * x.b2))
            = (x.a : ZMod 2) * (g.val 1 0 * x.b1 + g.val 1 1 * x.b2) +
                ((g.val 1 0 * M 0 0 + g.val 1 1 * M 1 0) * x.b1 +
                  (g.val 1 0 * M 0 1 + g.val 1 1 * M 1 1) * x.b2) := by ring
        _ = (x.a : ZMod 2) * (g.val 1 0 * x.b1 + g.val 1 1 * x.b2) +
              ((N 1 0 * g.val 0 0 + N 1 1 * g.val 1 0) * x.b1 +
                (N 1 0 * g.val 0 1 + N 1 1 * g.val 1 1) * x.b2) := by rw [h10, h11]
        _ = (x.a : ZMod 2) * (g.val 1 0 * x.b1 + g.val 1 1 * x.b2) +
              (N 1 0 * (g.val 0 0 * x.b1 + g.val 0 1 * x.b2) +
                N 1 1 * (g.val 1 0 * x.b1 + g.val 1 1 * x.b2)) := by ring

/-- Canonical representatives of the `6` `GL₂(𝔽₂)`-conjugacy orbits in `M₂(𝔽₂)`. -/
def canonMatRep : Fin 6 → Matrix (Fin 2) (Fin 2) (ZMod 2)
  | 0 => !![0, 0; 0, 0]
  | 1 => !![1, 0; 0, 1]
  | 2 => !![0, 1; 0, 0]
  | 3 => !![1, 0; 0, 0]
  | 4 => !![1, 1; 0, 1]
  | 5 => !![0, 1; 1, 1]

/-- Conjugation-invariant rational canonical form classifier `M₂(𝔽₂) → Fin 6`. -/
def mat2F2ClassIdx (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Fin 6 :=
  if M = 0 then 0
  else if M = 1 then 1
  else if M.det = 0 then (if M 0 0 + M 1 1 = 0 then 2 else 3)
  else if M 0 0 + M 1 1 = 0 then 4
  else 5

private lemma mat2F2_trace_conj {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)}
    {M N : Matrix (Fin 2) (Fin 2) (ZMod 2)} (h : g.val * M = N * g.val) :
    M 0 0 + M 1 1 = N 0 0 + N 1 1 := by
  have hg : M = (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val * N * g.val := by
    calc
      M = ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val * g.val) * M := by
            rw [g.inv_mul, one_mul]
      _ = (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val * (g.val * M) := by
            rw [Matrix.mul_assoc]
      _ = (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val * N * g.val := by
            rw [h, Matrix.mul_assoc]
  have hid : g.val * (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val = 1 :=
    g.mul_inv
  have h00 := congrFun (congrFun hid 0) 0
  have h01 := congrFun (congrFun hid 0) 1
  have h10 := congrFun (congrFun hid 1) 0
  have h11 := congrFun (congrFun hid 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, ↓reduceIte] at h00 h01 h10 h11
  rw [if_neg (by decide : (0 : Fin 2) ≠ 1)] at h01
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)] at h10
  rw [hg]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  calc
    (g⁻¹.val 0 0 * N 0 0 + g⁻¹.val 0 1 * N 1 0) * g.val 0 0 +
        (g⁻¹.val 0 0 * N 0 1 + g⁻¹.val 0 1 * N 1 1) * g.val 1 0 +
      ((g⁻¹.val 1 0 * N 0 0 + g⁻¹.val 1 1 * N 1 0) * g.val 0 1 +
        (g⁻¹.val 1 0 * N 0 1 + g⁻¹.val 1 1 * N 1 1) * g.val 1 1)
        = N 0 0 * (g.val 0 0 * g⁻¹.val 0 0 + g.val 0 1 * g⁻¹.val 1 0) +
          N 0 1 * (g.val 1 0 * g⁻¹.val 0 0 + g.val 1 1 * g⁻¹.val 1 0) +
          N 1 0 * (g.val 0 0 * g⁻¹.val 0 1 + g.val 0 1 * g⁻¹.val 1 1) +
          N 1 1 * (g.val 1 0 * g⁻¹.val 0 1 + g.val 1 1 * g⁻¹.val 1 1) := by ring
    _ = N 0 0 * 1 + N 0 1 * 0 + N 1 0 * 0 + N 1 1 * 1 := by rw [h00, h01, h10, h11]
    _ = N 0 0 + N 1 1 := by ring

private lemma mat2F2ClassIdx_conj_invariant {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)}
    {M N : Matrix (Fin 2) (Fin 2) (ZMod 2)} (h : g.val * M = N * g.val) :
    mat2F2ClassIdx M = mat2F2ClassIdx N := by
  have hdet : M.det = N.det := by
    have hd := congrArg Matrix.det h
    simp only [Matrix.det_mul] at hd
    have hdg : g.val.det = 1 := by
      have hmul : g.val.det * (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val.det = 1 := by
        rw [← Matrix.det_mul, g.mul_inv, Matrix.det_one]
      rcases R2Ring.zmod2_eq_zero_or_one g.val.det with h0 | h1
      · rw [h0, zero_mul] at hmul; cases hmul
      · exact h1
    simpa [hdg] using hd
  have hzero : M = 0 ↔ N = 0 := by
    constructor <;> intro hm
    · have := h
      rw [hm, Matrix.mul_zero] at this
      calc
        N = N * (g.val * (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val) := by
              rw [g.mul_inv, Matrix.mul_one]
        _ = (N * g.val) * (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val := by
              rw [Matrix.mul_assoc]
        _ = 0 := by rw [← this, Matrix.zero_mul]
    · have := h
      rw [hm, Matrix.zero_mul] at this
      calc
        M = ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val * g.val) * M := by
              rw [g.inv_mul, Matrix.one_mul]
        _ = (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val * (g.val * M) := by
              rw [Matrix.mul_assoc]
        _ = 0 := by rw [this, Matrix.mul_zero]
  have hone : M = 1 ↔ N = 1 := by
    constructor <;> intro hm
    · calc
        N = N * (g.val * (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val) := by
              rw [g.mul_inv, Matrix.mul_one]
        _ = (g.val * M) * (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val := by
              rw [← Matrix.mul_assoc, ← h]
        _ = 1 := by
              rw [hm, Matrix.mul_one]
              exact g.mul_inv
    · calc
        M = ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val * g.val) * M := by
              rw [g.inv_mul, Matrix.one_mul]
        _ = (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)).val * (N * g.val) := by
              rw [Matrix.mul_assoc, h]
        _ = 1 := by
              rw [hm, Matrix.one_mul]
              exact g.inv_mul
  have htr := mat2F2_trace_conj h
  simp only [mat2F2ClassIdx, hzero, hone, hdet, htr]

private lemma mat2F2_all_conj_canon :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 2),
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2),
        g.val * M = canonMatRep (mat2F2ClassIdx M) * g.val := by
  have hall : ∀ a b c d : ZMod 2,
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2),
        g.val * !![a, b; c, d] = canonMatRep (mat2F2ClassIdx !![a, b; c, d]) * g.val := by
    decide
  intro M
  have hM : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hM]
  exact hall (M 0 0) (M 0 1) (M 1 0) (M 1 1)

/-- Stage-3 `GL₂(𝔽₂)` orbit count over `R_{2,2}`: the `16` lifts fall into exactly `6`
non-isomorphic orbits. -/
theorem r22_iso_orbits_eq_six :
    letI : Fintype R22AugLift := Fintype.ofEquiv _ r22AugLiftEquivMatrix.symm
    letI : DecidableRel r22IsoSetoid.r := fun _ _ ↦ Classical.propDecidable _
    letI : Fintype (Quotient r22IsoSetoid) := @Quotient.fintype R22AugLift _ r22IsoSetoid _
    Fintype.card (Quotient r22IsoSetoid) = 6 := by
  let e : Quotient r22IsoSetoid ≃ Fin 6 :=
    { toFun := Quotient.lift (fun L ↦ mat2F2ClassIdx (r22AugLiftEquivMatrix L)) fun L₁ L₂ h ↦ by
        rw [show L₁ = r22AugLiftEquivMatrix.symm (r22AugLiftEquivMatrix L₁) from
          (r22AugLiftEquivMatrix.symm_apply_apply L₁).symm,
          show L₂ = r22AugLiftEquivMatrix.symm (r22AugLiftEquivMatrix L₂) from
          (r22AugLiftEquivMatrix.symm_apply_apply L₂).symm] at h
        rcases (r22LiftIso_iff_gl2_conj _ _).mp h with ⟨g, hg⟩
        exact mat2F2ClassIdx_conj_invariant hg
      invFun := fun i ↦ Quotient.mk r22IsoSetoid (r22AugLiftEquivMatrix.symm (canonMatRep i))
      left_inv := fun q ↦ Quotient.inductionOn q fun L ↦ by
        apply Quotient.sound
        rcases mat2F2_all_conj_canon (r22AugLiftEquivMatrix L) with ⟨g, hg⟩
        have hiso := (r22LiftIso_iff_gl2_conj (r22AugLiftEquivMatrix L)
          (canonMatRep (mat2F2ClassIdx (r22AugLiftEquivMatrix L)))).mpr ⟨g, hg⟩
        have hsym := r22IsoSetoid.symm hiso
        simpa [r22AugLiftEquivMatrix.symm_apply_apply] using hsym
      right_inv := fun i ↦ by
        change mat2F2ClassIdx
          (r22AugLiftEquivMatrix (r22AugLiftEquivMatrix.symm (canonMatRep i))) = i
        rw [r22AugLiftEquivMatrix.apply_symm_apply]
        fin_cases i <;> decide }
  letI : Fintype R22AugLift := Fintype.ofEquiv _ r22AugLiftEquivMatrix.symm
  letI : DecidableRel r22IsoSetoid.r := fun _ _ ↦ Classical.propDecidable _
  letI instQ : Fintype (Quotient r22IsoSetoid) := @Quotient.fintype R22AugLift _ r22IsoSetoid _
  exact (@Fintype.card_congr _ _ instQ _ e).trans (Fintype.card_fin 6)

/-! ### Finite Group-Cohomology Leray Transgressive Cancellation on `SL(2, ZMod 5)` -/

/-- Special linear group `SL(2, 𝔽₅)` of order `120`, carrying decidable equality. -/
abbrev SL2F5 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)

instance : DecidableEq SL2F5 :=
  fun a b ↦ decidable_of_iff' _ (Matrix.SpecialLinearGroup.ext_iff a b)

/-- Upper unitriangular transvection `[[1, t], [0, 1]] ∈ SL₂(𝔽₅)`. -/
def sl2U (t : ZMod 5) : SL2F5 :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- Lower unitriangular transvection `[[1, 0], [t, 1]] ∈ SL₂(𝔽₅)`. -/
def sl2L (t : ZMod 5) : SL2F5 :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

/-- Diagonal torus elements `diag(2, 3), diag(3, 2) ∈ SL₂(𝔽₅)`. -/
def sl2D2 : SL2F5 := ⟨!![2, 0; 0, 3], by decide⟩
def sl2D3 : SL2F5 := ⟨!![3, 0; 0, 2], by decide⟩

private lemma sl2U_mul (s t : ZMod 5) : sl2U s * sl2U t = sl2U (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2U, Matrix.mul_apply]
  ring

private lemma sl2L_mul (s t : ZMod 5) : sl2L s * sl2L t = sl2L (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2L, Matrix.mul_apply]

private lemma sl2U_one_commutator : sl2U 1 = ⁅sl2D2, sl2U 2⁆ := by decide
private lemma sl2L_one_commutator : sl2L 1 = ⁅sl2D3, sl2L 2⁆ := by decide

private lemma sl2U_mem_commutator (t : ZMod 5) : sl2U t ∈ commutator SL2F5 := by
  have h1 : sl2U 1 ∈ commutator SL2F5 := by
    rw [sl2U_one_commutator]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top sl2D2) (Subgroup.mem_top (sl2U 2))
  have h2 : sl2U 2 ∈ commutator SL2F5 := by
    rw [show (2 : ZMod 5) = 1 + 1 by decide, ← sl2U_mul]; exact Subgroup.mul_mem _ h1 h1
  have h3 : sl2U 3 ∈ commutator SL2F5 := by
    rw [show (3 : ZMod 5) = 2 + 1 by decide, ← sl2U_mul]; exact Subgroup.mul_mem _ h2 h1
  have h4 : sl2U 4 ∈ commutator SL2F5 := by
    rw [show (4 : ZMod 5) = 3 + 1 by decide, ← sl2U_mul]; exact Subgroup.mul_mem _ h3 h1
  have h0 : sl2U 0 ∈ commutator SL2F5 := by
    rw [show sl2U 0 = 1 by decide]; exact Subgroup.one_mem _
  fin_cases t <;> assumption

private lemma sl2L_mem_commutator (t : ZMod 5) : sl2L t ∈ commutator SL2F5 := by
  have h1 : sl2L 1 ∈ commutator SL2F5 := by
    rw [sl2L_one_commutator]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top sl2D3) (Subgroup.mem_top (sl2L 2))
  have h2 : sl2L 2 ∈ commutator SL2F5 := by
    rw [show (2 : ZMod 5) = 1 + 1 by decide, ← sl2L_mul]; exact Subgroup.mul_mem _ h1 h1
  have h3 : sl2L 3 ∈ commutator SL2F5 := by
    rw [show (3 : ZMod 5) = 2 + 1 by decide, ← sl2L_mul]; exact Subgroup.mul_mem _ h2 h1
  have h4 : sl2L 4 ∈ commutator SL2F5 := by
    rw [show (4 : ZMod 5) = 3 + 1 by decide, ← sl2L_mul]; exact Subgroup.mul_mem _ h3 h1
  have h0 : sl2L 0 ∈ commutator SL2F5 := by
    rw [show sl2L 0 = 1 by decide]; exact Subgroup.one_mem _
  fin_cases t <;> assumption

private lemma zmod5_mul_cube (c : ZMod 5) (hc : c ≠ 0) : c * c ^ 3 = 1 := by
  fin_cases c <;> simp at hc <;> decide

private lemma sl2_bruhat_mul_entries (a b c : ZMod 5) :
    (sl2U a * sl2L b * sl2U c).1 0 0 = 1 + a * b ∧
    (sl2U a * sl2L b * sl2U c).1 0 1 = (1 + a * b) * c + a ∧
    (sl2U a * sl2L b * sl2U c).1 1 0 = b ∧
    (sl2U a * sl2L b * sl2U c).1 1 1 = b * c + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [Matrix.SpecialLinearGroup.coe_mul, sl2U, sl2L, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one]
    ring

private lemma sl2_bruhat_mul (a b c : ZMod 5) :
    (sl2U a * sl2L b * sl2U c).1 = !![1 + a * b, (1 + a * b) * c + a; b, b * c + 1] := by
  have ⟨h00, h01, h10, h11⟩ := sl2_bruhat_mul_entries a b c
  ext i j
  fin_cases i <;> fin_cases j <;> first | exact h00 | exact h01 | exact h10 | exact h11

private lemma sl2_bruhat_of_c_ne_zero (g : SL2F5) (hc : g.1 1 0 ≠ 0) :
    g = sl2U ((g.1 0 0 - 1) * g.1 1 0 ^ 3) * sl2L (g.1 1 0) *
      sl2U ((g.1 1 1 - 1) * g.1 1 0 ^ 3) := by
  have hu : g.1 1 0 * g.1 1 0 ^ 3 = 1 := zmod5_mul_cube (g.1 1 0) hc
  have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two g.1]
    exact g.2
  ext i j
  rw [sl2_bruhat_mul]
  fin_cases i <;> fin_cases j
  · calc
      g.1 0 0 = 1 + (g.1 0 0 - 1) * (g.1 1 0 * g.1 1 0 ^ 3) := by rw [hu]; ring
      _ = 1 + (g.1 0 0 - 1) * g.1 1 0 ^ 3 * g.1 1 0 := by ring
  · have hbc : g.1 0 1 * g.1 1 0 = g.1 0 0 * g.1 1 1 - 1 := by
      have := congrArg (· + g.1 0 1 * g.1 1 0 - 1) hdet
      ring_nf at this ⊢
      exact this.symm
    calc
      g.1 0 1 = (g.1 0 1 * g.1 1 0) * g.1 1 0 ^ 3 := by rw [mul_assoc, hu, mul_one]
      _ = (g.1 0 0 * g.1 1 1 - 1) * g.1 1 0 ^ 3 := by rw [hbc]
      _ = ((g.1 0 0 - 1) * (g.1 1 1 - 1) * g.1 1 0 ^ 3) * (g.1 1 0 * g.1 1 0 ^ 3) +
            (g.1 1 1 - 1) * g.1 1 0 ^ 3 + (g.1 0 0 - 1) * g.1 1 0 ^ 3 := by
            rw [hu]; ring
      _ = (1 + (g.1 0 0 - 1) * g.1 1 0 ^ 3 * g.1 1 0) * ((g.1 1 1 - 1) * g.1 1 0 ^ 3) +
            (g.1 0 0 - 1) * g.1 1 0 ^ 3 := by ring
  · rfl
  · calc
      g.1 1 1 = (g.1 1 1 - 1) * (g.1 1 0 * g.1 1 0 ^ 3) + 1 := by rw [hu]; ring
      _ = g.1 1 0 * ((g.1 1 1 - 1) * g.1 1 0 ^ 3) + 1 := by ring

/-- **Perfection of `SL₂(𝔽₅)` (`commutator_sl2_f5_eq_top`):** Every element of `SL₂(𝔽₅)` is a
product of commutators (`[SL₂(𝔽₅), SL₂(𝔽₅)] = SL₂(𝔽₅)`). -/
theorem commutator_sl2_f5_eq_top : commutator SL2F5 = ⊤ := by
  rw [eq_top_iff]
  intro g _
  by_cases hc : g.1 1 0 ≠ 0
  · rw [sl2_bruhat_of_c_ne_zero g hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (sl2U_mem_commutator _) (sl2L_mem_commutator _))
      (sl2U_mem_commutator _)
  · have hc0 : g.1 1 0 = 0 := not_not.mp hc
    have hd_ne : (g * sl2L 1).1 1 0 ≠ 0 := by
      have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
        rw [← Matrix.det_fin_two g.1]
        exact g.2
      rw [hc0, mul_zero, sub_zero] at hdet
      simp only [Matrix.SpecialLinearGroup.coe_mul, sl2L, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
        Matrix.cons_val_one, hc0, mul_one, zero_add]
      intro hd0
      rw [hd0, mul_zero] at hdet
      exact absurd hdet (by decide)
    have hprod : g * sl2L 1 ∈ commutator SL2F5 := by
      rw [sl2_bruhat_of_c_ne_zero (g * sl2L 1) hd_ne]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (sl2U_mem_commutator _) (sl2L_mem_commutator _))
        (sl2U_mem_commutator _)
    have hlinv : sl2L (-1) = (sl2L 1)⁻¹ := by
      apply mul_eq_one_iff_eq_inv.mp
      rw [sl2L_mul]
      decide
    have hfin : (g * sl2L 1) * sl2L (-1) = g := by
      rw [hlinv, mul_inv_cancel_right]
    rw [← hfin]
    exact Subgroup.mul_mem _ hprod (sl2L_mem_commutator (-1))

/-- Consequently, `H¹(SL₂(𝔽₅); ℤ/2ℤ) = Hom(SL₂(𝔽₅), ℤ/2ℤ)` vanishes identically. -/
theorem h1_sl2_f5_zmod2_subsingleton :
    Subsingleton (SL2F5 →* Multiplicative (ZMod 2)) := by
  refine ⟨fun φ ψ ↦ ?_⟩
  ext g
  have h1 : ∀ f : SL2F5 →* Multiplicative (ZMod 2), ∀ x ∈ commutator SL2F5, f x = 1 := by
    intro f x hx
    exact f.mem_ker.mp (Abelianization.commutator_subset_ker f hx)
  have htop : g ∈ commutator SL2F5 := commutator_sl2_f5_eq_top.symm ▸ Subgroup.mem_top g
  rw [h1 φ g htop, h1 ψ g htop]

/-- Central involution `-I = diag(4, 4) ∈ SL₂(𝔽₅)`. -/
def negOneSL2F5 : SL2F5 := ⟨!![4, 0; 0, 4], by decide⟩

lemma negOneSL2F5_sq : negOneSL2F5 * negOneSL2F5 = 1 := by decide
lemma negOneSL2F5_ne_one : negOneSL2F5 ≠ 1 := by decide

lemma negOneSL2F5_comm (g : SL2F5) : g * negOneSL2F5 = negOneSL2F5 * g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negOneSL2F5, Matrix.mul_apply] <;> ring

/-- Center `{±I}` of `SL₂(𝔽₅)` packaged as a normal subgroup. -/
def centerSL2F5 : Subgroup SL2F5 where
  carrier := {1, negOneSL2F5}
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · simp
    · simp
    · simp
    · simp [negOneSL2F5_sq]
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl)
    · simp
    · exact Or.inr (inv_eq_of_mul_eq_one_left negOneSL2F5_sq)

instance : centerSL2F5.Normal where
  conj_mem a ha g := by
    rcases ha with rfl | rfl
    · simp [centerSL2F5]
    · exact Or.inr (by
        calc
          g * negOneSL2F5 * g⁻¹ = (negOneSL2F5 * g) * g⁻¹ := by rw [negOneSL2F5_comm]
          _ = negOneSL2F5 := mul_inv_cancel_right negOneSL2F5 g)

lemma centerSL2F5_comm (z : centerSL2F5) (g : SL2F5) : g * z.1 = z.1 * g := by
  rcases z.2 with hz | hz
  · simp [hz]
  · rw [hz, negOneSL2F5_comm]

/-- Projective special linear quotient `A₅ ≅ PSL₂(𝔽₅) = SL₂(𝔽₅) / {±I}`. -/
abbrev PSL2F5 : Type := SL2F5 ⧸ centerSL2F5

private def sl2Code (g : SL2F5) : ℕ :=
  ((g.1 0 0).val * 125 + (g.1 0 1).val * 25 + (g.1 1 0).val * 5 + (g.1 1 1).val)

private def cosetPick (g : SL2F5) : SL2F5 :=
  if sl2Code g ≤ sl2Code (g * negOneSL2F5) then g else g * negOneSL2F5

/-- Deterministic choice-free section `PSL₂(𝔽₅) → SL₂(𝔽₅)` selecting the smaller `sl2Code` in
each `{g, -g}` coset. -/
@[irreducible] def psl2Sec : PSL2F5 → SL2F5 :=
  Quotient.lift cosetPick fun a b hab ↦ by
    have hmem : a⁻¹ * b ∈ centerSL2F5 := QuotientGroup.leftRel_apply.mp hab
    rcases hmem with h1 | hneg
    · have : a = b := eq_of_inv_mul_eq_one h1
      subst this; rfl
    · have hb : b = a * negOneSL2F5 := inv_mul_eq_iff_eq_mul.mp hneg
      subst hb
      have hba : a * negOneSL2F5 * negOneSL2F5 = a := by
        rw [mul_assoc, negOneSL2F5_sq, mul_one]
      have hne : sl2Code a ≠ sl2Code (a * negOneSL2F5) := by
        intro hcd
        have hlt00 := ZMod.val_lt (a.1 0 0)
        have hlt01 := ZMod.val_lt (a.1 0 1)
        have hlt10 := ZMod.val_lt (a.1 1 0)
        have hlt11 := ZMod.val_lt (a.1 1 1)
        have hlt00' := ZMod.val_lt ((a * negOneSL2F5).1 0 0)
        have hlt01' := ZMod.val_lt ((a * negOneSL2F5).1 0 1)
        have hlt10' := ZMod.val_lt ((a * negOneSL2F5).1 1 0)
        have hlt11' := ZMod.val_lt ((a * negOneSL2F5).1 1 1)
        unfold sl2Code at hcd
        have h00 : (a.1 0 0).val = ((a * negOneSL2F5).1 0 0).val := by omega
        have h01 : (a.1 0 1).val = ((a * negOneSL2F5).1 0 1).val := by omega
        have h10 : (a.1 1 0).val = ((a * negOneSL2F5).1 1 0).val := by omega
        have h11 : (a.1 1 1).val = ((a * negOneSL2F5).1 1 1).val := by omega
        have heq : a = a * negOneSL2F5 := by
          ext i j
          fin_cases i <;> fin_cases j <;> apply ZMod.val_injective 5 <;> assumption
        have h1 : negOneSL2F5 = 1 := by
          calc
            negOneSL2F5 = a⁻¹ * (a * negOneSL2F5) := by rw [inv_mul_cancel_left]
            _ = a⁻¹ * a := by rw [← heq]
            _ = 1 := inv_mul_cancel a
        exact negOneSL2F5_ne_one h1
      dsimp only [cosetPick]
      rw [hba]
      split_ifs with h1 h2 h2
      · omega
      · rfl
      · rfl
      · omega

theorem psl2Sec_mk (x : PSL2F5) : QuotientGroup.mk (psl2Sec x) = x := by
  refine Quotient.inductionOn x fun g ↦ ?_
  unfold psl2Sec
  change QuotientGroup.mk (cosetPick g) = QuotientGroup.mk g
  dsimp only [cosetPick]
  split_ifs
  · rfl
  · symm
    exact QuotientGroup.eq.mpr (by
      rw [show g⁻¹ * (g * negOneSL2F5) = negOneSL2F5 by rw [← mul_assoc, inv_mul_cancel, one_mul]]
      exact Or.inr rfl)

/-- Non-trivial sign character `sgnChar : {±I} →* Multiplicative (ZMod 2)` mapping `-I ↦ -1`. -/
def sgnChar : centerSL2F5 →* Multiplicative (ZMod 2) where
  toFun z := Multiplicative.ofAdd (if z.1 = 1 then 0 else 1)
  map_one' := rfl
  map_mul' a b := by
    rcases a with ⟨xa, ha⟩
    rcases b with ⟨xb, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · decide
    · decide
    · decide
    · have hmul : (⟨negOneSL2F5, Or.inr rfl⟩ : centerSL2F5) * ⟨negOneSL2F5, Or.inr rfl⟩ = 1 :=
        Subtype.ext negOneSL2F5_sq
      rw [hmul]
      rfl

theorem sgnChar_negOne : sgnChar ⟨negOneSL2F5, Or.inr rfl⟩ ≠ 1 := by
  decide

/-- Group 2-cocycles `Q × Q → A` with trivial `Q`-action on an abelian group `A` (`CommGroup`). -/
@[ext]
structure TwoCocycle (Q : Type u) (A : Type v) [Group Q] [CommGroup A] : Type (max u v) where
  /-- Cocycle 2-cochain `c(x, y)`. -/
  c : Q → Q → A
  /-- Associativity 2-cocycle condition `c(x, y) c(xy, z) = c(y, z) c(x, yz)`. -/
  cocycle : ∀ x y z : Q, c x y * c (x * y) z = c y z * c x (y * z)

/-- A 2-cocycle `c` is a 2-coboundary iff `∃ β : Q → A, c(x, y) = β(x) β(y) β(xy)⁻¹`. -/
def IsTwoCoboundary {Q : Type u} {A : Type v} [Group Q] [CommGroup A] (c : TwoCocycle Q A) : Prop :=
  ∃ β : Q → A, ∀ x y : Q, c.c x y = β x * β y * (β (x * y))⁻¹

private def twoCocycleMul {Q : Type u} {A : Type v} [Group Q] [CommGroup A]
    (c₁ c₂ : TwoCocycle Q A) : TwoCocycle Q A where
  c x y := c₁.c x y * c₂.c x y
  cocycle x y z := by
    calc
      c₁.c x y * c₂.c x y * (c₁.c (x * y) z * c₂.c (x * y) z)
          = (c₁.c x y * c₁.c (x * y) z) * (c₂.c x y * c₂.c (x * y) z) := by
              simp only [mul_assoc, mul_left_comm]
      _ = (c₁.c y z * c₁.c x (y * z)) * (c₂.c y z * c₂.c x (y * z)) := by
            rw [c₁.cocycle, c₂.cocycle]
      _ = c₁.c y z * c₂.c y z * (c₁.c x (y * z) * c₂.c x (y * z)) := by
            simp only [mul_assoc, mul_left_comm]

instance {Q : Type u} {A : Type v} [Group Q] [CommGroup A] :
    CommGroup (TwoCocycle Q A) where
  one := ⟨fun _ _ ↦ 1, fun _ _ _ ↦ by simp⟩
  mul := twoCocycleMul
  inv c := ⟨fun x y ↦ (c.c x y)⁻¹, fun x y z ↦ by
    have h := congrArg (·⁻¹) (c.cocycle x y z)
    simpa [mul_inv, mul_comm] using h⟩
  mul_assoc a b c := by ext x y; exact mul_assoc _ _ _
  one_mul a := by ext x y; exact one_mul _
  mul_one a := by ext x y; exact mul_one _
  inv_mul_cancel a := by ext x y; exact inv_mul_cancel _
  mul_comm a b := by ext x y; exact mul_comm _ _

/-- Normal subgroup of 2-coboundaries inside `TwoCocycle Q A`. -/
def twoCoboundarySubgroup (Q : Type u) (A : Type v) [Group Q] [CommGroup A] :
    Subgroup (TwoCocycle Q A) where
  carrier := { c | IsTwoCoboundary c }
  mul_mem' := by
    rintro c₁ c₂ ⟨β₁, h₁⟩ ⟨β₂, h₂⟩
    refine ⟨fun x ↦ β₁ x * β₂ x, fun x y ↦ ?_⟩
    change c₁.c x y * c₂.c x y = _
    rw [h₁ x y, h₂ x y, mul_inv]
    simp only [mul_assoc, mul_left_comm, mul_comm]
  one_mem' := ⟨fun _ ↦ 1, fun _ _ ↦ by change (1 : A) = 1 * 1 * 1⁻¹; simp⟩
  inv_mem' := by
    rintro c ⟨β, h⟩
    refine ⟨fun x ↦ (β x)⁻¹, fun x y ↦ ?_⟩
    change (c.c x y)⁻¹ = _
    rw [h x y]
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- Group cohomology `H²(Q; A)` with trivial action of `Q` on `A`. -/
abbrev H2Trivial (Q : Type u) (A : Type v) [Group Q] [CommGroup A] : Type (max u v) :=
  TwoCocycle Q A ⧸ twoCoboundarySubgroup Q A

private lemma schreierFactor_mem (x y : PSL2F5) :
    (psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y ∈ centerSL2F5 := by
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' centerSL2F5 ((psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y) = 1
  rw [map_mul, map_mul, map_inv]
  change (QuotientGroup.mk (psl2Sec (x * y)))⁻¹ *
    QuotientGroup.mk (psl2Sec x) * QuotientGroup.mk (psl2Sec y) = 1
  rw [psl2Sec_mk, psl2Sec_mk, psl2Sec_mk]
  simp

private lemma center_factor_assoc {G : Type*} [Group G] {Z : Subgroup G}
    (hcomm : ∀ z : Z, ∀ g : G, g * z.1 = z.1 * g)
    {a b c ab bc abc : G}
    (hab : ab⁻¹ * a * b ∈ Z) (hbc : bc⁻¹ * b * c ∈ Z) :
    (ab⁻¹ * a * b) * (abc⁻¹ * ab * c) = (bc⁻¹ * b * c) * (abc⁻¹ * a * bc) := by
  have hc1 : (ab⁻¹ * a * b) * abc⁻¹ = abc⁻¹ * (ab⁻¹ * a * b) := (hcomm ⟨_, hab⟩ abc⁻¹).symm
  have hc2 : (ab⁻¹ * a * b) * ab = ab * (ab⁻¹ * a * b) := (hcomm ⟨_, hab⟩ ab).symm
  have hc3 : (abc⁻¹ * a * bc) * (bc⁻¹ * b * c) = (bc⁻¹ * b * c) * (abc⁻¹ * a * bc) :=
    hcomm ⟨_, hbc⟩ (abc⁻¹ * a * bc)
  calc
    (ab⁻¹ * a * b) * (abc⁻¹ * ab * c)
        = ((ab⁻¹ * a * b) * abc⁻¹) * (ab * c) := by simp only [mul_assoc]
    _ = (abc⁻¹ * (ab⁻¹ * a * b)) * (ab * c) := by rw [hc1]
    _ = abc⁻¹ * (((ab⁻¹ * a * b) * ab) * c) := by simp only [mul_assoc]
    _ = abc⁻¹ * ((ab * (ab⁻¹ * a * b)) * c) := by rw [hc2]
    _ = abc⁻¹ * (a * b * c) := by simp only [mul_assoc, mul_inv_cancel_left]
    _ = abc⁻¹ * (a * (bc * (bc⁻¹ * b * c))) := by simp only [mul_assoc, mul_inv_cancel_left]
    _ = (abc⁻¹ * a * bc) * (bc⁻¹ * b * c) := by simp only [mul_assoc]
    _ = (bc⁻¹ * b * c) * (abc⁻¹ * a * bc) := hc3

private def schreierCocycle (χ : centerSL2F5 →* Multiplicative (ZMod 2)) :
    TwoCocycle PSL2F5 (Multiplicative (ZMod 2)) where
  c x y := χ ⟨(psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y, schreierFactor_mem x y⟩
  cocycle x y z := by
    rw [← map_mul, ← map_mul]
    apply congrArg χ
    apply Subtype.ext
    have hprod : x * y * z = x * (y * z) := mul_assoc x y z
    change ((psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y) *
        ((psl2Sec ((x * y) * z))⁻¹ * psl2Sec (x * y) * psl2Sec z) =
      ((psl2Sec (y * z))⁻¹ * psl2Sec y * psl2Sec z) *
        ((psl2Sec (x * (y * z)))⁻¹ * psl2Sec x * psl2Sec (y * z))
    rw [hprod]
    exact center_factor_assoc centerSL2F5_comm
      (schreierFactor_mem x y) (schreierFactor_mem y z)

/-- The 5-term Leray / Lyndon–Hochschild–Serre transgression
`d₂ : Hom({±I}, ℤ/2ℤ) →* H²(PSL₂(𝔽₅); ℤ/2ℤ)`. -/
def lerayTransgressionD2 :
    (centerSL2F5 →* Multiplicative (ZMod 2)) →* H2Trivial PSL2F5 (Multiplicative (ZMod 2)) where
  toFun χ := QuotientGroup.mk (schreierCocycle χ)
  map_one' := by
    change QuotientGroup.mk (1 : TwoCocycle PSL2F5 (Multiplicative (ZMod 2))) = 1
    rfl
  map_mul' χ₁ χ₂ := by
    change QuotientGroup.mk (schreierCocycle (χ₁ * χ₂)) =
      QuotientGroup.mk (schreierCocycle χ₁ * schreierCocycle χ₂)
    rfl

private lemma sec_quot_mem (g : SL2F5) :
    (psl2Sec (QuotientGroup.mk g))⁻¹ * g ∈ centerSL2F5 := by
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' centerSL2F5 ((psl2Sec (QuotientGroup.mk g))⁻¹ * g) = 1
  rw [map_mul, map_inv]
  change (QuotientGroup.mk (psl2Sec (QuotientGroup.mk g)))⁻¹ * QuotientGroup.mk g = 1
  rw [psl2Sec_mk, inv_mul_cancel]

private lemma psl2Sec_one_mem : psl2Sec 1 ∈ centerSL2F5 := by
  have h := sec_quot_mem (1 : SL2F5)
  change (psl2Sec 1)⁻¹ * 1 ∈ centerSL2F5 at h
  rw [mul_one] at h
  have hi := centerSL2F5.inv_mem h
  rwa [inv_inv] at hi

private lemma commGroup_coboundary_mul {A : Type*} [CommGroup A]
    (bx by_ bxy u1 u2 : A) :
    (bx * by_ * bxy⁻¹ * u1 * u2) * bxy = (u1 * bx) * (u2 * by_) := by
  calc
    (bx * by_ * bxy⁻¹ * u1 * u2) * bxy
        = (u1 * bx * (u2 * by_)) * (bxy⁻¹ * bxy) := by ac_rfl
    _ = (u1 * bx) * (u2 * by_) := by rw [inv_mul_cancel, mul_one]

/-- **5-Term Leray Exactness at `H¹ → H²`:** `d₂(χ) = 0 ∈ H²(PSL₂(𝔽₅); ℤ/2ℤ)` iff `χ` extends to a
character `φ : SL₂(𝔽₅) →* ℤ/2ℤ`. -/
theorem lerayTransgressionD2_eq_one_iff (χ : centerSL2F5 →* Multiplicative (ZMod 2)) :
    lerayTransgressionD2 χ = 1 ↔
      ∃ φ : SL2F5 →* Multiplicative (ZMod 2), φ.comp centerSL2F5.subtype = χ := by
  constructor
  · intro h
    change QuotientGroup.mk (schreierCocycle χ) = 1 at h
    rw [QuotientGroup.eq_one_iff] at h
    rcases h with ⟨β, hβ⟩
    let φ : SL2F5 →* Multiplicative (ZMod 2) :=
      { toFun := fun g ↦ χ ⟨(psl2Sec (QuotientGroup.mk g))⁻¹ * g, sec_quot_mem g⟩ *
          β (QuotientGroup.mk g)
        map_one' := by
          have h11 := hβ 1 1
          rw [mul_one] at h11
          have hβ1 : β 1 = (schreierCocycle χ).c 1 1 := by
            calc
              β 1 = β 1 * β 1 * (β 1)⁻¹ := by simp
              _ = (schreierCocycle χ).c 1 1 := h11.symm
          have hc1 : (schreierCocycle χ).c 1 1 = χ ⟨psl2Sec 1, psl2Sec_one_mem⟩ := by
            dsimp [schreierCocycle]
            apply congrArg χ
            apply Subtype.ext
            simp [inv_mul_cancel, one_mul]
          have hq1 : (QuotientGroup.mk (1 : SL2F5) : PSL2F5) = 1 := rfl
          have h1eq : (⟨(psl2Sec (QuotientGroup.mk (1 : SL2F5)))⁻¹ * 1, sec_quot_mem 1⟩ :
              centerSL2F5) = ⟨(psl2Sec 1)⁻¹, centerSL2F5.inv_mem psl2Sec_one_mem⟩ :=
            Subtype.ext (by simp [hq1])
          rw [h1eq, hq1, hβ1, hc1, ← map_mul]
          calc
            χ (⟨(psl2Sec 1)⁻¹, centerSL2F5.inv_mem psl2Sec_one_mem⟩ *
                ⟨psl2Sec 1, psl2Sec_one_mem⟩)
                = χ 1 := by apply congrArg χ; apply Subtype.ext; exact inv_mul_cancel _
            _ = 1 := map_one χ
        map_mul' := fun g₁ g₂ ↦ by
          let x : PSL2F5 := QuotientGroup.mk g₁
          let y : PSL2F5 := QuotientGroup.mk g₂
          have hxy : QuotientGroup.mk (g₁ * g₂) = x * y := rfl
          have hm1 : (⟨(psl2Sec (QuotientGroup.mk (g₁ * g₂)))⁻¹ * (g₁ * g₂),
              sec_quot_mem (g₁ * g₂)⟩ : centerSL2F5) =
              ⟨(psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y, schreierFactor_mem x y⟩ *
                ⟨(psl2Sec x)⁻¹ * g₁, sec_quot_mem g₁⟩ *
                ⟨(psl2Sec y)⁻¹ * g₂, sec_quot_mem g₂⟩ := by
            apply Subtype.ext
            have hq : QuotientGroup.mk (g₁ * g₂) = x * y := rfl
            change (psl2Sec (QuotientGroup.mk (g₁ * g₂)))⁻¹ * (g₁ * g₂) =
              ((psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y) *
                ((psl2Sec x)⁻¹ * g₁) * ((psl2Sec y)⁻¹ * g₂)
            rw [hq]
            have hc_comm := centerSL2F5_comm ⟨_, sec_quot_mem g₁⟩ (psl2Sec y)
            calc
              (psl2Sec (x * y))⁻¹ * (g₁ * g₂)
                  = (psl2Sec (x * y))⁻¹ * (psl2Sec x * ((psl2Sec x)⁻¹ * g₁)) *
                      (psl2Sec y * ((psl2Sec y)⁻¹ * g₂)) := by
                      simp only [mul_assoc, mul_inv_cancel_left]
              _ = (psl2Sec (x * y))⁻¹ * psl2Sec x *
                    (((psl2Sec x)⁻¹ * g₁) * psl2Sec y) * ((psl2Sec y)⁻¹ * g₂) := by
                    simp only [mul_assoc]
              _ = (psl2Sec (x * y))⁻¹ * psl2Sec x *
                    (psl2Sec y * ((psl2Sec x)⁻¹ * g₁)) * ((psl2Sec y)⁻¹ * g₂) := by
                    rw [hc_comm]
              _ = ((psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y) *
                    ((psl2Sec x)⁻¹ * g₁) * ((psl2Sec y)⁻¹ * g₂) := by
                    simp only [mul_assoc]
          rw [hm1, map_mul, map_mul]
          have hc_eq : χ ⟨(psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y, schreierFactor_mem x y⟩ =
              β x * β y * (β (x * y))⁻¹ := hβ x y
          rw [hc_eq, hxy]
          exact commGroup_coboundary_mul _ _ _ _ _ }
    refine ⟨φ, ?_⟩
    ext ⟨z, hz⟩
    change χ ⟨(psl2Sec (QuotientGroup.mk z))⁻¹ * z, sec_quot_mem z⟩ *
        β (QuotientGroup.mk z) = χ ⟨z, hz⟩
    have hqz : (QuotientGroup.mk z : PSL2F5) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hz
    have h11 := hβ 1 1
    rw [mul_one] at h11
    have hβ1 : β 1 = χ ⟨psl2Sec 1, psl2Sec_one_mem⟩ := by
      have h1' : β 1 = (schreierCocycle χ).c 1 1 := by
        calc
          β 1 = β 1 * β 1 * (β 1)⁻¹ := by simp
          _ = (schreierCocycle χ).c 1 1 := h11.symm
      rw [h1']
      dsimp [schreierCocycle]
      apply congrArg χ; apply Subtype.ext; simp [inv_mul_cancel, one_mul]
    have hzeq : (⟨(psl2Sec (QuotientGroup.mk z))⁻¹ * z, sec_quot_mem z⟩ : centerSL2F5) =
        ⟨(psl2Sec 1)⁻¹ * z, centerSL2F5.mul_mem (centerSL2F5.inv_mem psl2Sec_one_mem) hz⟩ :=
      Subtype.ext (congrArg (fun q : PSL2F5 ↦ (psl2Sec q)⁻¹ * z) hqz)
    rw [hzeq, hqz, hβ1, ← map_mul]
    apply congrArg χ; apply Subtype.ext
    have hcz := centerSL2F5_comm ⟨z, hz⟩ (psl2Sec 1)
    calc
      (psl2Sec 1)⁻¹ * z * psl2Sec 1 = (psl2Sec 1)⁻¹ * (psl2Sec 1 * z) := by
            rw [mul_assoc, ← hcz]
      _ = z := inv_mul_cancel_left _ _
  · rintro ⟨φ, hφ⟩
    change QuotientGroup.mk (schreierCocycle χ) = 1
    rw [QuotientGroup.eq_one_iff]
    refine ⟨fun x ↦ φ (psl2Sec x), fun x y ↦ ?_⟩
    have hext : χ ⟨(psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y, schreierFactor_mem x y⟩ =
        φ ((psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y) :=
      congrArg (fun f : centerSL2F5 →* Multiplicative (ZMod 2) ↦
        f ⟨(psl2Sec (x * y))⁻¹ * psl2Sec x * psl2Sec y, schreierFactor_mem x y⟩) hφ.symm
    change χ _ = _
    rw [hext, map_mul, map_mul, map_inv,
      mul_assoc (φ (psl2Sec (x * y)))⁻¹ (φ (psl2Sec x)) (φ (psl2Sec y)),
      mul_comm (φ (psl2Sec (x * y)))⁻¹ (φ (psl2Sec x) * φ (psl2Sec y))]

/-- **Finite Group-Cohomology Leray Transgressive Cancellation:**
On the central extension `1 → {±I} → SL₂(𝔽₅) → PSL₂(𝔽₅) → 1`, because `SL₂(𝔽₅)` is perfect
(`H¹(SL₂(𝔽₅); ℤ/2ℤ) = 0`), the Leray transgression `d₂` is injective and maps the non-trivial
center character `sgnChar` to a non-trivial class `0 ≠ d₂(sgnChar) ∈ H²(PSL₂(𝔽₅); ℤ/2ℤ)`. -/
theorem sl2_f5_leray_transgression_injective :
    Function.Injective lerayTransgressionD2 ∧ lerayTransgressionD2 sgnChar ≠ 1 := by
  have hinj : Function.Injective lerayTransgressionD2 := by
    rw [injective_iff_map_eq_one]
    intro χ hχ
    rcases (lerayTransgressionD2_eq_one_iff χ).mp hχ with ⟨φ, hφ⟩
    have htriv : φ = 1 := h1_sl2_f5_zmod2_subsingleton.elim φ 1
    rw [← hφ, htriv]
    ext z
    rfl
  refine ⟨hinj, ?_⟩
  intro h1
  have hs1 : sgnChar = 1 := hinj (h1.trans lerayTransgressionD2.map_one.symm)
  exact sgnChar_negOne (congrArg (fun f ↦ f ⟨negOneSL2F5, Or.inr rfl⟩) hs1)

end DeltaObstructionTower

/-! ## Section 4: Cross-Module Witness Registration Across `HomotopyCRM` -/

section CrossModuleRegistration

/-- Mode (i) registration of `T_odd` in `Nom` (`NominalSimplicity`): empty global sections over
`∅ : Finset ℕ`. -/
def nominalOddTorsorGlobalMode : SectionObstructionMode (Type 0) where
  total := { t : T_odd // ∀ σ ∈ pointwiseStabilizer (∅ : Finset ℕ), σ • t = t }
  base := Unit
  proj := fun _ ↦ ()

theorem isEmpty_nominalOddTorsor_sections :
    IsEmpty nominalOddTorsorGlobalMode.SectionSpace := by
  refine ⟨fun s ↦ isEmpty_t_odd_sections_empty.false (s.1 ())⟩

/-- Mode (i) registration of `FreshRootStream` in `Nom` (`NominalICaTT`): empty finitely
supported streams (`Nom`) vs. inhabited total streams (`Set` via `DC_ω`). -/
def nominalFreshRootStreamMode : SectionObstructionMode (Type 0) where
  total := { s : FreshRootStream // HasFiniteSupport s }
  base := Unit
  proj := fun _ ↦ ()

theorem nominalFreshRootStream_nom_vs_set :
    IsEmpty nominalFreshRootStreamMode.SectionSpace ∧ Nonempty FreshRootStream :=
  ⟨⟨fun s ↦ isEmpty_nominal_freshRootStream.false (s.1 ())⟩,
   (theorem9B_choice_calibration_of_coinductive_streams).2.1⟩

/-- Mode (i) / Double-Solvent registration of `E0Quotient` (`BorelTailResiduum`): ZFC linear
section exists while continuous `T₁`-separators vanish (`π₀^{T₁}(Q_{E₀}) ≃ 1`). -/
theorem borelE0_double_solvent_bridge :
    (∃ s : E0Quotient →ₗ[ZMod 2] CantorSpace, e0QuotientMk.comp s = LinearMap.id) ∧
      (¬ ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T1Space Y) (f : CantorSpace → Y),
        Continuous f ∧ (∀ z w : CantorSpace, E0Rel z w → f z = f w) ∧ ∃ a b, f a ≠ f b) :=
  ⟨exists_zfc_linear_section_e0Quotient, not_exists_continuous_t1_e0Separator⟩

/-- Mode (i) registration of the cubical amalgamation obstruction `facetCycleDiagram 3`
(`CubicalAmalgamation` & `DirectedFraisseSAP`). -/
theorem cubicalFacetCycle_mode_bridge :
    (∀ (Q : Type) [OrientedGradedPoset Q], IsFlowAcyclic Q →
      IsEmpty (CubicalCocone (facetCycleDiagram 3 (by decide)) Q)) :=
  fun _ _ hA ↦ no_flowAcyclic_cubical_amalgam_of_three_le 3 (by decide) hA

/-- Mode (i) / Adjoint bridge to `SetsResiduum`: `Def ⊣ π_Set` and `card_split_iff_global_choice`.
-/
noncomputable def setsDefProjBridge :
    HomotopyCRM.SetsResiduum.defFunctor.{0} ⊣ HomotopyCRM.SetsResiduum.piSetFunctor.{0} :=
  HomotopyCRM.SetsResiduum.defSetProjAdjunction

theorem setsCardSplitBridge (M : HomotopyCRM.SetsResiduum.SkeletalCardBase.{0, 0}) :
    HomotopyCRM.SetsResiduum.HomotopyCardSplitting M ↔
      HomotopyCRM.SetsResiduum.UniformSmallChoice.{0} :=
  HomotopyCRM.SetsResiduum.card_split_iff_global_choice M

/-- Mode (ii) registration of `OrdinalRankCompleteness` (`Theorem 9A`). -/
theorem ordinalRankCompletenessBridge {S : Type u} [RankedInfCat S]
    {θ : Ordinal.{0}} {s : S} (hrank : RankedInfCat.rank s ≤ θ)
    {x y : GlobularInfSystem.Obj s} {f : GlobularInfSystem.Obj (GlobularInfSystem.hom x y)} :
    IsOrdinalInv θ f ↔ IsEquiv f :=
  theorem9A_ordinal_rank_completeness hrank

/-- Mode (iii) bridge registering `DualInt` and `R₂` perfection vs. lift obstructions
(`DeltaRingPerfection`). -/
theorem deltaRingPerfectionModeBridge :
    ¬ IsPerfectDeltaRing DualInt ∧
      ¬ IsPerfectDeltaRing R2Delta0 ∧
      IsEmpty (DeltaRing2Cat.of R2Delta0 ≅ DeltaRing2Cat.of R2Delta1) :=
  ⟨DualInt.not_isPerfectDeltaRing, R2Delta0.not_isPerfectDeltaRing, r2Delta0_not_iso_r2Delta1⟩

end CrossModuleRegistration

/-! ## Section 5: Mandatory 4-Layer Lean 4 Definition Check Gate (`namespace Checks`) -/

namespace Checks

/-! ### Layer 1: Inhabitation (Non-Degeneracy of Formalized Carriers) -/

instance instNontrivialOmegaM1 : Nontrivial OmegaM1 :=
  ⟨⟨OmegaM1.bot, OmegaM1.top, by decide⟩⟩

instance instNontrivialR22Ring : Nontrivial R22Ring :=
  ⟨⟨0, R22Ring.eta1, by decide⟩⟩

instance instNontrivialTwoGroup : Nontrivial TwoGroup :=
  ⟨⟨1, ⟨true⟩, by decide⟩⟩

instance instNontrivialTestTopos : Nontrivial TestTopos :=
  ⟨⟨TestTopos.setTopos, TestTopos.setM1, by decide⟩⟩

instance instNontrivialM1Monoid : Nontrivial M1Monoid :=
  ⟨⟨⟨false⟩, ⟨true⟩, by decide⟩⟩

instance instNontrivialBZ2BotObj : Nontrivial BZ2BotObj :=
  ⟨⟨BZ2BotObj.bot, BZ2BotObj.star, by decide⟩⟩

instance instNontrivialFrobLiftRing2 : Nontrivial FrobLiftRing2.{0} :=
  ⟨⟨intFrobLift, zmod2FrobLift, fun h ↦ by
    have hEq := congrArg (fun F : FrobLiftRing2.{0} ↦ (2 : F.R) = 0) h
    have hz : (2 : ZMod 2) = 0 := by decide
    have hint : (2 : ℤ) = 0 := Eq.mpr hEq hz
    exact absurd hint (by decide)⟩⟩

instance instNontrivialVPoset : Nontrivial VPoset :=
  ⟨⟨VPoset.c, VPoset.a, by decide⟩⟩

instance instNontrivialDiamondPoset : Nontrivial DiamondPoset :=
  ⟨⟨DiamondPoset.bot, DiamondPoset.top, by decide⟩⟩

/-! ### Layer 2: Bidirectional Separation (Positive & Negative Witnesses) -/

/-- Layer 2 Beck–Chevalley separation: trivial square is Beck–Chevalley while `const PEmpty → 𝟭`
is not. -/
theorem layer2_sep_isBeckChevalley :
    let idSq : MateDoubleSquare (𝟭 (Type 0)) (𝟭 (Type 0))
        (𝟭 (Type 0)) (𝟭 (Type 0)) (𝟭 (Type 0)) (𝟭 (Type 0)) :=
      ⟨Adjunction.id, Adjunction.id, CategoryTheory.TwoSquare.mk _ _ _ _ (𝟙 _)⟩
    let emptySq : MateDoubleSquare ((Functor.const (Type 0)).obj PEmpty) (𝟭 (Type 0))
        (𝟭 (Type 0)) (𝟭 (Type 0)) (𝟭 (Type 0)) (𝟭 (Type 0)) :=
      ⟨Adjunction.id, Adjunction.id,
        CategoryTheory.TwoSquare.mk _ _ _ _ { app := fun _ x ↦ PEmpty.elim x }⟩
    idSq.IsBeckChevalley ∧ ¬ emptySq.IsBeckChevalley := by
  dsimp only
  constructor
  · change IsIso (CategoryTheory.mateEquiv Adjunction.id Adjunction.id
      (CategoryTheory.TwoSquare.mk _ _ _ _ (𝟙 (𝟭 (Type 0) ⋙ 𝟭 (Type 0))))).natTrans
    rw [CategoryTheory.NatTrans.isIso_iff_isIso_app]
    intro X
    change IsIso (𝟙 X)
    infer_instance
  · intro hIso
    let emptySq : MateDoubleSquare ((Functor.const (Type 0)).obj PEmpty) (𝟭 (Type 0))
        (𝟭 (Type 0)) (𝟭 (Type 0)) (𝟭 (Type 0)) (𝟭 (Type 0)) :=
      ⟨Adjunction.id, Adjunction.id,
        CategoryTheory.TwoSquare.mk _ _ _ _ { app := fun _ x ↦ PEmpty.elim x }⟩
    haveI : IsIso emptySq.beckChevalleyMate.natTrans := hIso
    let eIso := CategoryTheory.asIso emptySq.beckChevalleyMate.natTrans
    exact PEmpty.elim ((eIso.inv.app PUnit) PUnit.unit)

/-- Layer 2 `DoctrinalFibration` & non-identity `MateDoubleSquare` separation:
`! : BZ2BotObj ⥤ PUnitCat` is fibered while `PUnitCat ⥤ BZ2BotObj` is not; the non-identity
`Bool ⇄ PUnitCat` squares separate `IsBeckChevalley` and `defectMorphismProperty` even when
`alpha` is an isomorphism. -/
theorem layer2_sep_fibration_and_nonId_mateSquare :
    (Nontrivial BZ2BotObj ∧ Nonempty (DoctrinalFibration BZ2BotObj PUnitCat) ∧
        ¬ bz2BotStarIncl.IsFibered) ∧
      ((nonIdBeckChevalleyPosSq.IsBeckChevalley ∧
          ∀ {X Y : PUnitCat} (f : X ⟶ Y),
            nonIdBeckChevalleyPosSq.defectMorphismProperty f) ∧
        (IsIso nonIdBeckChevalleyNegSq.alpha.natTrans ∧
          ¬ nonIdBeckChevalleyNegSq.IsBeckChevalley ∧
          ¬ nonIdBeckChevalleyNegSq.defectMorphismProperty (𝟙 PUnitCat.star))) :=
  ⟨doctrinalFibration_nontrivial_sep,
    ⟨⟨nonId_mateDoubleSquare_beckChevalley_sep.1.1,
      (MateDoubleSquare.isBeckChevalley_iff_defectMorphismProperty_all
        nonIdBeckChevalleyPosSq).mp nonId_mateDoubleSquare_beckChevalley_sep.1.1⟩,
     nonId_mateDoubleSquare_beckChevalley_sep.2⟩⟩

/-- Layer 2 Mode (i) separation: `intToZMod2TypeMode` is inhabited yet non-contractible, while
`intToZMod2AbMode` is un-inhabited. -/
theorem layer2_sep_sectionObstructionMode :
    (intToZMod2TypeMode.IsSectionInhabited ∧ ¬ intToZMod2TypeMode.IsSectionContractible) ∧
      ¬ intToZMod2AbMode.IsSectionInhabited :=
  ⟨⟨intToZMod2TypeMode_inhabited, not_intToZMod2TypeMode_contractible⟩,
   not_intToZMod2AbMode_inhabited⟩

/-- Layer 2 Mode (ii) separation: `profiniteLassoTowerMode` and `stepProductTowerMode` possess
phantoms, while `idTowerMode` does not. -/
theorem layer2_sep_towerPhantomMode :
    (profiniteLassoTowerMode.HasPhantom ∧ stepProductTowerMode.HasPhantom) ∧
      ¬ idTowerMode.HasPhantom :=
  ⟨⟨profiniteLassoTowerMode_hasPhantom, stepProductTowerMode_hasPhantom⟩,
   not_idTowerMode_hasPhantom⟩

/-- Layer 2 uniform categorical presheaf separation across all 5 probes (`AC`, `IAC`, `ProjSub`,
`Proj₁`, `Localic`). -/
theorem layer2_sep_catPresheaf :
    (CatPresheafAC PUnitCat ∧ ¬ CatPresheafAC TwoGroupCat) ∧
      (CatPresheafIAC TwoGroupCat ∧ ¬ CatPresheafIAC M1Cat) ∧
      (CatPresheafProjSub M1Cat ∧ ¬ CatPresheafProjSub BZ2BotObj) ∧
      (CatPresheafProj1 BZ2BotObj ∧ ¬ CatPresheafProj1 TwoGroupCat) ∧
      (CatPresheafLocalic VPosetOpCat ∧ ¬ CatPresheafLocalic M1Cat) :=
  ⟨⟨catPresheafAC_punitCat, not_catPresheafAC_twoGroupCat⟩,
   ⟨catPresheafIAC_twoGroupCat, not_catPresheafIAC_m1Cat⟩,
   ⟨catPresheafProjSub_m1Cat, not_catPresheafProjSub_bz2Bot⟩,
   ⟨catPresheafProj1_bz2Bot, not_catPresheafProj1_twoGroupCat⟩,
   ⟨catPresheafLocalic_vPosetOpCat, not_catPresheafLocalic_m1Cat⟩⟩

/-- Layer 2 Stage-1 `DeltaLift` separation over `FrobLiftRing2`: `(R₂, φ_aug)` admits lifts while
`(ZMod 2, id)`, `(ZMod 4, id)`, and `(R2IdempRing, id)` have empty `DeltaLift` fibers. -/
theorem layer2_sep_deltaLift :
    Nonempty (DeltaLift r2AugFrobLift) ∧
      IsEmpty (DeltaLift zmod2FrobLift) ∧
      IsEmpty (DeltaLift zmod4FrobLift) ∧
      IsEmpty (DeltaLift r2IdempFrobLift) :=
  ⟨⟨⟨instDeltaRing2R2_zero, r2Delta0Map_frobeniusLift⟩⟩,
    empty_deltaLift_zmod2, empty_deltaLift_zmod4, empty_deltaLift_R2Idemp⟩

/-- Layer 2 `M1SliceLTT.IsLocalic` separation on `Fin 1`: `dneg` is localic while `id` is not. -/
theorem layer2_sep_m1Slice_localic :
    let jLoc : M1SliceLTT (_root_.id : Unit → Unit) :=
      { j := fun _ ω ↦ match ω with | .bot => .bot | _ => .top
        map_top := fun _ ↦ rfl
        monotone := fun _ x y hxy ↦ by
          cases x <;> cases y <;> first | exact hxy | exact trivial
        idem := fun _ ω ↦ by cases ω <;> rfl
        equivariant := fun _ ω ↦ by cases ω <;> rfl }
    let jNon : M1SliceLTT (_root_.id : Unit → Unit) :=
      { j := fun _ ω ↦ ω
        map_top := fun _ ↦ rfl
        monotone := fun _ _ _ h ↦ h
        idem := fun _ _ ↦ rfl
        equivariant := fun _ _ ↦ rfl }
    jLoc.IsLocalic ∧ ¬ jNon.IsLocalic := by
  refine ⟨fun _ _ ↦ rfl, fun h ↦ ?_⟩
  have hm := h () rfl
  cases hm

/-! ### Layer 3: Stock `Mathlib` Projections & Derived Boundary Lemmas -/

def check_doctrinalFibration_proj (B : Type u) [Category.{v} B] :
    (DoctrinalFibration.id B).proj.IsFibered := inferInstance

def check_mooreClosureOperator {D P : Type*} (Φ : DoctrinalPhilosophy D P) :
    ClosureOperator (Set D) := Φ.mooreClosureOperator

def check_bz2Bot_smallCategory : SmallCategory BZ2BotObj := inferInstance
def check_m1Monoid_commMonoid : CommMonoid M1Monoid := inferInstance
def check_r22Ring_commRing : CommRing R22Ring := inferInstance
def check_r2IdempRing_commRing : CommRing R2IdempRing := inferInstance
def check_twoGroup_commGroup : CommGroup TwoGroup := inferInstance
def check_sl2f5_group : Group SL2F5 := inferInstance
def check_centerSL2F5_normal : centerSL2F5.Normal := inferInstance

theorem derived_boffa_twin_bridge :
    Nonempty HomotopyCRM.SetsResiduum.APG :=
  ⟨HomotopyCRM.SetsResiduum.quineAPG⟩

theorem derived_m1_slice_one_fixed_one_nonfixed :
    let rho : Bool → Bool := fun _ ↦ false
    letI : Fintype (M1SliceLTT rho) :=
      Fintype.ofEquiv _ (M1SliceLTT.equivProd (rho := rho) (fun _ ↦ rfl)).symm
    Fintype.card (M1SliceLTT rho) = 6 ∧
      Fintype.card { J : M1SliceLTT rho // J.IsLocalic } = 4 ∧
      Fintype.card { J : M1SliceLTT rho // ¬ J.IsLocalic } = 2 := by
  have h := M1SliceLTT.m1_slice_lt_count (rho := fun _ : Bool ↦ false) (fun _ ↦ rfl)
  have hk : Fintype.card { x : Bool // (fun _ : Bool ↦ false) x = x } = 1 := by decide
  have hm : Fintype.card { x : Bool // (fun _ : Bool ↦ false) x ≠ x } = 1 := by decide
  rw [hk, hm] at h
  exact h

/-! ### Layer 4: Kernel Axiom Gate (`#guard_msgs in #print axioms`, `≥ 30` Checks) -/

section KernelAxiomGate

set_option linter.hashCommand false

/--
info: 'HomotopyCRM.mateDoubleSquare_mate_involutive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.mateDoubleSquare_mate_involutive

/--
info: 'HomotopyCRM.intToZMod2TypeMode_sectionSpace_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.intToZMod2TypeMode_sectionSpace_nontrivial

/--
info: 'HomotopyCRM.not_intToZMod2TypeMode_contractible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.not_intToZMod2TypeMode_contractible

/--
info: 'HomotopyCRM.isEmpty_intToZMod2AbMode_sectionSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.isEmpty_intToZMod2AbMode_sectionSpace

/--
info: 'HomotopyCRM.profiniteLassoTowerMode_hasPhantom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.profiniteLassoTowerMode_hasPhantom

/--
info: 'HomotopyCRM.stepProductTowerMode_hasPhantom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.stepProductTowerMode_hasPhantom

/-- info: 'HomotopyCRM.inquisitor_impossibility_casuistry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.inquisitor_impossibility_casuistry

/-- info: 'HomotopyCRM.monoid_proj1_iff_rightZero' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.monoid_proj1_iff_rightZero

/-- info: 'HomotopyCRM.m1_projSub_and_not_localic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.m1_projSub_and_not_localic

/-- info: 'HomotopyCRM.vPoset_localic_not_proj1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.vPoset_localic_not_proj1

/-- info: 'HomotopyCRM.diamond_proj1_not_projSub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.diamond_proj1_not_projSub

/-- info: 'HomotopyCRM.freydCover_dogma_banishment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.freydCover_dogma_banishment

/-- info: 'HomotopyCRM.not_catPresheafIAC_m1Cat' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.not_catPresheafIAC_m1Cat

/-- info: 'HomotopyCRM.not_catPresheafIAC_vPosetOpCat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.not_catPresheafIAC_vPosetOpCat

/-- info: 'HomotopyCRM.not_catPresheafAC_twoGroupCat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.not_catPresheafAC_twoGroupCat

/--
info: 'HomotopyCRM.twoGroupCat_iac_and_not_ac' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.twoGroupCat_iac_and_not_ac

/--
info: 'HomotopyCRM.choiceConcl_ne_extProj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.choiceConcl_ne_extProj

/--
info: 'HomotopyCRM.pareto_incomparable_projSub_localic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.pareto_incomparable_projSub_localic

/--
info: 'HomotopyCRM.M1SliceLTT.m1_slice_lt_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.M1SliceLTT.m1_slice_lt_count

/-- info: 'HomotopyCRM.delta_mul_p_eq_frob_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.delta_mul_p_eq_frob_sub

/--
info: 'HomotopyCRM.isEmpty_deltaRing2_zmod2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.isEmpty_deltaRing2_zmod2

/--
info: 'HomotopyCRM.empty_deltaLift_zmod2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.empty_deltaLift_zmod2

/-- info: 'HomotopyCRM.isEmpty_deltaRing2_zmod4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.isEmpty_deltaRing2_zmod4

/-- info: 'HomotopyCRM.empty_deltaLift_zmod4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.empty_deltaLift_zmod4

/-- info: 'HomotopyCRM.empty_deltaLift_R2Idemp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.empty_deltaLift_R2Idemp

/-- info: 'HomotopyCRM.r2_lift_card_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.r2_lift_card_eq_two

/-- info: 'HomotopyCRM.r2_lifts_non_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.r2_lifts_non_iso

/-- info: 'HomotopyCRM.r22_lift_card_eq_sixteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.r22_lift_card_eq_sixteen

/-- info: 'HomotopyCRM.r22_iso_orbits_eq_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.r22_iso_orbits_eq_six

/-- info: 'HomotopyCRM.commutator_sl2_f5_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.commutator_sl2_f5_eq_top

/--
info: 'HomotopyCRM.sl2_f5_leray_transgression_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.sl2_f5_leray_transgression_injective

/--
info: 'HomotopyCRM.Checks.layer2_sep_fibration_and_nonId_mateSquare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.Checks.layer2_sep_fibration_and_nonId_mateSquare

end KernelAxiomGate

end Checks

end HomotopyCRM

