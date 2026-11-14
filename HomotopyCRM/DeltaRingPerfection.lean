/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HomotopyCRM Formalization Team
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

/-!
# Slice Endofunctor Algebras, Joyal `δ`-Rings, and Relative Colimit Perfection

This module formalizes `MSG_006` (`TODO-06`) of the `HomotopyCRM` library, uniting:

1. **Goldthorpe §2.3 Slice Endofunctor & Theorem A (`sliceEndofunctor F c`):**
   Given an endofunctor `F : C ⥤ C` and an `F`-coalgebra `c = (V, str : V ⟶ F.obj V)`, the slice
   endofunctor `sliceEndofunctor F c : Under c.V ⥤ Under c.V` sends `(X, η : c.V ⟶ X)` to
   `(F.obj X, c.str ≫ F.map η)`. By **Lambek's Lemma** (`lambek_isIso`), any initial algebra
   `initAlg` of `sliceEndofunctor F c` has an invertible underlying `C`-morphism
   `ν_∞ = initAlg.str.right : F.obj initAlg.a.right ⟶ initAlg.a.right`, endowing its carrier with
   the canonical initial fixed-point `F`-coalgebra structure under `c` (`Theorem A`).

2. **Sequential Colimit Relative Perfection (`Theorem B`):**
   Specializing to `F = 𝟭 C` and a natural endomorphism `φ : 𝟭 C ⟶ 𝟭 C` on `c = ⟨A, φ.app A⟩`,
   any sequential colimit `cocone` of the `ℕ`-chain `A --φ_A--> A --φ_A--> ⋯` carries a canonical
   shift automorphism `s : cocone.pt ≅ cocone.pt` satisfying `φ.app cocone.pt = s.inv` (so `φ`
   becomes invertible on `cocone.pt`), and `(cocone.pt, ι_0)` with structure map `s.hom` is
   initial in the category of `sliceEndofunctor (𝟭 C) ⟨A, φ.app A⟩`-algebras via the cocone legs
   `n ↦ (· ≫ ψ)^[n] f` (`f ≫ endomorphismPow ψ n`).

3. **Mathematical Red-Team Guardrail 2 (Scope of Perfection vs. General Prisms):**
   **CRITICAL GUARDRAIL:** Sequential colimit perfection `A_perf = colim_φ A` (`Theorem B`)
   constructs **ONLY** the **relative perfection** (perfect reflector) where Frobenius `φ` becomes
   an isomorphism. It **NEVER** models general non-perfect prisms `(A, I)` or prismatic cohomology
   `(R)_Δ`: imposing a Lambek initial-algebra isomorphism on a general prism forces Frobenius `φ`
   to be invertible (perfection) and destroys the Nygaard filtration `N^{≥ i} A = φ⁻¹(I^i)`.

4. **Joyal `δ`-Rings & Explicit Dual-Number Counter-Witness `DualInt = ℤ[ε]/(ε²)` at `p = 2`:**
   We formalize general-`p` `DeltaStructure` (with `nygaardLevel`) and polynomial-cofactor `p = 2`
   Joyal `δ`-rings (`DeltaRing2`, `DeltaRing2Cat`), instantiate `ℤ` with its unique `p = 2`
   `δ`-structure (`frobeniusLift = id`, perfect), instantiate `DualInt` (`ℤ[ε]/(ε²)`) with
   `δ(a, b) = ((a - a²) / 2, -ab)` (`frobeniusLift (a, b) = (a, 0)`, neither injective nor
   surjective, hence strictly non-perfect), and prove the **1-step perfection colimit theorem**
   identifying `(ℤ, fst)` as the colimit of `DualInt --φ--> DualInt --φ--> ⋯` in both
   `CommRingCat` and `DeltaRing2Cat`, instantiating `Theorem B` concretely.

5. **Mandatory 4-Layer Definition Check Gate (`namespace Checks`):**
   Verifies Layer 1 (Inhabitation), Layer 2 (Bidirectional Separation), Layer 3 (Projection &
   Derived Sanity), and Layer 4 (`#guard_msgs in #print axioms` Kernel Axiom Gate).
-/

universe v u

namespace HomotopyCRM

open CategoryTheory CategoryTheory.Limits

/-! ## Section 1: Goldthorpe §2.3 Slice Endofunctor and Theorem A -/

section SliceEndofunctor

variable {C : Type u} [Category.{v} C]

/-- Abbreviation for an endofunctor `F`-coalgebra `(V : C, str : V ⟶ F.obj V)`. -/
abbrev Coalgebra (F : C ⥤ C) := Endofunctor.Coalgebra F

/-- Abbreviation for an endofunctor `G`-algebra `(a : D, str : G.obj a ⟶ a)`. -/
abbrev EndofunctorAlgebra {D : Type*} [Category* D] (G : D ⥤ D) := Endofunctor.Algebra G

/-- Carrier accessor alias `A` for `Endofunctor.Algebra` matching blueprint notation. -/
abbrev _root_.CategoryTheory.Endofunctor.Algebra.A
    {D : Type*} [Category* D] {G : D ⥤ D} (alg : Endofunctor.Algebra G) : D :=
  alg.a

/-- **Lambek's Lemma:** the structure morphism `A.str : F.obj A.a ⟶ A.a` of an initial
`F`-algebra `A` is an isomorphism. -/
theorem lambek_isIso {D : Type*} [Category* D] (G : D ⥤ D)
    (alg : Endofunctor.Algebra G) (hInit : IsInitial alg) :
    IsIso alg.str := by
  let nextAlg : Endofunctor.Algebra G :=
    { a := G.obj alg.a
      str := G.map alg.str }
  let invHom : alg ⟶ nextAlg := hInit.to nextAlg
  let strHom : nextAlg ⟶ alg :=
    { f := alg.str
      h := rfl }
  have hComp : invHom ≫ strHom = 𝟙 alg := hInit.hom_ext _ _
  have hRight : invHom.f ≫ alg.str = 𝟙 alg.a :=
    congrArg Endofunctor.Algebra.Hom.f hComp
  have hLeft : alg.str ≫ invHom.f = 𝟙 (G.obj alg.a) := by
    calc
      alg.str ≫ invHom.f = G.map invHom.f ≫ G.map alg.str := invHom.h.symm
      _ = G.map (invHom.f ≫ alg.str) := (G.map_comp invHom.f alg.str).symm
      _ = G.map (𝟙 alg.a) := by rw [hRight]
      _ = 𝟙 (G.obj alg.a) := G.map_id alg.a
  exact ⟨⟨invHom.f, hLeft, hRight⟩⟩

/-- **Goldthorpe §2.3 Slice Endofunctor:** for an endofunctor `F : C ⥤ C` and an `F`-coalgebra
`c = (V, str : V ⟶ F.obj V)`, `sliceEndofunctor F c : Under c.V ⥤ Under c.V` maps an object
`X = (c.V ⟶ X.right)` under `c.V` to `c.V --c.str--> F(c.V) --F(X.hom)--> F(X.right)`. -/
@[simps! obj_right obj_hom map_right]
def sliceEndofunctor (F : C ⥤ C) (c : Coalgebra F) : Under c.V ⥤ Under c.V where
  obj X := Under.mk (c.str ≫ F.map X.hom)
  map f := Under.homMk (F.map f.right) (by
    simp only [Under.mk_right, Under.mk_hom, Category.assoc, ← F.map_comp, Under.w])
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

/-- The category of algebras for the Goldthorpe slice endofunctor `sliceEndofunctor F c`. -/
abbrev SliceAlgebra (F : C ⥤ C) (c : Coalgebra F) :=
  Endofunctor.Algebra (sliceEndofunctor F c)

/-- Predicate asserting that a slice algebra `alg : SliceAlgebra F c` is a fixed point, i.e., its
structure morphism `alg.str` is an isomorphism in `Under c.V`. -/
def IsFixedPointSliceAlg {F : C ⥤ C} {c : Coalgebra F} (alg : SliceAlgebra F c) : Prop :=
  IsIso alg.str

/-- A slice algebra is a fixed point in `Under c.V` if and only if its underlying `C`-morphism
`alg.str.right : F.obj alg.a.right ⟶ alg.a.right` is an isomorphism in `C`. -/
theorem isFixedPointSliceAlg_iff_isIso_right {F : C ⥤ C} {c : Coalgebra F}
    (alg : SliceAlgebra F c) :
    IsFixedPointSliceAlg alg ↔ IsIso alg.str.right := by
  constructor
  · intro h
    haveI : IsIso alg.str := h
    exact (Under.forget c.V).map_isIso alg.str
  · intro h
    haveI : IsIso ((Under.forget c.V).map alg.str) := h
    exact isIso_of_reflects_iso alg.str (Under.forget c.V)

/-- A fixed-point `F`-coalgebra under `c` consists of an `F`-coalgebra `coalg` whose structure
morphism `coalg.str : coalg.V ⟶ F.obj coalg.V` is an isomorphism, together with a coalgebra
morphism `underHom : c ⟶ coalg`. -/
structure FixedPointCoalgebraUnder (F : C ⥤ C) (c : Coalgebra F) where
  /-- The underlying `F`-coalgebra. -/
  coalg : Coalgebra F
  /-- The coalgebra morphism from `c` to `coalg`. -/
  underHom : c ⟶ coalg
  /-- Fixed-point property: `coalg.str` is an isomorphism. -/
  isIso_str : IsIso coalg.str

attribute [instance] FixedPointCoalgebraUnder.isIso_str

namespace FixedPointCoalgebraUnder

variable {F : C ⥤ C} {c : Coalgebra F}

/-- A morphism of fixed-point `F`-coalgebras under `c` is an `F`-coalgebra morphism commuting
with the structural morphisms from `c`. -/
@[ext]
structure Hom (d₁ d₂ : FixedPointCoalgebraUnder F c) where
  /-- Underlying `F`-coalgebra morphism. -/
  hom : d₁.coalg ⟶ d₂.coalg
  /-- Commutativity of the triangle under `c`. -/
  w : d₁.underHom ≫ hom = d₂.underHom := by cat_disch

attribute [reassoc (attr := simp)] Hom.w

instance : Category (FixedPointCoalgebraUnder F c) where
  Hom := Hom
  id d := { hom := 𝟙 d.coalg }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]
lemma ext {d₁ d₂ : FixedPointCoalgebraUnder F c} {f g : d₁ ⟶ d₂}
    (h : f.hom.f = g.hom.f) : f = g := by
  apply Hom.ext
  apply Endofunctor.Coalgebra.ext
  exact h

@[simp]
lemma id_hom (d : FixedPointCoalgebraUnder F c) : (𝟙 d : d ⟶ d).hom = 𝟙 d.coalg := rfl

@[simp]
lemma comp_hom {d₁ d₂ d₃ : FixedPointCoalgebraUnder F c} (f : d₁ ⟶ d₂) (g : d₂ ⟶ d₃) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Faithful forgetful functor from `FixedPointCoalgebraUnder F c` to `Coalgebra F`. -/
@[simps]
def forgetToCoalgebra (F : C ⥤ C) (c : Coalgebra F) :
    FixedPointCoalgebraUnder F c ⥤ Coalgebra F where
  obj d := d.coalg
  map f := f.hom

instance (F : C ⥤ C) (c : Coalgebra F) : (forgetToCoalgebra F c).Faithful where
  map_injective h := Hom.ext h

/-- Every fixed-point `F`-coalgebra `d` under `c` canonically defines a `SliceAlgebra F c` via
`inv d.coalg.str : F.obj d.coalg.V ⟶ d.coalg.V`. -/
noncomputable def toSliceAlgebra (d : FixedPointCoalgebraUnder F c) : SliceAlgebra F c where
  a := Under.mk d.underHom.f
  str := Under.homMk (inv d.coalg.str) (by
    simp only [sliceEndofunctor_obj_right, Under.mk_right, sliceEndofunctor_obj_hom, Under.mk_hom,
      IsIso.comp_inv_eq]
    exact d.underHom.h)

@[simp]
lemma toSliceAlgebra_a_right (d : FixedPointCoalgebraUnder F c) :
    d.toSliceAlgebra.a.right = d.coalg.V := rfl

@[simp]
lemma toSliceAlgebra_a_hom (d : FixedPointCoalgebraUnder F c) :
    d.toSliceAlgebra.a.hom = d.underHom.f := rfl

@[simp]
lemma toSliceAlgebra_str_right (d : FixedPointCoalgebraUnder F c) :
    d.toSliceAlgebra.str.right = inv d.coalg.str := rfl

end FixedPointCoalgebraUnder

/-- **Theorem A (Part 1 — Slice Lambek Isomorphism):** for an initial algebra `initAlg` of
`sliceEndofunctor F c`, the underlying `C`-morphism
`ν_∞ = initAlg.str.right : F.obj initAlg.A.right ⟶ initAlg.A.right` is an isomorphism. -/
theorem sliceLambek_right_isIso (F : C ⥤ C) (c : Coalgebra F)
    (initAlg : SliceAlgebra F c) (hInit : IsInitial initAlg) :
    IsIso initAlg.str.right := by
  have hIso : IsIso initAlg.str := lambek_isIso (sliceEndofunctor F c) initAlg hInit
  exact (Under.forget c.V).map_isIso initAlg.str

/-- **Theorem A (Part 2 — Canonical Fixed-Point Coalgebra Structure):** an initial algebra
`initAlg` of `sliceEndofunctor F c` carries a canonical fixed-point `F`-coalgebra structure under
`c` with coalgebra map `inv initAlg.str.right`. -/
noncomputable def initFixedPointCoalgebraUnder (F : C ⥤ C) (c : Coalgebra F)
    (initAlg : SliceAlgebra F c) (hInit : IsInitial initAlg) :
    FixedPointCoalgebraUnder F c :=
  letI : IsIso initAlg.str.right := sliceLambek_right_isIso F c initAlg hInit
  { coalg :=
      { V := initAlg.A.right
        str := inv initAlg.str.right }
    underHom :=
      { f := initAlg.A.hom
        h := by
          rw [IsIso.eq_comp_inv]
          simpa [sliceEndofunctor] using Under.w initAlg.str }
    isIso_str := inferInstance }

/-- **Theorem A (Part 3 — Universal Hom-Set Equivalence):** morphisms out of an initial slice
algebra `initAlg` into `d.toSliceAlgebra` correspond bijectively (`Equiv`) to morphisms of
fixed-point `F`-coalgebras under `c` from `initFixedPointCoalgebraUnder F c initAlg hInit` to `d`.
-/
noncomputable def theoremA_homEquiv (F : C ⥤ C) (c : Coalgebra F)
    (initAlg : SliceAlgebra F c) (hInit : IsInitial initAlg)
    (d : FixedPointCoalgebraUnder F c) :
    (initAlg ⟶ d.toSliceAlgebra) ≃ (initFixedPointCoalgebraUnder F c initAlg hInit ⟶ d) where
  toFun m :=
    letI : IsIso initAlg.str.right := sliceLambek_right_isIso F c initAlg hInit
    { hom :=
        { f := m.f.right
          h := by
            have hm : F.map m.f.right ≫ inv d.coalg.str = initAlg.str.right ≫ m.f.right :=
              congrArg (Under.forget c.V).map m.h
            dsimp only [initFixedPointCoalgebraUnder]
            rw [IsIso.inv_comp_eq, ← Category.assoc, ← IsIso.comp_inv_eq]
            exact hm }
      w := by
        apply Endofunctor.Coalgebra.ext
        simp [initFixedPointCoalgebraUnder] }
  invFun k :=
    letI : IsIso initAlg.str.right := sliceLambek_right_isIso F c initAlg hInit
    { f := Under.homMk k.hom.f (by
        simpa [initFixedPointCoalgebraUnder] using
          congrArg Endofunctor.Coalgebra.Hom.f k.w)
      h := by
        apply Under.UnderMorphism.ext
        change F.map k.hom.f ≫ inv d.coalg.str = initAlg.str.right ≫ k.hom.f
        rw [IsIso.comp_inv_eq, Category.assoc]
        have hk : inv initAlg.str.right ≫ F.map k.hom.f = k.hom.f ≫ d.coalg.str := k.hom.h
        rw [IsIso.inv_comp_eq] at hk
        exact hk }
  left_inv m := by
    apply Endofunctor.Algebra.ext
    apply Under.UnderMorphism.ext
    rfl
  right_inv k := FixedPointCoalgebraUnder.ext rfl

/-- **Theorem A (Corollary — Initiality in Fixed-Point Coalgebras Under `c`):** the canonical
fixed-point coalgebra `initFixedPointCoalgebraUnder F c initAlg hInit` is initial in
`FixedPointCoalgebraUnder F c`. -/
noncomputable def theoremA_isInitial_fixedPointCoalgebraUnder (F : C ⥤ C) (c : Coalgebra F)
    (initAlg : SliceAlgebra F c) (hInit : IsInitial initAlg) :
    IsInitial (initFixedPointCoalgebraUnder F c initAlg hInit) :=
  IsInitial.ofUniqueHom
    (fun d ↦ theoremA_homEquiv F c initAlg hInit d (hInit.to d.toSliceAlgebra))
    (fun d k ↦ by
      apply (theoremA_homEquiv F c initAlg hInit d).symm.injective
      rw [Equiv.symm_apply_apply]
      exact hInit.hom_ext _ _)

end SliceEndofunctor

/-! ## Section 2: Theorem B — Sequential Colimit Relative Perfection

**Mathematical Red-Team Guardrail 2:** The sequential colimit `colim_φ A` below constructs
**strictly the relative perfection** `A_perf = colim_φ A` on which the natural endomorphism `φ`
becomes an isomorphism. It **never** models general non-perfect prisms `(A, I)` or `(R)_Δ`, where
forcing a Lambek initial-algebra isomorphism forces `φ` to be invertible and collapses the
Nygaard filtration. -/

section SequentialPerfection

variable {C : Type u} [Category.{v} C]

/-- The `ℕ`-indexed sequential chain `A --φA--> A --φA--> A --φA--> ⋯` generated by a single
endomorphism `φA : A ⟶ A`. -/
def endomorphismChain {A : C} (φA : A ⟶ A) : ℕ ⥤ C :=
  Functor.ofSequence (fun _ : ℕ ↦ φA)

@[simp]
lemma endomorphismChain_obj {A : C} (φA : A ⟶ A) (n : ℕ) :
    (endomorphismChain φA).obj n = A := rfl

@[simp]
lemma endomorphismChain_map_succ {A : C} (φA : A ⟶ A) (n : ℕ) :
    (endomorphismChain φA).map (homOfLE (Nat.le_add_right n 1)) = φA :=
  Functor.ofSequence_map_homOfLE_succ (fun _ : ℕ ↦ φA) n

/-- Constructor for a cocone on `endomorphismChain φA` from legs `n ↦ legs n : A ⟶ P` satisfying
`φA ≫ legs (n + 1) = legs n` for every `n : ℕ`. -/
@[simps pt]
def mkEndomorphismChainCocone {A : C} (φA : A ⟶ A) (P : C)
    (legs : ℕ → (A ⟶ P)) (hlegs : ∀ n : ℕ, φA ≫ legs (n + 1) = legs n) :
    Cocone (endomorphismChain φA) where
  pt := P
  ι := NatTrans.ofSequence legs (fun n ↦ by
    simp [hlegs n])

@[simp]
lemma mkEndomorphismChainCocone_ι_app {A : C} (φA : A ⟶ A) (P : C)
    (legs : ℕ → (A ⟶ P)) (hlegs : ∀ n : ℕ, φA ≫ legs (n + 1) = legs n) (n : ℕ) :
    (mkEndomorphismChainCocone φA P legs hlegs).ι.app n = legs n := rfl

/-- Step compatibility `φA ≫ cocone.ι.app (n + 1) = cocone.ι.app n` for any cocone on
`endomorphismChain φA`. -/
lemma endomorphismChain_cocone_w {A : C} {φA : A ⟶ A}
    (cocone : Cocone (endomorphismChain φA)) (n : ℕ) :
    φA ≫ cocone.ι.app (n + 1) = cocone.ι.app n := by
  simpa using cocone.w (homOfLE (Nat.le_add_right n 1))

/-- Iterated endomorphism `ψ^n : B ⟶ B` in a category `C`. -/
def endomorphismPow {B : C} (ψ : B ⟶ B) : ℕ → (B ⟶ B)
  | 0 => 𝟙 B
  | n + 1 => ψ ≫ endomorphismPow ψ n

@[simp]
lemma endomorphismPow_zero {B : C} (ψ : B ⟶ B) :
    endomorphismPow ψ 0 = 𝟙 B := rfl

@[simp]
lemma endomorphismPow_succ_left {B : C} (ψ : B ⟶ B) (n : ℕ) :
    endomorphismPow ψ (n + 1) = ψ ≫ endomorphismPow ψ n := rfl

lemma endomorphismPow_comm {B : C} (ψ : B ⟶ B) (n : ℕ) :
    endomorphismPow ψ n ≫ ψ = ψ ≫ endomorphismPow ψ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Category.assoc, ih]

lemma endomorphismPow_succ_right {B : C} (ψ : B ⟶ B) (n : ℕ) :
    endomorphismPow ψ (n + 1) = endomorphismPow ψ n ≫ ψ :=
  (endomorphismPow_comm ψ n).symm

/-- Agreement of `f ≫ endomorphismPow ψ n` with standard `Function.iterate` `(· ≫ ψ)^[n] f`. -/
lemma comp_endomorphismPow_eq_iterate {A B : C} (f : A ⟶ B) (ψ : B ⟶ B) (n : ℕ) :
    f ≫ endomorphismPow ψ n = (fun h : A ⟶ B ↦ h ≫ ψ)^[n] f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, Category.assoc, ← endomorphismPow_succ_right]

/-- Forward-shifted cocone on `endomorphismChain φA` with `n`-th leg `cocone.ι.app (n + 1)`. -/
def shiftUpCocone {A : C} {φA : A ⟶ A} (cocone : Cocone (endomorphismChain φA)) :
    Cocone (endomorphismChain φA) :=
  mkEndomorphismChainCocone φA cocone.pt (fun n ↦ cocone.ι.app (n + 1))
    (fun n ↦ endomorphismChain_cocone_w cocone (n + 1))

/-- Backward-shifted cocone on `endomorphismChain φA` with `n`-th leg `φA ≫ cocone.ι.app n`. -/
def shiftDownCocone {A : C} {φA : A ⟶ A} (cocone : Cocone (endomorphismChain φA)) :
    Cocone (endomorphismChain φA) :=
  mkEndomorphismChainCocone φA cocone.pt (fun n ↦ φA ≫ cocone.ι.app n)
    (fun n ↦ by rw [← Category.assoc, Category.assoc, endomorphismChain_cocone_w])

/-- **Theorem B (Part 1 — Sequential Colimit Shift Isomorphism):** given a colimit `cocone` of
`endomorphismChain φA`, shifting cocone legs by `+1` (`s.hom`) and precomposing with `φA`
(`s.inv`) define mutually inverse automorphisms `s : cocone.pt ≅ cocone.pt`.

**Guardrail 2 Note:** This isomorphism exists on the colimit perfection `A_perf = colim_φ A`; it
must never be assumed on a general non-perfect prism `(A, I)`. -/
def endomorphismColimitShiftIso {A : C} {φA : A ⟶ A}
    {cocone : Cocone (endomorphismChain φA)} (hColim : IsColimit cocone) :
    cocone.pt ≅ cocone.pt where
  hom := hColim.desc (shiftUpCocone cocone)
  inv := hColim.desc (shiftDownCocone cocone)
  hom_inv_id := by
    refine (hColim.uniq cocone _ (fun n ↦ ?_)).trans (hColim.desc_self)
    calc
      cocone.ι.app n ≫ hColim.desc (shiftUpCocone cocone) ≫
          hColim.desc (shiftDownCocone cocone)
        = (cocone.ι.app n ≫ hColim.desc (shiftUpCocone cocone)) ≫
            hColim.desc (shiftDownCocone cocone) := (Category.assoc _ _ _).symm
      _ = cocone.ι.app (n + 1) ≫ hColim.desc (shiftDownCocone cocone) := by
          rw [hColim.fac (shiftUpCocone cocone) n]
          rfl
      _ = φA ≫ cocone.ι.app (n + 1) := hColim.fac (shiftDownCocone cocone) (n + 1)
      _ = cocone.ι.app n := endomorphismChain_cocone_w cocone n
  inv_hom_id := by
    refine (hColim.uniq cocone _ (fun n ↦ ?_)).trans (hColim.desc_self)
    calc
      cocone.ι.app n ≫ hColim.desc (shiftDownCocone cocone) ≫
          hColim.desc (shiftUpCocone cocone)
        = (cocone.ι.app n ≫ hColim.desc (shiftDownCocone cocone)) ≫
            hColim.desc (shiftUpCocone cocone) := (Category.assoc _ _ _).symm
      _ = (φA ≫ cocone.ι.app n) ≫ hColim.desc (shiftUpCocone cocone) := by
          rw [hColim.fac (shiftDownCocone cocone) n]
          rfl
      _ = φA ≫ cocone.ι.app (n + 1) := by
          rw [Category.assoc, hColim.fac (shiftUpCocone cocone) n]
          rfl
      _ = cocone.ι.app n := endomorphismChain_cocone_w cocone n

@[simp, reassoc]
lemma ι_comp_shiftIso_hom {A : C} {φA : A ⟶ A}
    {cocone : Cocone (endomorphismChain φA)} (hColim : IsColimit cocone) (n : ℕ) :
    cocone.ι.app n ≫ (endomorphismColimitShiftIso hColim).hom = cocone.ι.app (n + 1) :=
  hColim.fac (shiftUpCocone cocone) n

@[simp, reassoc]
lemma ι_comp_shiftIso_inv {A : C} {φA : A ⟶ A}
    {cocone : Cocone (endomorphismChain φA)} (hColim : IsColimit cocone) (n : ℕ) :
    cocone.ι.app n ≫ (endomorphismColimitShiftIso hColim).inv = φA ≫ cocone.ι.app n :=
  hColim.fac (shiftDownCocone cocone) n

/-- **Theorem B (Part 2 — Natural Endomorphism Identification `φ_{A_perf} = s.inv`):** for a
natural endomorphism `φ : 𝟭 C ⟶ 𝟭 C` and a colimit `cocone` of `endomorphismChain (φ.app A)`,
the component `φ.app cocone.pt` equals `(endomorphismColimitShiftIso hColim).inv`.

**Guardrail 2 Note:** This proves that passing to the sequential colimit `A_perf = colim_φ A`
forces `φ` to become invertible; general prisms `(A, I)` or `(R)_Δ` are NOT colimit perfections,
and forcing `φ` to be an isomorphism on them destroys the Nygaard filtration. -/
theorem theoremB_natEndo_app_eq_shift_inv (φ : 𝟭 C ⟶ 𝟭 C) (A : C)
    {cocone : Cocone (endomorphismChain (φ.app A))} (hColim : IsColimit cocone) :
    φ.app cocone.pt = (endomorphismColimitShiftIso hColim).inv := by
  refine hColim.uniq (shiftDownCocone cocone) (φ.app cocone.pt) (fun n ↦ ?_)
  simpa [shiftDownCocone] using φ.naturality (cocone.ι.app n)

/-- Corollary of Theorem B (Part 2): `φ.app cocone.pt` is an isomorphism on the sequential
colimit `cocone.pt`. -/
theorem theoremB_isIso_natEndo_app (φ : 𝟭 C ⟶ 𝟭 C) (A : C)
    {cocone : Cocone (endomorphismChain (φ.app A))} (hColim : IsColimit cocone) :
    IsIso (φ.app cocone.pt) := by
  rw [theoremB_natEndo_app_eq_shift_inv φ A hColim]
  infer_instance

/-- The canonical slice algebra on `(cocone.pt, cocone.ι.app 0)` for
`sliceEndofunctor (𝟭 C) ⟨A, φ.app A⟩` with structure map `(endomorphismColimitShiftIso hColim).hom`.
-/
def perfectionSliceAlg (φ : 𝟭 C ⟶ 𝟭 C) (A : C)
    {cocone : Cocone (endomorphismChain (φ.app A))} (hColim : IsColimit cocone) :
    SliceAlgebra (𝟭 C) ⟨A, φ.app A⟩ where
  a := Under.mk (cocone.ι.app 0)
  str := Under.homMk (endomorphismColimitShiftIso hColim).hom (by
    simp only [sliceEndofunctor_obj_right, Functor.id_obj, Under.mk_right,
      sliceEndofunctor_obj_hom, Functor.id_map, Under.mk_hom, Category.assoc,
      ι_comp_shiftIso_hom]
    exact endomorphismChain_cocone_w cocone 0)

/-- Cocone on `endomorphismChain (φ.app A)` induced by any slice algebra `alg` over
`⟨A, φ.app A⟩`, with `n`-th leg `(· ≫ ψ)^[n] f = f ≫ endomorphismPow ψ n`. -/
def coconeOfSliceAlg (φ : 𝟭 C ⟶ 𝟭 C) (A : C)
    (alg : SliceAlgebra (𝟭 C) ⟨A, φ.app A⟩) :
    Cocone (endomorphismChain (φ.app A)) :=
  mkEndomorphismChainCocone (φ.app A) alg.a.right
    (fun n ↦ (fun h : A ⟶ alg.a.right ↦ h ≫ alg.str.right)^[n] alg.a.hom)
    (fun n ↦ by
      simp only [← comp_endomorphismPow_eq_iterate, endomorphismPow_succ_left]
      have hw : (φ.app A ≫ alg.a.hom) ≫ alg.str.right = alg.a.hom := by
        simpa [sliceEndofunctor] using Under.w alg.str
      rw [← Category.assoc, ← Category.assoc, hw])

/-- **Theorem B (Part 3 — Initiality of the Perfection Slice Algebra):** for `F = 𝟭 C` and
`φ : 𝟭 C ⟶ 𝟭 C`, the sequential colimit slice algebra `perfectionSliceAlg φ A hColim` is initial
in `SliceAlgebra (𝟭 C) ⟨A, φ.app A⟩`, with the unique morphism to any `(B, f, ψ)` induced by the
cocone legs `n ↦ (· ≫ ψ)^[n] f`.

**Guardrail 2 Compliance:** This universal property characterizes the **relative perfection**
`A_perf = colim_φ A` (left-adjoint perfect reflector), and must **never** be misapplied to claim
initial-algebra structure on general non-perfect prisms `(A, I)` or `(R)_Δ`. -/
def theoremB_perfectionSliceAlg_isInitial (φ : 𝟭 C ⟶ 𝟭 C) (A : C)
    {cocone : Cocone (endomorphismChain (φ.app A))} (hColim : IsColimit cocone) :
    IsInitial (perfectionSliceAlg φ A hColim) :=
  IsInitial.ofUniqueHom
    (fun alg ↦
      { f := Under.homMk (hColim.desc (coconeOfSliceAlg φ A alg)) (by
          simp [perfectionSliceAlg, coconeOfSliceAlg])
        h := by
          apply Under.UnderMorphism.ext
          change hColim.desc (coconeOfSliceAlg φ A alg) ≫ alg.str.right =
            (endomorphismColimitShiftIso hColim).hom ≫ hColim.desc (coconeOfSliceAlg φ A alg)
          let cRight : Cocone (endomorphismChain (φ.app A)) :=
            mkEndomorphismChainCocone (φ.app A) alg.a.right
              (fun n ↦ alg.a.hom ≫ endomorphismPow alg.str.right (n + 1))
              (fun n ↦ by
                have hw : (φ.app A ≫ alg.a.hom) ≫ alg.str.right = alg.a.hom := by
                  simpa [sliceEndofunctor] using Under.w alg.str
                simp only [endomorphismPow_succ_left]
                rw [← Category.assoc, ← Category.assoc, hw])
          have h1 : hColim.desc (coconeOfSliceAlg φ A alg) ≫ alg.str.right =
              hColim.desc cRight := by
            refine hColim.uniq cRight _ (fun n ↦ ?_)
            calc
              cocone.ι.app n ≫ hColim.desc (coconeOfSliceAlg φ A alg) ≫ alg.str.right
                = (cocone.ι.app n ≫ hColim.desc (coconeOfSliceAlg φ A alg)) ≫
                    alg.str.right := (Category.assoc _ _ _).symm
              _ = ((fun h ↦ h ≫ alg.str.right)^[n] alg.a.hom) ≫ alg.str.right := by
                  rw [hColim.fac (coconeOfSliceAlg φ A alg) n]
                  rfl
              _ = alg.a.hom ≫ endomorphismPow alg.str.right (n + 1) := by
                  rw [← comp_endomorphismPow_eq_iterate, Category.assoc,
                    ← endomorphismPow_succ_right]
          have h2 : (endomorphismColimitShiftIso hColim).hom ≫
              hColim.desc (coconeOfSliceAlg φ A alg) = hColim.desc cRight := by
            refine hColim.uniq cRight _ (fun n ↦ ?_)
            calc
              cocone.ι.app n ≫ (endomorphismColimitShiftIso hColim).hom ≫
                  hColim.desc (coconeOfSliceAlg φ A alg)
                = cocone.ι.app (n + 1) ≫ hColim.desc (coconeOfSliceAlg φ A alg) := by
                    rw [← Category.assoc, ι_comp_shiftIso_hom]
              _ = (fun h ↦ h ≫ alg.str.right)^[n + 1] alg.a.hom :=
                    hColim.fac (coconeOfSliceAlg φ A alg) (n + 1)
              _ = alg.a.hom ≫ endomorphismPow alg.str.right (n + 1) := by
                    rw [← comp_endomorphismPow_eq_iterate]
          exact h1.trans h2.symm })
    (fun alg m ↦ by
      apply Endofunctor.Algebra.ext
      apply Under.UnderMorphism.ext
      change m.f.right = hColim.desc (coconeOfSliceAlg φ A alg)
      refine hColim.uniq (coconeOfSliceAlg φ A alg) m.f.right (fun n ↦ ?_)
      simp only [coconeOfSliceAlg, mkEndomorphismChainCocone_ι_app,
        ← comp_endomorphismPow_eq_iterate]
      induction n with
      | zero =>
        simpa [perfectionSliceAlg] using Under.w m.f
      | succ n ih =>
        have hm : m.f.right ≫ alg.str.right =
            (endomorphismColimitShiftIso hColim).hom ≫ m.f.right :=
          congrArg (Under.forget A).map m.h
        calc
          cocone.ι.app (n + 1) ≫ m.f.right
            = (cocone.ι.app n ≫ (endomorphismColimitShiftIso hColim).hom) ≫ m.f.right := by
                rw [ι_comp_shiftIso_hom]
          _ = cocone.ι.app n ≫ ((endomorphismColimitShiftIso hColim).hom ≫ m.f.right) :=
                Category.assoc _ _ _
          _ = cocone.ι.app n ≫ (m.f.right ≫ alg.str.right) := by rw [← hm]
          _ = (cocone.ι.app n ≫ m.f.right) ≫ alg.str.right := (Category.assoc _ _ _).symm
          _ = (alg.a.hom ≫ endomorphismPow alg.str.right n) ≫ alg.str.right := by rw [ih]
          _ = alg.a.hom ≫ endomorphismPow alg.str.right (n + 1) := by
                rw [Category.assoc, ← endomorphismPow_succ_right])

end SequentialPerfection

/-! ## Section 3: Joyal `δ`-Rings (`DeltaStructure` and `DeltaRing2`) & Nygaard Filtration -/

section DeltaRings

/-- General-prime `p`-typical Joyal `δ`-structure on a commutative ring `A`
(following Joyal 1985 and Bhatt–Scholze `arXiv:1905.08229`, §2), packaging the set map
`delta : A → A` together with its associated Frobenius lift `phi : A →+* A` satisfying
`phi x = x ^ p + p * delta x`. -/
structure DeltaStructure (p : ℕ) [Fact (Nat.Prime p)] (A : Type u) [CommRing A] where
  /-- The Joyal `p`-derivation `δ : A → A` (a map of underlying sets, not a ring hom). -/
  delta : A → A
  /-- The associated Frobenius lift `φ(x) = x^p + p * δ(x)` packaged as a ring endomorphism. -/
  phi : A →+* A
  /-- Defining relation `φ(x) = x^p + p * δ(x)`. -/
  phi_spec : ∀ x : A, phi x = x ^ p + (p : A) * delta x
  /-- `δ(0) = 0`. -/
  delta_zero : delta 0 = 0
  /-- `δ(1) = 0`. -/
  delta_one : delta 1 = 0
  /-- Leibniz-like product rule for `δ`. -/
  delta_mul : ∀ x y : A,
    delta (x * y) = x ^ p * delta y + y ^ p * delta x + (p : A) * delta x * delta y

/-- Morphism of general-`p` `DeltaStructure`s commuting with `δ`. -/
structure DeltaStructureHom {p : ℕ} [Fact (Nat.Prime p)]
    {A B : Type u} [CommRing A] [CommRing B]
    (dA : DeltaStructure p A) (dB : DeltaStructure p B) extends A →+* B where
  /-- Compatibility with `δ`. -/
  map_delta : ∀ x : A, toRingHom (dA.delta x) = dB.delta (toRingHom x)

/-- The `i`-th Nygaard filtration level `N^{≥ i} A = φ⁻¹(I^i)` associated to an ideal `I` of a
`δ`-ring `(A, dA)`. Inverting `I` or forcing `φ` to be an isomorphism collapses this filtration
(Guardrail 2). -/
def nygaardLevel {p : ℕ} [Fact (Nat.Prime p)]
    {A : Type u} [CommRing A] (dA : DeltaStructure p A) (I : Ideal A) (i : ℕ) :
    Ideal A :=
  (I ^ i).comap dA.phi

/-- Antitonicity of the Nygaard filtration: `i ≤ j ⟹ N^{≥ j} A ≤ N^{≥ i} A`. -/
theorem nygaard_antitone {p : ℕ} [Fact (Nat.Prime p)]
    {A : Type u} [CommRing A] (dA : DeltaStructure p A) (I : Ideal A)
    {i j : ℕ} (hij : i ≤ j) :
    nygaardLevel dA I j ≤ nygaardLevel dA I i := by
  intro x hx
  simp only [nygaardLevel, Ideal.mem_comap] at hx ⊢
  exact Ideal.pow_le_pow_right hij hx

/-- Polynomial-cofactor Joyal `δ`-ring class at `p = 2`: since `((x + y)² - x² - y²) / 2 = x * y`
over `ℤ[x, y]`, all four `δ`-identities are polynomial over **every** commutative ring `R`,
making `frobeniusLift x = x² + 2 * δ(x)` a ring endomorphism unconditionally. -/
class DeltaRing2 (R : Type u) [CommRing R] where
  /-- The `2`-typical Joyal `δ`-operation `δ : R → R`. -/
  delta : R → R
  /-- `δ(0) = 0`. -/
  delta_zero : delta 0 = 0
  /-- `δ(1) = 0`. -/
  delta_one : delta 1 = 0
  /-- Additive `δ`-identity at `p = 2`: `δ(x + y) = δ(x) + δ(y) - xy`. -/
  delta_add : ∀ x y : R, delta (x + y) = delta x + delta y - x * y
  /-- Multiplicative `δ`-identity at `p = 2`: `δ(xy) = x² δ(y) + y² δ(x) + 2 δ(x) δ(y)`. -/
  delta_mul : ∀ x y : R,
    delta (x * y) = x ^ 2 * delta y + y ^ 2 * delta x + 2 * delta x * delta y

export DeltaRing2 (delta delta_zero delta_one delta_add delta_mul)

/-- The canonical `p = 2` Frobenius lift `φ(x) = x² + 2 δ(x)` of a `DeltaRing2`. -/
def frobeniusLift {R : Type u} [CommRing R] [DeltaRing2 R] (x : R) : R :=
  x ^ 2 + 2 * delta x

/-- Unconditionally over every `CommRing R` with `[DeltaRing2 R]`, `frobeniusLift` is a ring
endomorphism `R →+* R`. -/
def frobeniusLiftRingHom (R : Type u) [CommRing R] [DeltaRing2 R] : R →+* R where
  toFun := frobeniusLift
  map_one' := by simp [frobeniusLift, delta_one]
  map_mul' x y := by
    simp only [frobeniusLift, delta_mul]
    ring
  map_zero' := by simp [frobeniusLift, delta_zero]
  map_add' x y := by
    simp only [frobeniusLift, delta_add]
    ring

@[simp]
lemma coe_frobeniusLiftRingHom (R : Type u) [CommRing R] [DeltaRing2 R] :
    (frobeniusLiftRingHom R : R → R) = frobeniusLift := rfl

@[simp]
lemma frobeniusLiftRingHom_apply {R : Type u} [CommRing R] [DeltaRing2 R] (x : R) :
    frobeniusLiftRingHom R x = frobeniusLift x := rfl

/-- Unconditionally over every `CommRing R` with `[DeltaRing2 R]`, `δ` commutes with
`frobeniusLift` (`δ(φ(x)) = φ(δ(x))`), so `frobeniusLift` is itself a `δ`-ring endomorphism. -/
theorem delta_comm_frobeniusLift {R : Type u} [CommRing R] [DeltaRing2 R] (x : R) :
    delta (frobeniusLift x) = frobeniusLift (delta x) := by
  have h2 : (2 : R) * delta x = delta x + delta x := two_mul (delta x)
  calc
    delta (frobeniusLift x)
      = delta (x * x + (delta x + delta x)) := by
          rw [frobeniusLift, sq, h2]
    _ = delta (x * x) + delta (delta x + delta x) - (x * x) * (delta x + delta x) :=
          delta_add (x * x) (delta x + delta x)
    _ = (x ^ 2 * delta x + x ^ 2 * delta x + 2 * delta x * delta x) +
          (delta (delta x) + delta (delta x) - delta x * delta x) -
          (x * x) * (delta x + delta x) := by
          rw [delta_mul, delta_add]
    _ = (delta x) ^ 2 + 2 * delta (delta x) := by ring
    _ = frobeniusLift (delta x) := rfl

/-- Canonical projection from `[DeltaRing2 R]` to the general-prime `DeltaStructure 2 R`. -/
def DeltaRing2.toDeltaStructure (R : Type u) [CommRing R] [DeltaRing2 R] :
    DeltaStructure 2 R where
  delta := delta
  phi := frobeniusLiftRingHom R
  phi_spec x := by simp [frobeniusLift]
  delta_zero := delta_zero
  delta_one := delta_one
  delta_mul x y := by simpa using delta_mul x y

/-- A `p = 2` `δ`-ring `R` is **perfect** when its Frobenius lift `frobeniusLift : R → R` is
bijective. -/
def IsPerfectDeltaRing (R : Type u) [CommRing R] [DeltaRing2 R] : Prop :=
  Function.Bijective (frobeniusLift (R := R))

/-- Morphisms of `p = 2` `δ`-rings are ring homomorphisms commuting with `delta`. -/
structure DeltaRing2Hom (R : Type*) (S : Type*) [CommRing R] [CommRing S]
    [DeltaRing2 R] [DeltaRing2 S] extends R →+* S where
  /-- Compatibility with `delta`. -/
  map_delta' : ∀ x : R, toRingHom (delta x) = delta (toRingHom x)

namespace DeltaRing2Hom

@[ext]
lemma ext {R S : Type*} [CommRing R] [CommRing S] [DeltaRing2 R] [DeltaRing2 S]
    {f g : DeltaRing2Hom R S} (h : ∀ x : R, f.toRingHom x = g.toRingHom x) : f = g := by
  cases f
  cases g
  congr
  exact RingHom.ext h

/-- Identity `δ`-ring homomorphism. -/
def id (R : Type*) [CommRing R] [DeltaRing2 R] : DeltaRing2Hom R R where
  toRingHom := RingHom.id R
  map_delta' _ := rfl

/-- Composition of `δ`-ring homomorphisms. -/
def comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [DeltaRing2 R] [DeltaRing2 S] [DeltaRing2 T]
    (g : DeltaRing2Hom S T) (f : DeltaRing2Hom R S) : DeltaRing2Hom R T where
  toRingHom := g.toRingHom.comp f.toRingHom
  map_delta' x := by
    simp only [RingHom.comp_apply]
    rw [f.map_delta', g.map_delta']

/-- Every `DeltaRing2Hom` automatically commutes with `frobeniusLift`. -/
lemma map_frobeniusLift {R S : Type*} [CommRing R] [CommRing S]
    [DeltaRing2 R] [DeltaRing2 S] (f : DeltaRing2Hom R S) (x : R) :
    f.toRingHom (frobeniusLift x) = frobeniusLift (f.toRingHom x) := by
  simp only [frobeniusLift, map_add, map_pow, map_mul, map_ofNat, f.map_delta']

/-- The Frobenius lift packaged as a `DeltaRing2Hom R R`. -/
def frobeniusEndo (R : Type*) [CommRing R] [DeltaRing2 R] : DeltaRing2Hom R R where
  toRingHom := frobeniusLiftRingHom R
  map_delta' x := (delta_comm_frobeniusLift x).symm

end DeltaRing2Hom

/-- Bundled category `DeltaRing2Cat` of `p = 2` Joyal `δ`-rings, on which Frobenius is a genuine
natural endomorphism `frobeniusNatEndo : 𝟭 DeltaRing2Cat ⟶ 𝟭 DeltaRing2Cat`. -/
structure DeltaRing2Cat : Type (u + 1) where
  /-- Construct a bundled `p = 2` `δ`-ring from a carrier with typeclasses. -/
  of ::
  /-- Underlying carrier type. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [deltaRing2 : DeltaRing2 carrier]

attribute [instance] DeltaRing2Cat.commRing DeltaRing2Cat.deltaRing2

namespace DeltaRing2Cat

instance : Category DeltaRing2Cat.{u} where
  Hom R S := DeltaRing2Hom R.carrier S.carrier
  id R := DeltaRing2Hom.id R.carrier
  comp f g := DeltaRing2Hom.comp g f

@[ext]
lemma hom_ext {R S : DeltaRing2Cat.{u}} {f g : R ⟶ S}
    (h : ∀ x : R.carrier, f.toRingHom x = g.toRingHom x) : f = g :=
  DeltaRing2Hom.ext h

@[simp]
lemma id_toRingHom (R : DeltaRing2Cat.{u}) :
    (𝟙 R : R ⟶ R).toRingHom = RingHom.id R.carrier := rfl

@[simp]
lemma comp_toRingHom {R S T : DeltaRing2Cat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).toRingHom = g.toRingHom.comp f.toRingHom := rfl

/-- Faithful forgetful functor from `DeltaRing2Cat` to stock `CommRingCat`. -/
@[simps]
def forgetToCommRingCat : DeltaRing2Cat.{u} ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of R.carrier
  map f := CommRingCat.ofHom f.toRingHom

instance : forgetToCommRingCat.{u}.Faithful where
  map_injective h := hom_ext (fun x ↦ congrArg (fun k ↦ k.hom x) h)

/-- The Frobenius lift `φ` as a natural endomorphism `𝟭 DeltaRing2Cat ⟶ 𝟭 DeltaRing2Cat`. -/
@[simps]
def frobeniusNatEndo : 𝟭 DeltaRing2Cat.{u} ⟶ 𝟭 DeltaRing2Cat.{u} where
  app R := DeltaRing2Hom.frobeniusEndo R.carrier
  naturality _ _ f := by
    ext x
    exact (f.map_frobeniusLift x).symm

end DeltaRing2Cat

end DeltaRings

/-! ## Section 4: Unique `p = 2` `δ`-Structure on `ℤ` -/

section IntDeltaRing

/-- The canonical `p = 2` `δ`-map on `ℤ`: `δ(a) = (a - a²) / 2`. -/
def intDelta (a : ℤ) : ℤ := (a - a ^ 2) / 2

/-- Parity cancellation identity `2 * ((a - a²) / 2) = a - a²` for all `a : ℤ`. -/
theorem two_mul_intDelta (a : ℤ) : 2 * intDelta a = a - a ^ 2 := by
  unfold intDelta
  set k : ℤ := a / 2
  have hpar : a = 2 * k ∨ a = 2 * k + 1 := by omega
  rcases hpar with h | h
  · have hpoly : a - a ^ 2 = 2 * (k - 2 * k ^ 2) := by
      rw [h]
      ring
    rw [hpoly, Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]
  · have hpoly : a - a ^ 2 = 2 * (-2 * k ^ 2 - k) := by
      rw [h]
      ring
    rw [hpoly, Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]

instance instDeltaRing2Int : DeltaRing2 ℤ where
  delta := intDelta
  delta_zero := by decide
  delta_one := by decide
  delta_add x y := by
    have hlin : 2 * intDelta (x + y) = 2 * (intDelta x + intDelta y - x * y) := by
      calc
        2 * intDelta (x + y) = (x + y) - (x + y) ^ 2 := two_mul_intDelta (x + y)
        _ = (x - x ^ 2) + (y - y ^ 2) - 2 * x * y := by ring
        _ = 2 * intDelta x + 2 * intDelta y - 2 * x * y := by
              rw [← two_mul_intDelta x, ← two_mul_intDelta y]
        _ = 2 * (intDelta x + intDelta y - x * y) := by ring
    omega
  delta_mul x y := by
    have hlin :
        2 * intDelta (x * y) =
          2 * (x ^ 2 * intDelta y + y ^ 2 * intDelta x + 2 * intDelta x * intDelta y) := by
      calc
        2 * intDelta (x * y) = x * y - (x * y) ^ 2 := two_mul_intDelta (x * y)
        _ = x ^ 2 * (y - y ^ 2) + y ^ 2 * (x - x ^ 2) + (x - x ^ 2) * (y - y ^ 2) := by ring
        _ = x ^ 2 * (2 * intDelta y) + y ^ 2 * (2 * intDelta x) +
              (2 * intDelta x) * (2 * intDelta y) := by
              rw [← two_mul_intDelta x, ← two_mul_intDelta y]
        _ = 2 * (x ^ 2 * intDelta y + y ^ 2 * intDelta x + 2 * intDelta x * intDelta y) := by
              ring
    omega

@[simp]
lemma delta_int_eq (a : ℤ) : delta a = (a - a ^ 2) / 2 := rfl

/-- On `ℤ`, the `p = 2` Frobenius lift `frobeniusLift` is the identity map. -/
theorem frobeniusLift_int_eq_id : frobeniusLift (R := ℤ) = id := by
  funext a
  have h := two_mul_intDelta a
  change a ^ 2 + 2 * intDelta a = a
  omega

@[simp]
lemma frobeniusLift_int_apply (a : ℤ) : frobeniusLift a = a :=
  congrFun frobeniusLift_int_eq_id a

/-- `ℤ` is a perfect `p = 2` `δ`-ring. -/
theorem isPerfectDeltaRing_int : IsPerfectDeltaRing ℤ := by
  unfold IsPerfectDeltaRing
  rw [frobeniusLift_int_eq_id]
  exact Function.bijective_id

/-- Uniqueness of the `p = 2` `δ`-ring structure on `ℤ`: because `ℤ →+* ℤ` is a subsingleton,
every `DeltaRing2 ℤ` structure has `frobeniusLift = id` and therefore `delta = intDelta`. -/
instance instUniqueDeltaRing2Int : Unique (DeltaRing2 ℤ) where
  default := instDeltaRing2Int
  uniq d := by
    cases d with
    | mk d_delta d_zero d_one d_add d_mul =>
      congr
      funext a
      let dInst : DeltaRing2 ℤ := ⟨d_delta, d_zero, d_one, d_add, d_mul⟩
      have hHom : @frobeniusLiftRingHom ℤ _ dInst = RingHom.id ℤ :=
        Subsingleton.elim _ _
      have ha : a ^ 2 + 2 * d_delta a = a :=
        congrArg (fun f : ℤ →+* ℤ ↦ f a) hHom
      have hint : 2 * intDelta a = a - a ^ 2 := two_mul_intDelta a
      omega

/-- In **every** `DeltaRing2 R`, `delta` commutes with `Int.castRingHom R`, making `ℤ` initial in
`DeltaRing2Cat`. -/
theorem delta_intCast {R : Type u} [CommRing R] [DeltaRing2 R] (a : ℤ) :
    delta (a : R) = ((intDelta a : ℤ) : R) := by
  have hNat : ∀ n : ℕ, delta ((n : ℤ) : R) = ((intDelta (n : ℤ) : ℤ) : R) := by
    intro n
    induction n with
    | zero => simp [intDelta, delta_zero]
    | succ n ih =>
      have hstep : intDelta ((n : ℤ) + 1) = intDelta (n : ℤ) - (n : ℤ) := by
        have hlin : 2 * intDelta ((n : ℤ) + 1) = 2 * (intDelta (n : ℤ) - (n : ℤ)) := by
          calc
            2 * intDelta ((n : ℤ) + 1) = ((n : ℤ) + 1) - ((n : ℤ) + 1) ^ 2 :=
              two_mul_intDelta ((n : ℤ) + 1)
            _ = ((n : ℤ) - (n : ℤ) ^ 2) - 2 * (n : ℤ) := by ring
            _ = 2 * intDelta (n : ℤ) - 2 * (n : ℤ) := by rw [← two_mul_intDelta (n : ℤ)]
            _ = 2 * (intDelta (n : ℤ) - (n : ℤ)) := by ring
        omega
      have hcastR : (((n + 1 : ℕ) : ℤ) : R) = ((n : ℤ) : R) + 1 := by
        push_cast
        ring
      have hcastZ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by
        push_cast
        ring
      rw [hcastR, delta_add, ih, delta_one, hcastZ, hstep]
      push_cast
      ring
  rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
  · exact hNat n
  · have hzero : delta (((n : ℤ) : R) + ((-(n : ℤ) : ℤ) : R)) = 0 := by
      have hc : ((n : ℤ) : R) + ((-(n : ℤ) : ℤ) : R) = 0 := by push_cast; ring
      rw [hc, delta_zero]
    rw [delta_add] at hzero
    have hnegR : delta ((-(n : ℤ) : ℤ) : R) = -delta ((n : ℤ) : R) - ((n : ℤ) : R) ^ 2 := by
      calc
        delta ((-(n : ℤ) : ℤ) : R)
          = (delta ((n : ℤ) : R) + delta ((-(n : ℤ) : ℤ) : R) -
              ((n : ℤ) : R) * ((-(n : ℤ) : ℤ) : R)) -
            delta ((n : ℤ) : R) + ((n : ℤ) : R) * ((-(n : ℤ) : ℤ) : R) := by ring
        _ = 0 - delta ((n : ℤ) : R) + ((n : ℤ) : R) * ((-(n : ℤ) : ℤ) : R) := by rw [hzero]
        _ = -delta ((n : ℤ) : R) - ((n : ℤ) : R) ^ 2 := by
              push_cast
              ring
    have hnegZ : intDelta (-(n : ℤ)) = -intDelta (n : ℤ) - (n : ℤ) ^ 2 := by
      have hlin : 2 * intDelta (-(n : ℤ)) = 2 * (-intDelta (n : ℤ) - (n : ℤ) ^ 2) := by
        calc
          2 * intDelta (-(n : ℤ)) = -(n : ℤ) - (-(n : ℤ)) ^ 2 := two_mul_intDelta (-(n : ℤ))
          _ = -((n : ℤ) - (n : ℤ) ^ 2) - 2 * (n : ℤ) ^ 2 := by ring
          _ = -(2 * intDelta (n : ℤ)) - 2 * (n : ℤ) ^ 2 := by rw [← two_mul_intDelta (n : ℤ)]
          _ = 2 * (-intDelta (n : ℤ) - (n : ℤ) ^ 2) := by ring
      omega
    rw [hnegR, hNat n, hnegZ]
    push_cast
    ring

/-- The unique `DeltaRing2Hom` from `ℤ` into any `p = 2` `δ`-ring `R`. -/
def intCastDeltaHom (R : Type u) [CommRing R] [DeltaRing2 R] : DeltaRing2Hom ℤ R where
  toRingHom := Int.castRingHom R
  map_delta' a := (delta_intCast a).symm

end IntDeltaRing

/-! ## Section 5: Dual Integers `DualInt = ℤ[ε]/(ε²)` & 1-Step Perfection Colimit -/

/-- The ring of dual integers `ℤ[ε]/(ε²)` on underlying carrier `ℤ × ℤ`, representing
`a + b ε` as `⟨a, b⟩` with multiplication `(a₁, b₁) * (a₂, b₂) = (a₁ a₂, a₁ b₂ + b₁ a₂)`. -/
@[ext]
structure DualInt : Type where
  /-- Constant part `a` of `a + b ε`. -/
  fst : ℤ
  /-- Dual/infinitesimal coefficient `b` of `a + b ε`. -/
  snd : ℤ
  deriving DecidableEq, Repr

namespace DualInt

/-- Underlying carrier equivalence `DualInt ≃ ℤ × ℤ`. -/
def equivProd : DualInt ≃ ℤ × ℤ where
  toFun x := (x.fst, x.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The square-zero generator `ε = (0, 1) ∈ ℤ[ε]/(ε²)`. -/
def eps : DualInt := ⟨0, 1⟩

instance : Zero DualInt := ⟨⟨0, 0⟩⟩
instance : One DualInt := ⟨⟨1, 0⟩⟩
instance : Add DualInt := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg DualInt := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
instance : Sub DualInt := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance : Mul DualInt := ⟨fun x y ↦ ⟨x.fst * y.fst, x.fst * y.snd + x.snd * y.fst⟩⟩
instance : NatCast DualInt := ⟨fun n ↦ ⟨n, 0⟩⟩
instance : IntCast DualInt := ⟨fun z ↦ ⟨z, 0⟩⟩

@[simp] lemma zero_fst : (0 : DualInt).fst = 0 := rfl
@[simp] lemma zero_snd : (0 : DualInt).snd = 0 := rfl
@[simp] lemma one_fst : (1 : DualInt).fst = 1 := rfl
@[simp] lemma one_snd : (1 : DualInt).snd = 0 := rfl
@[simp] lemma add_fst (x y : DualInt) : (x + y).fst = x.fst + y.fst := rfl
@[simp] lemma add_snd (x y : DualInt) : (x + y).snd = x.snd + y.snd := rfl
@[simp] lemma neg_fst (x : DualInt) : (-x).fst = -x.fst := rfl
@[simp] lemma neg_snd (x : DualInt) : (-x).snd = -x.snd := rfl
@[simp] lemma sub_fst (x y : DualInt) : (x - y).fst = x.fst - y.fst := rfl
@[simp] lemma sub_snd (x y : DualInt) : (x - y).snd = x.snd - y.snd := rfl
@[simp] lemma mul_fst (x y : DualInt) : (x * y).fst = x.fst * y.fst := rfl
@[simp] lemma mul_snd (x y : DualInt) : (x * y).snd = x.fst * y.snd + x.snd * y.fst := rfl
@[simp] lemma natCast_fst (n : ℕ) : (n : DualInt).fst = n := rfl
@[simp] lemma natCast_snd (n : ℕ) : (n : DualInt).snd = 0 := rfl
@[simp] lemma intCast_fst (z : ℤ) : (z : DualInt).fst = z := rfl
@[simp] lemma intCast_snd (z : ℤ) : (z : DualInt).snd = 0 := rfl

instance instCommRing : CommRing DualInt where
  add := (· + ·)
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero := 0
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := @nsmulRec DualInt ⟨0⟩ ⟨(· + ·)⟩
  neg := Neg.neg
  sub := (· - ·)
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  zsmul := @zsmulRec DualInt ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec DualInt ⟨0⟩ ⟨(· + ·)⟩)
  neg_add_cancel a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  mul := (· * ·)
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one := 1
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  natCast n := n
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp
  intCast z := z
  intCast_ofNat n := by ext <;> simp
  intCast_negSucc n := by ext <;> rfl
  npow := @npowRec DualInt ⟨1⟩ ⟨(· * ·)⟩
  mul_comm a b := by ext <;> simp <;> ring

@[simp]
lemma sq_fst (x : DualInt) : (x ^ 2).fst = x.fst ^ 2 := by
  simp [sq]

@[simp]
lemma sq_snd (x : DualInt) : (x ^ 2).snd = 2 * (x.fst * x.snd) := by
  simp [sq]
  ring

@[simp]
lemma ofNat_two_fst : ((2 : DualInt)).fst = 2 := rfl

@[simp]
lemma ofNat_two_snd : ((2 : DualInt)).snd = 0 := rfl

/-- First-projection augmentation homomorphism `fstRingHom : ℤ[ε]/(ε²) →+* ℤ` sending `ε ↦ 0`. -/
@[simps]
def fstRingHom : DualInt →+* ℤ where
  toFun := fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `p = 2` Joyal `δ`-operation on `DualInt = ℤ[ε]/(ε²)`:
`δ(a, b) = ((a - a²) / 2, -(a * b))`. -/
def dualDelta (x : DualInt) : DualInt :=
  ⟨intDelta x.fst, -(x.fst * x.snd)⟩

instance instDeltaRing2 : DeltaRing2 DualInt where
  delta := dualDelta
  delta_zero := by ext <;> decide
  delta_one := by ext <;> decide
  delta_add x y := by
    ext
    · exact delta_add x.fst y.fst
    · simp only [dualDelta, add_fst, add_snd, sub_snd, mul_snd]
      ring
  delta_mul x y := by
    ext
    · simpa [dualDelta] using delta_mul x.fst y.fst
    · simp only [dualDelta, mul_fst, mul_snd, add_snd, sq_fst, sq_snd, ofNat_two_fst,
        ofNat_two_snd]
      ring

@[simp]
lemma delta_mk (a b : ℤ) : delta (⟨a, b⟩ : DualInt) = ⟨intDelta a, -(a * b)⟩ := rfl

/-- Explicit formula for the `p = 2` Frobenius lift on `DualInt`:
`frobeniusLift ⟨a, b⟩ = ⟨a, 0⟩` (annihilating the infinitesimal coordinate `b ε`). -/
theorem frobeniusLift_mk (a b : ℤ) : frobeniusLift (⟨a, b⟩ : DualInt) = ⟨a, 0⟩ := by
  unfold frobeniusLift
  ext
  · simp only [add_fst, sq_fst, mul_fst, ofNat_two_fst, delta_mk]
    have h := two_mul_intDelta a
    omega
  · simp only [add_snd, sq_snd, mul_snd, ofNat_two_fst, ofNat_two_snd, delta_mk]
    ring

@[simp]
lemma frobeniusLift_eq (x : DualInt) : frobeniusLift x = ⟨x.fst, 0⟩ :=
  frobeniusLift_mk x.fst x.snd

/-- `frobeniusLift` on `DualInt` is **not** injective (`ε = ⟨0, 1⟩` and `0 = ⟨0, 0⟩` both map
to `⟨0, 0⟩`). -/
theorem not_injective_frobeniusLift :
    ¬ Function.Injective (frobeniusLift (R := DualInt)) := by
  intro hInj
  have hEq : frobeniusLift eps = frobeniusLift (0 : DualInt) := by
    simp [eps]
  have hNe : eps ≠ (0 : DualInt) := by decide
  exact hNe (hInj hEq)

/-- `frobeniusLift` on `DualInt` is **not** surjective (`ε = ⟨0, 1⟩` is not in its range). -/
theorem not_surjective_frobeniusLift :
    ¬ Function.Surjective (frobeniusLift (R := DualInt)) := by
  intro hSurj
  rcases hSurj eps with ⟨x, hx⟩
  have hsnd := congrArg snd hx
  simp [eps] at hsnd

/-- `DualInt = ℤ[ε]/(ε²)` is **not** a perfect `δ`-ring (`¬ Function.Bijective frobeniusLift`). -/
theorem not_isPerfectDeltaRing : ¬ IsPerfectDeltaRing DualInt := by
  intro hBij
  exact not_injective_frobeniusLift hBij.1

/-- First projection `fst : DualInt →+* ℤ` is a `DeltaRing2Hom`. -/
def fstDeltaHom : DeltaRing2Hom DualInt ℤ where
  toRingHom := fstRingHom
  map_delta' _ := rfl

/-- Constant-leg cocone on `endomorphismChain (CommRingCat.ofHom (frobeniusLiftRingHom DualInt))`
with vertex `CommRingCat.of ℤ` and every leg equal to `CommRingCat.ofHom fstRingHom`. -/
def perfectionCommRingCocone :
    Cocone (endomorphismChain (CommRingCat.ofHom (frobeniusLiftRingHom DualInt))) :=
  mkEndomorphismChainCocone
    (CommRingCat.ofHom (frobeniusLiftRingHom DualInt))
    (CommRingCat.of ℤ)
    (fun _ ↦ CommRingCat.ofHom fstRingHom)
    (fun _ ↦ by
      ext x
      simp)

/-- **1-Step Perfection Colimit Theorem in `CommRingCat`:** `(ℤ, fstRingHom)` is the sequential
colimit of `DualInt --φ--> DualInt --φ--> ⋯` in `CommRingCat`, because `φ` kills `ε` in 1 step!
-/
def perfectionCommRingCocone_isColimit : IsColimit perfectionCommRingCocone where
  desc s := CommRingCat.ofHom (Int.castRingHom s.pt)
  fac s n := by
    have hw := endomorphismChain_cocone_w s n
    ext x
    have hx := congrArg (fun f : CommRingCat.of DualInt ⟶ s.pt ↦ f.hom x) hw
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      frobeniusLiftRingHom_apply, frobeniusLift_eq] at hx
    have hcast : (⟨x.fst, 0⟩ : DualInt) = (x.fst : DualInt) := rfl
    rw [hcast, map_intCast] at hx
    simpa [perfectionCommRingCocone] using hx
  uniq s m _ := by
    ext a
    exact congrArg (fun f : ℤ →+* s.pt ↦ f a) (RingHom.eq_intCast' m.hom)

/-- Bundled object `DualInt` in `DeltaRing2Cat`. -/
abbrev dualIntObj : DeltaRing2Cat.{0} := DeltaRing2Cat.of DualInt

/-- Bundled object `ℤ` in `DeltaRing2Cat`. -/
abbrev intObj : DeltaRing2Cat.{0} := DeltaRing2Cat.of ℤ

/-- Constant-leg cocone on `endomorphismChain (frobeniusNatEndo.app dualIntObj)` in
`DeltaRing2Cat` with vertex `intObj` (`ℤ`) and every leg equal to `fstDeltaHom`. -/
def perfectionDeltaCocone :
    Cocone (endomorphismChain (DeltaRing2Cat.frobeniusNatEndo.app dualIntObj)) :=
  mkEndomorphismChainCocone
    (DeltaRing2Cat.frobeniusNatEndo.app dualIntObj)
    intObj
    (fun _ ↦ fstDeltaHom)
    (fun _ ↦ by
      apply DeltaRing2Cat.hom_ext
      intro (x : DualInt)
      change (frobeniusLift x).fst = x.fst
      rw [frobeniusLift_eq])

/-- **1-Step Perfection Colimit Theorem in `DeltaRing2Cat`:** `(ℤ, fstDeltaHom)` is the
sequential colimit of `DualInt --φ--> DualInt --φ--> ⋯` in `DeltaRing2Cat`. -/
def perfectionDeltaCocone_isColimit : IsColimit perfectionDeltaCocone where
  desc s := intCastDeltaHom s.pt.carrier
  fac s n := by
    have hw := endomorphismChain_cocone_w s n
    apply DeltaRing2Cat.hom_ext
    intro (x : DualInt)
    have hx : (s.ι.app (n + 1)).toRingHom (frobeniusLift x) = (s.ι.app n).toRingHom x :=
      congrArg (fun f : dualIntObj ⟶ s.pt ↦ f.toRingHom x) hw
    have hcast : frobeniusLift x = (x.fst : DualInt) := by
      rw [frobeniusLift_eq]
      rfl
    rw [hcast, map_intCast] at hx
    exact hx
  uniq s m _ := by
    apply DeltaRing2Cat.hom_ext
    intro (a : ℤ)
    exact congrArg (fun f : ℤ →+* s.pt.carrier ↦ f a) (RingHom.eq_intCast' m.toRingHom)

/-- The concrete perfection slice algebra `(ℤ, fstDeltaHom)` over `(DualInt, φ)` in
`DeltaRing2Cat`, obtained by specializing `perfectionSliceAlg` to `perfectionDeltaCocone`. -/
def perfectionSliceAlgDualInt :
    SliceAlgebra (𝟭 DeltaRing2Cat.{0})
      ⟨dualIntObj, DeltaRing2Cat.frobeniusNatEndo.app dualIntObj⟩ :=
  perfectionSliceAlg DeltaRing2Cat.frobeniusNatEndo dualIntObj perfectionDeltaCocone_isColimit

/-- **Concrete Instantiation of Theorem B on `DualInt = ℤ[ε]/(ε²)`:** `(ℤ, fstDeltaHom)` is the
initial algebra of `sliceEndofunctor (𝟭 DeltaRing2Cat) ⟨DualInt, φ⟩`, and its perfection `ℤ`
satisfies `frobeniusLift = id`. -/
def perfectionSliceAlgDualInt_isInitial :
    IsInitial perfectionSliceAlgDualInt :=
  theoremB_perfectionSliceAlg_isInitial
    DeltaRing2Cat.frobeniusNatEndo dualIntObj perfectionDeltaCocone_isColimit

end DualInt

/-! ## Section 6: Mandatory 4-Layer Lean 4 Definition Check Gate (`namespace Checks`) -/

namespace Checks

/-! ### Layer 1: Inhabitation (Non-Degeneracy of Formalized Carriers) -/

/-- Layer 1 witness: `DualInt` is `Nontrivial` (`0 ≠ ε`). -/
instance instNontrivialDualInt : Nontrivial DualInt :=
  ⟨⟨0, DualInt.eps, by decide⟩⟩

/-- Explicit existential non-degeneracy witness on `DualInt`. -/
theorem dualInt_exists_ne : ∃ x y : DualInt, x ≠ y :=
  ⟨0, DualInt.eps, by decide⟩

/-- A concrete **non-fixed** slice algebra over `(DualInt, φ)` in `DeltaRing2Cat`: carrier
`(DualInt, φ : DualInt ⟶ DualInt)` equipped with structure endomorphism `ψ = φ`. Since `φ` is
idempotent (`φ ∘ φ = φ`), `(φ ≫ φ) ≫ φ = φ` holds, while `ψ = φ` is NOT an isomorphism. -/
def nonFixedDualIntSliceAlg :
    SliceAlgebra (𝟭 DeltaRing2Cat.{0})
      ⟨DualInt.dualIntObj, DeltaRing2Cat.frobeniusNatEndo.app DualInt.dualIntObj⟩ where
  a := Under.mk (DeltaRing2Cat.frobeniusNatEndo.app DualInt.dualIntObj)
  str := Under.homMk (DeltaRing2Cat.frobeniusNatEndo.app DualInt.dualIntObj) (by
    apply DeltaRing2Cat.hom_ext
    intro (x : DualInt)
    change frobeniusLift (frobeniusLift (frobeniusLift x)) = frobeniusLift x
    rw [DualInt.frobeniusLift_eq, DualInt.frobeniusLift_mk, DualInt.frobeniusLift_mk])

/-! ### Layer 2: Bidirectional Separation (Positive & Negative Witnesses for Core Predicates) -/

/-- Layer 2 positive witness for `IsPerfectDeltaRing`: `ℤ` is perfect. -/
theorem layer2_pos_isPerfectDeltaRing : IsPerfectDeltaRing ℤ :=
  isPerfectDeltaRing_int

/-- Layer 2 negative counter-witness for `IsPerfectDeltaRing`: `DualInt` is NOT perfect. -/
theorem layer2_neg_isPerfectDeltaRing : ¬ IsPerfectDeltaRing DualInt :=
  DualInt.not_isPerfectDeltaRing

/-- Layer 2 positive witness for `IsFixedPointSliceAlg`: the 1-step perfection initial slice
algebra `(ℤ, fstDeltaHom)` over `(DualInt, φ)` is a fixed-point slice algebra. -/
theorem isFixedPointSliceAlg_dualIntPerfection :
    IsFixedPointSliceAlg DualInt.perfectionSliceAlgDualInt :=
  lambek_isIso _ DualInt.perfectionSliceAlgDualInt DualInt.perfectionSliceAlgDualInt_isInitial

/-- Layer 2 negative counter-witness for `IsFixedPointSliceAlg`: `nonFixedDualIntSliceAlg` over
`(DualInt, φ)` is NOT a fixed-point slice algebra (`φ` annihilates `ε`). -/
theorem not_isFixedPointSliceAlg_nonFixedDualInt :
    ¬ IsFixedPointSliceAlg nonFixedDualIntSliceAlg := by
  rw [isFixedPointSliceAlg_iff_isIso_right]
  intro hIso
  have hRingIso : IsIso (DeltaRing2Cat.forgetToCommRingCat.map nonFixedDualIntSliceAlg.str.right) :=
    DeltaRing2Cat.forgetToCommRingCat.map_isIso _
  let e : DualInt ≃+* DualInt :=
    (asIso (DeltaRing2Cat.forgetToCommRingCat.map
      nonFixedDualIntSliceAlg.str.right)).commRingCatIsoToRingEquiv
  have he : ∀ x : DualInt, e x = frobeniusLift x := fun _ ↦ rfl
  exact DualInt.not_injective_frobeniusLift (by simpa [he] using e.injective)

/-- Layer 1 corollary: `SliceAlgebra` over `(DualInt, φ)` is `Nontrivial`, separated by
`IsFixedPointSliceAlg`. -/
instance instNontrivialDualIntSliceAlgebra :
    Nontrivial (SliceAlgebra (𝟭 DeltaRing2Cat.{0})
      ⟨DualInt.dualIntObj, DeltaRing2Cat.frobeniusNatEndo.app DualInt.dualIntObj⟩) :=
  ⟨⟨DualInt.perfectionSliceAlgDualInt, nonFixedDualIntSliceAlg, fun hEq ↦
    not_isFixedPointSliceAlg_nonFixedDualInt (hEq ▸ isFixedPointSliceAlg_dualIntPerfection)⟩⟩

/-! ### Layer 3: Projection & Derived Sanity (Stock Mathlib Projections & Boundary Lemmas) -/

/-- Layer 3 stock `CommRing` projection check on `DualInt`. -/
def dualIntCommRingCheck : CommRing DualInt := inferInstance

/-- Layer 3 stock `RingHom` projection check on `frobeniusLiftRingHom`. -/
def dualIntFrobeniusRingHomCheck : DualInt →+* DualInt :=
  frobeniusLiftRingHom DualInt

/-- Derived boundary lemma 1: `ε² = 0` in `DualInt`. -/
theorem dualInt_eps_sq : DualInt.eps ^ 2 = 0 := by decide

/-- Derived boundary lemma 2: `δ(ε) = 0` in `DualInt` (`ε` is a rank-1 `δ`-nilpotent element). -/
theorem dualInt_delta_eps : delta DualInt.eps = 0 := by decide

/-- Derived boundary lemma 3: `frobeniusLift ε = 0` in `DualInt`. -/
theorem dualInt_frobeniusLift_eps : frobeniusLift DualInt.eps = 0 := by decide

/-- Derived boundary lemma 4: `frobeniusLift` on `DualInt` is idempotent (`φ(φ(x)) = φ(x)`). -/
theorem dualInt_frobeniusLift_idem (x : DualInt) :
    frobeniusLift (frobeniusLift x) = frobeniusLift x := by
  rw [DualInt.frobeniusLift_eq, DualInt.frobeniusLift_mk]

/-- Derived boundary lemma 5: non-trivial Nygaard filtration separation on `DualInt` at ideal
`I = Ideal.span {ε}`: `ε ∈ N^{≥ 1} DualInt` whereas `1 ∉ N^{≥ 1} DualInt`. -/
theorem dualInt_nygaard_separation :
    DualInt.eps ∈ nygaardLevel (DeltaRing2.toDeltaStructure DualInt)
        (Ideal.span {DualInt.eps}) 1 ∧
      (1 : DualInt) ∉ nygaardLevel (DeltaRing2.toDeltaStructure DualInt)
        (Ideal.span {DualInt.eps}) 1 := by
  constructor
  · rw [nygaardLevel, pow_one, Ideal.mem_comap]
    change frobeniusLift DualInt.eps ∈ Ideal.span {DualInt.eps}
    rw [dualInt_frobeniusLift_eps]
    exact Ideal.zero_mem _
  · intro h1
    rw [nygaardLevel, pow_one, Ideal.mem_comap, map_one, Ideal.mem_span_singleton] at h1
    rcases h1 with ⟨c, hc⟩
    have hfst := congrArg DualInt.fst hc
    simp [DualInt.eps] at hfst

/-! ### Layer 4: Kernel Axiom Gate (`#guard_msgs in #print axioms`) -/

section KernelAxiomGate

set_option linter.hashCommand false

/-- info: 'HomotopyCRM.lambek_isIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.lambek_isIso

/-- info: 'HomotopyCRM.sliceLambek_right_isIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.sliceLambek_right_isIso

/-- info: 'HomotopyCRM.initFixedPointCoalgebraUnder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.initFixedPointCoalgebraUnder

/-- info: 'HomotopyCRM.theoremA_homEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theoremA_homEquiv

/-- info: 'HomotopyCRM.theoremA_isInitial_fixedPointCoalgebraUnder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theoremA_isInitial_fixedPointCoalgebraUnder

/-- info: 'HomotopyCRM.endomorphismColimitShiftIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.endomorphismColimitShiftIso

/-- info: 'HomotopyCRM.theoremB_natEndo_app_eq_shift_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theoremB_natEndo_app_eq_shift_inv

/-- info: 'HomotopyCRM.theoremB_isIso_natEndo_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theoremB_isIso_natEndo_app

/-- info: 'HomotopyCRM.theoremB_perfectionSliceAlg_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.theoremB_perfectionSliceAlg_isInitial

/-- info: 'HomotopyCRM.delta_comm_frobeniusLift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.delta_comm_frobeniusLift

/-- info: 'HomotopyCRM.instDeltaRing2Int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.instDeltaRing2Int

/-- info: 'HomotopyCRM.isPerfectDeltaRing_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.isPerfectDeltaRing_int

/-- info: 'HomotopyCRM.instUniqueDeltaRing2Int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.instUniqueDeltaRing2Int

/-- info: 'HomotopyCRM.DualInt.instCommRing' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.DualInt.instCommRing

/-- info: 'HomotopyCRM.DualInt.instDeltaRing2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.DualInt.instDeltaRing2

/-- info: 'HomotopyCRM.DualInt.not_isPerfectDeltaRing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.DualInt.not_isPerfectDeltaRing

/-- info: 'HomotopyCRM.DualInt.perfectionCommRingCocone_isColimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.DualInt.perfectionCommRingCocone_isColimit

/-- info: 'HomotopyCRM.DualInt.perfectionDeltaCocone_isColimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.DualInt.perfectionDeltaCocone_isColimit

/-- info: 'HomotopyCRM.DualInt.perfectionSliceAlgDualInt_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.DualInt.perfectionSliceAlgDualInt_isInitial

/-- info: 'HomotopyCRM.Checks.isFixedPointSliceAlg_dualIntPerfection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.isFixedPointSliceAlg_dualIntPerfection

/-- info: 'HomotopyCRM.Checks.not_isFixedPointSliceAlg_nonFixedDualInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.Checks.not_isFixedPointSliceAlg_nonFixedDualInt

end KernelAxiomGate

end Checks

end HomotopyCRM
