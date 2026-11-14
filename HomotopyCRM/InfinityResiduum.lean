/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HomotopyCRM Formalization Team
-/
import HomotopyCRM.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Pure Axiom-of-Infinity Residua in `FinSet` and Nominal Crossing Point (`Ch. 1, §1.6`)

This module formalizes Chapter 1, §1.6 of the *Categorical Reverse Mathematics* monograph,
isolating pure Axis III (`Inf`) structural residua in `mathbf{FinSet}` (where `LEM` and
external `AC` hold completely) together with the nominal crossing point `𝔸 ∈ Nom`:

1. **Profinite Lasso Initial-Algebra Phantom (`Section 1`):**
   - Formalizes pointed single-successor dynamical systems `PointedDynSys` (algebras for the
     polynomial functor `S(X) = 1 ⨿ X`) and their category structure.
   - Proves initiality of `natDynSys` (`ℕ`, `0`, `Nat.succ`) externally (`Unique (PointedDynHom
     natDynSys A)`), contrasted with internal `FinSet` non-initiality: no `Fintype` object admits
     a `PointedDynHom` into `lassoDynSys (card A) 1` (`IsEmpty`).
   - Formalizes finite dynamical lassos `L_{p,q}` (`LassoCarrier p q := Fin (p + q)`, `q ≥ 1`),
     stem-period collision `s^{p+q}(x_0) = s^p(x_0)`, coherent surjective transition homomorphisms
     `lassoTransition hp hq` for `p' ≤ p` and `q' ∣ q`, the periodic `p = 0` identification
     `LassoCarrier 0 q ≃ ZMod q`, and the inverse limit projection `profiniteLassoToZHat :
     ProfiniteLasso → ProfiniteZHat` (surjective onto the profinite integers `ProfiniteZHat`, with
     `Infinite ProfiniteLasso`).

2. **Dedekind / Pigeonhole Residuum and the Nominal Crossing Point (`Section 2`):**
   - Defines `DedekindResiduum X := {f : X → X | Injective f ∧ ¬ Bijective f}`.
   - Proves `FinSet` Pigeonhole triviality (`dedekindResiduum_eq_empty_of_fintype`) vs. `ℕ`
     non-emptiness (`Nat.succ ∈ DedekindResiduum ℕ`).
   - Proves the `Nom` crossing point on the infinite atom carrier `𝔸 = ℕ`: every finitely
     supported (`SupportsMap S f`) injective endomorphism `f : ℕ → ℕ` fixes all atoms `x ∉ S`,
     preserves `S`, and is therefore bijective (`nominalDedekindResiduum_eq_empty`), isolating
     `Inf ∧ ¬ AC_ω`.

3. **Biproduct-Tail Cokernel (`Section 3`):**
   - Formalizes `finsuppToPiAddHom : (I →₀ A) →+ (I → A)` and the tail cokernel
     `TailCokernel I A := (I → A) ⧸ range (finsuppToPiAddHom I A)`.
   - Proves finitary collapse `Subsingleton (TailCokernel I A)` for `[Fintype I]` via
     `finsuppEquivPiOfFintype` vs. `Nontrivial (TailCokernel ℕ A)` for `[Nontrivial A]`.

4. **Summary Theorem & Mandatory 4-Layer Definition Check Gate (`Sections 4–5`):**
   - Packages `chapter1_pure_infinity_residua_summary` and verifies Carrier Inhabitation,
     Bidirectional Separation, `mathlib4` projections, and `#guard_msgs in #print axioms`.
-/

namespace HomotopyCRM

/-! ## Section 1: Profinite Lasso Initial-Algebra Phantom (`L_{p,q} → ℤ̂`) -/

/-- A pointed dynamical system `(X, x_0, s)`, i.e., an algebra for `S(X) = 1 ⨿ X`. -/
structure PointedDynSys.{u} where
  Carrier : Type u
  base : Carrier
  step : Carrier → Carrier

/-- Structure-preserving homomorphism of pointed dynamical systems. -/
@[ext]
structure PointedDynHom (A : PointedDynSys.{u}) (B : PointedDynSys.{v}) where
  toFun : A.Carrier → B.Carrier
  map_base' : toFun A.base = B.base
  map_step' : ∀ x : A.Carrier, toFun (A.step x) = B.step (toFun x)

namespace PointedDynHom

instance instFunLike (A : PointedDynSys.{u}) (B : PointedDynSys.{v}) :
    FunLike (PointedDynHom A B) A.Carrier B.Carrier where
  coe := PointedDynHom.toFun
  coe_injective' := by
    intro f g h
    cases f
    cases g
    cases h
    rfl

@[simp]
theorem coe_mk (A : PointedDynSys.{u}) (B : PointedDynSys.{v})
    (f : A.Carrier → B.Carrier) (hb : f A.base = B.base)
    (hs : ∀ x, f (A.step x) = B.step (f x)) :
    ⇑(⟨f, hb, hs⟩ : PointedDynHom A B) = f := rfl

@[simp]
theorem map_base {A : PointedDynSys.{u}} {B : PointedDynSys.{v}} (φ : PointedDynHom A B) :
    φ A.base = B.base := φ.map_base'

@[simp]
theorem map_step {A : PointedDynSys.{u}} {B : PointedDynSys.{v}} (φ : PointedDynHom A B)
    (x : A.Carrier) :
    φ (A.step x) = B.step (φ x) := φ.map_step' x

/-- Identity homomorphism of pointed dynamical systems. -/
def id (A : PointedDynSys.{u}) : PointedDynHom A A where
  toFun := _root_.id
  map_base' := rfl
  map_step' := fun _ => rfl

/-- Composition of pointed dynamical system homomorphisms. -/
def comp {A : PointedDynSys.{u}} {B : PointedDynSys.{v}} {C : PointedDynSys.{w}}
    (ψ : PointedDynHom B C) (φ : PointedDynHom A B) : PointedDynHom A C where
  toFun := ψ ∘ φ
  map_base' := by simp [Function.comp]
  map_step' := fun x => by simp [Function.comp]

@[simp]
theorem id_apply (A : PointedDynSys.{u}) (x : A.Carrier) : id A x = x := rfl

@[simp]
theorem comp_apply {A : PointedDynSys.{u}} {B : PointedDynSys.{v}} {C : PointedDynSys.{w}}
    (ψ : PointedDynHom B C) (φ : PointedDynHom A B) (x : A.Carrier) :
    comp ψ φ x = ψ (φ x) := rfl

end PointedDynHom

instance instCategoryPointedDynSys : CategoryTheory.Category PointedDynSys.{u} where
  Hom A B := PointedDynHom A B
  id := PointedDynHom.id
  comp φ ψ := PointedDynHom.comp ψ φ
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

/-- The Natural Numbers Object viewed as a pointed dynamical system `(ℕ, 0, succ)`. -/
@[reducible] def natDynSys : PointedDynSys.{0} where
  Carrier := ℕ
  base := 0
  step := Nat.succ

/-- Canonical iterator from `natDynSys` into any pointed dynamical system `A`. -/
def natDynHom (A : PointedDynSys.{u}) : PointedDynHom natDynSys A where
  toFun n := A.step^[n] A.base
  map_base' := rfl
  map_step' (n : ℕ) := by
    change A.step^[n + 1] A.base = A.step (A.step^[n] A.base)
    exact Function.iterate_succ_apply' A.step n A.base

/-- Every homomorphism out of `natDynSys` agrees with iteration of `A.step`. -/
theorem eq_natDynHom (A : PointedDynSys.{u}) (φ : PointedDynHom natDynSys A) :
    φ = natDynHom A := by
  ext (n : ℕ)
  induction n with
  | zero =>
    change φ 0 = A.step^[0] A.base
    exact φ.map_base
  | succ n ih =>
    change φ (n + 1) = A.step^[n + 1] A.base
    have hstep : φ (n + 1) = A.step (φ n) := φ.map_step n
    have hprev : φ n = A.step^[n] A.base := ih
    rw [hstep, hprev, Function.iterate_succ_apply']

instance instUniqueNatDynHom (A : PointedDynSys.{u}) : Unique (PointedDynHom natDynSys A) where
  default := natDynHom A
  uniq φ := eq_natDynHom A φ

/-- Carrier `Fin (p + q)` of the finite dynamical lasso `L_{p,q}` (`p ≥ 0` stem, `q ≥ 1` cycle). -/
abbrev LassoCarrier (p q : ℕ) : Type := Fin (p + q)

/-- Base point `0` of the dynamical lasso `L_{p,q}`. -/
def lassoBase (p q : ℕ) [NeZero q] : LassoCarrier p q :=
  ⟨0, Nat.add_pos_right p (NeZero.pos q)⟩

/-- Successor step on the finite dynamical lasso `L_{p,q}`, looping from `p + q - 1` back to `p`. -/
def lassoSucc (p q : ℕ) [NeZero q] (x : LassoCarrier p q) : LassoCarrier p q :=
  if h : x.1 + 1 < p + q then ⟨x.1 + 1, h⟩ else ⟨p, Nat.lt_add_of_pos_right (NeZero.pos q)⟩

/-- The finite pointed dynamical lasso `L_{p,q}` in `FinSet`. -/
@[reducible] def lassoDynSys (p q : ℕ) [NeZero q] : PointedDynSys.{0} where
  Carrier := LassoCarrier p q
  base := lassoBase p q
  step := lassoSucc p q

/-- Explicit orbit map `ℕ → L_{p,q}` sending `n < p` to `n` and `n ≥ p` to `p + (n - p) % q`. -/
def lassoOfNat (p q : ℕ) [NeZero q] (n : ℕ) : LassoCarrier p q :=
  if h : n < p then
    ⟨n, Nat.lt_of_lt_of_le h (Nat.le_add_right p q)⟩
  else
    ⟨p + (n - p) % q, Nat.add_lt_add_left (Nat.mod_lt _ (NeZero.pos q)) p⟩

@[simp]
theorem lassoOfNat_zero (p q : ℕ) [NeZero q] :
    lassoOfNat p q 0 = lassoBase p q := by
  by_cases h : 0 < p
  · simp [lassoOfNat, lassoBase, h]
  · have hp : p = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp h)
    subst hp
    simp [lassoOfNat, lassoBase]

private theorem nat_succ_mod_lt {a q : ℕ} (hq : 0 < q) (hlt : a % q + 1 < q) :
    (a + 1) % q = a % q + 1 := by
  have h1q : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.add_mod, h1q, Nat.mod_eq_of_lt hlt]

private theorem nat_succ_mod_eq_zero {a q : ℕ} (hq : 0 < q) (hge : ¬ a % q + 1 < q) :
    (a + 1) % q = 0 := by
  have hlt : a % q < q := Nat.mod_lt a hq
  have heq : a % q + 1 = q := by omega
  have h1 : (a + 1) % q = (a % q + 1) % q := by
    by_cases hq1 : q = 1
    · subst hq1; simp
    · have h1q : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
      rw [Nat.add_mod, h1q]
  rw [h1, heq, Nat.mod_self]

theorem lassoOfNat_succ (p q : ℕ) [NeZero q] (n : ℕ) :
    lassoOfNat p q (n + 1) = lassoSucc p q (lassoOfNat p q n) := by
  have hq : 0 < q := NeZero.pos q
  by_cases hn : n < p
  · by_cases hn1 : n + 1 < p
    · have hlt : n + 1 < p + q := Nat.lt_of_lt_of_le hn1 (Nat.le_add_right p q)
      simp [lassoOfNat, lassoSucc, hn, hn1, hlt]
    · have hnp : n + 1 = p := by omega
      have hlt : n + 1 < p + q := hnp ▸ Nat.lt_add_of_pos_right hq
      ext
      simp only [lassoOfNat, lassoSucc, hn, hnp, ↓reduceDIte, Nat.sub_self, Nat.zero_mod,
        Nat.add_zero]
      simp only [Nat.lt_irrefl, ↓reduceDIte, Nat.lt_add_of_pos_right hq]
  · have hn1 : ¬ n + 1 < p := by omega
    have hsub : n + 1 - p = (n - p) + 1 := by omega
    by_cases hmod : (n - p) % q + 1 < q
    · have hlt : p + (n - p) % q + 1 < p + q := by omega
      ext
      simp [lassoOfNat, lassoSucc, hn, hn1, hlt, hsub, nat_succ_mod_lt hq hmod]
      omega
    · have hnlt : ¬ p + (n - p) % q + 1 < p + q := by omega
      ext
      simp [lassoOfNat, lassoSucc, hn, hn1, hnlt, hsub, nat_succ_mod_eq_zero hq hmod]

/-- Homomorphism `natDynSys → lassoDynSys p q` realized by `lassoOfNat p q`. -/
def natToLasso (p q : ℕ) [NeZero q] : PointedDynHom natDynSys (lassoDynSys p q) where
  toFun := lassoOfNat p q
  map_base' := lassoOfNat_zero p q
  map_step' := lassoOfNat_succ p q

theorem lassoOfNat_eq_iterate (p q : ℕ) [NeZero q] (n : ℕ) :
    lassoOfNat p q n = (lassoSucc p q)^[n] (lassoBase p q) := by
  have h := congrArg (fun φ : PointedDynHom natDynSys (lassoDynSys p q) => φ n)
    (eq_natDynHom (lassoDynSys p q) (natToLasso p q))
  simpa [natToLasso, natDynHom, lassoDynSys] using h

theorem lassoOfNat_lt {p q k : ℕ} [NeZero q] (hk : k < p + q) :
    lassoOfNat p q k = ⟨k, hk⟩ := by
  by_cases hp : k < p
  · simp [lassoOfNat, hp]
  · have hlt : k - p < q := by omega
    ext
    simp [lassoOfNat, hp, Nat.mod_eq_of_lt hlt]
    omega

theorem lassoOfNat_surjective (p q : ℕ) [NeZero q] :
    Function.Surjective (lassoOfNat p q) := by
  intro x
  exact ⟨x.1, lassoOfNat_lt x.2⟩

/-- Characteristic stem-period relation `s^{p+q}(x_0) = s^p(x_0)` on `L_{p,q}`. -/
theorem lasso_stem_period_eq (p q : ℕ) [NeZero q] :
    (lassoSucc p q)^[p + q] (lassoBase p q) = (lassoSucc p q)^[p] (lassoBase p q) := by
  rw [← lassoOfNat_eq_iterate, ← lassoOfNat_eq_iterate]
  ext
  simp [lassoOfNat]

/-- The first `p + q` iterates on `L_{p,q}` are pairwise distinct. -/
theorem lassoOfNat_injOn_init (p q : ℕ) [NeZero q] {i j : ℕ}
    (hi : i < p + q) (hj : j < p + q) (heq : lassoOfNat p q i = lassoOfNat p q j) :
    i = j := by
  rw [lassoOfNat_lt hi, lassoOfNat_lt hj] at heq
  exact congrArg Fin.val heq

/-- **FinSet Non-Initiality:** no finite dynamical system admits a homomorphism into a
    strictly larger lasso `L_{|A|, 1}`, so `μS` fails to exist inside `FinSet`. -/
theorem isEmpty_hom_of_fintype_to_succ_lasso (A : PointedDynSys.{0}) [Fintype A.Carrier] :
    IsEmpty (PointedDynHom A (lassoDynSys (Fintype.card A.Carrier) 1)) := by
  refine ⟨fun φ => ?_⟩
  have huniq : φ.comp (natDynHom A) = natToLasso (Fintype.card A.Carrier) 1 :=
    Subsingleton.elim _ _
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, hn⟩ := lassoOfNat_surjective (Fintype.card A.Carrier) 1 y
    refine ⟨natDynHom A n, ?_⟩
    have hn' : (φ.comp (natDynHom A)) n = natToLasso (Fintype.card A.Carrier) 1 n := by
      rw [huniq]
    simpa [natToLasso] using hn'.trans hn
  have hcard : Fintype.card (LassoCarrier (Fintype.card A.Carrier) 1) ≤
      Fintype.card A.Carrier :=
    Fintype.card_le_of_surjective φ hsurj
  simp [LassoCarrier] at hcard

/-- Coherent transition homomorphism `L_{p,q} ↠ L_{p',q'}` whenever `p' ≤ p` and `q' ∣ q`. -/
def lassoTransition {p' p q' q : ℕ} [NeZero q'] [NeZero q]
    (hp : p' ≤ p) (hq : q' ∣ q) :
    PointedDynHom (lassoDynSys p q) (lassoDynSys p' q') where
  toFun x := lassoOfNat p' q' x.1
  map_base' := lassoOfNat_zero p' q'
  map_step' x := by
    change lassoOfNat p' q' (lassoSucc p q x).1 = lassoSucc p' q' (lassoOfNat p' q' x.1)
    by_cases hlt : x.1 + 1 < p + q
    · simp [lassoSucc, hlt, lassoOfNat_succ]
    · have hxend : x.1 + 1 = p + q := by
        have := x.2
        omega
      have hsub : lassoSucc p q x = ⟨p, Nat.lt_add_of_pos_right (NeZero.pos q)⟩ := by
        simp [lassoSucc, hlt]
      rw [hsub, ← lassoOfNat_succ p' q' x.1, hxend]
      dsimp only
      have hnp : ¬ p < p' := Nat.not_lt.mpr hp
      have hnpq : ¬ p + q < p' := by omega
      obtain ⟨k, rfl⟩ := hq
      have hsplit : p + q' * k - p' = (p - p') + q' * k := by omega
      ext
      simp [lassoOfNat, hnp, hnpq, hsplit, Nat.add_mul_mod_self_left]

theorem lassoTransition_surjective {p' p q' q : ℕ} [NeZero q'] [NeZero q]
    (hp : p' ≤ p) (hq : q' ∣ q) :
    Function.Surjective (lassoTransition hp hq) := by
  intro y
  obtain ⟨k, hk⟩ := y
  have hlt : k < p + q := by
    have hq_pos : 0 < q := NeZero.pos q
    have hle : q' ≤ q := Nat.le_of_dvd hq_pos hq
    omega
  refine ⟨⟨k, hlt⟩, ?_⟩
  change lassoOfNat p' q' k = ⟨k, hk⟩
  exact lassoOfNat_lt hk

@[simp]
theorem lassoTransition_id (p q : ℕ) [NeZero q] :
    lassoTransition (le_refl p) (dvd_refl q) = PointedDynHom.id (lassoDynSys p q) := by
  apply PointedDynHom.ext
  funext x
  exact lassoOfNat_lt x.2

theorem lassoTransition_comp {p'' p' p q'' q' q : ℕ} [NeZero q''] [NeZero q'] [NeZero q]
    (hp₁ : p' ≤ p) (hq₁ : q' ∣ q) (hp₂ : p'' ≤ p') (hq₂ : q'' ∣ q') :
    (lassoTransition hp₂ hq₂).comp (lassoTransition hp₁ hq₁) =
      lassoTransition (hp₂.trans hp₁) (hq₂.trans hq₁) := by
  apply PointedDynHom.ext
  funext x
  have huniq :
      ((lassoTransition hp₂ hq₂).comp (lassoTransition hp₁ hq₁)).comp (natToLasso p q) =
        (lassoTransition (hp₂.trans hp₁) (hq₂.trans hq₁)).comp (natToLasso p q) :=
    Subsingleton.elim _ _
  have hx := congrArg (fun φ : PointedDynHom natDynSys (lassoDynSys p'' q'') => φ x.1) huniq
  have hlt : natToLasso p q x.1 = x := lassoOfNat_lt x.2
  change (lassoTransition hp₂ hq₂) ((lassoTransition hp₁ hq₁) (natToLasso p q x.1)) =
      (lassoTransition (hp₂.trans hp₁) (hq₂.trans hq₁)) (natToLasso p q x.1) at hx
  rw [hlt] at hx
  exact hx

/-- Cyclic ring `ZMod q` viewed as a pointed dynamical system `(ZMod q, 0, (+ 1))`. -/
@[reducible] def zmodDynSys (q : ℕ) [NeZero q] : PointedDynSys.{0} where
  Carrier := ZMod q
  base := 0
  step z := z + 1

/-- Explicit bijection `L_{0,q} ≃ ZMod q` identifying the stem-free lasso with `ℤ/qℤ`. -/
def lassoZeroEquivZMod (q : ℕ) [NeZero q] : LassoCarrier 0 q ≃ ZMod q where
  toFun x := (x.1 : ZMod q)
  invFun z := ⟨z.val, by simpa using ZMod.val_lt z⟩
  left_inv x := by
    ext
    dsimp only
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by simpa using x.2)]
  right_inv z := by
    simp

/-- Forward isomorphism `L_{0,q} → zmodDynSys q` of pointed dynamical systems. -/
def lassoZeroHomZMod (q : ℕ) [NeZero q] :
    PointedDynHom (lassoDynSys 0 q) (zmodDynSys q) where
  toFun := lassoZeroEquivZMod q
  map_base' := by simp [lassoZeroEquivZMod, lassoBase]
  map_step' x := by
    change ((lassoSucc 0 q x).1 : ZMod q) = (x.1 : ZMod q) + 1
    by_cases hlt : x.1 + 1 < q
    · have hlt' : x.1 + 1 < 0 + q := by omega
      simp only [lassoSucc, dif_pos hlt', Nat.cast_add, Nat.cast_one]
    · have hxq : x.1 + 1 = q := by
        have := x.2
        omega
      have hnlt' : ¬ x.1 + 1 < 0 + q := by omega
      simp only [lassoSucc, dif_neg hnlt']
      have hcast : ((x.1 + 1 : ℕ) : ZMod q) = 0 := by
        rw [hxq, ZMod.natCast_self]
      calc
        ((0 : ℕ) : ZMod q) = ((x.1 + 1 : ℕ) : ZMod q) := by simpa using hcast.symm
        _ = (x.1 : ZMod q) + 1 := by simp [Nat.cast_add]

/-- Transition maps on `p = 0` lassos commute with `ZMod.castHom` on `ℤ/qℤ`. -/
theorem lassoTransition_zero_comm_castHom {q' q : ℕ} [NeZero q'] [NeZero q] (hq : q' ∣ q)
    (x : LassoCarrier 0 q) :
    lassoZeroEquivZMod q' (lassoTransition (le_refl 0) hq x) =
      ZMod.castHom hq (ZMod q') (lassoZeroEquivZMod q x) := by
  have hx : (lassoOfNat 0 q' x.1).1 = x.1 % q' := by
    simp [lassoOfNat]
  change ((lassoOfNat 0 q' x.1).1 : ZMod q') = ZMod.castHom hq (ZMod q') (x.1 : ZMod q)
  rw [hx, ZMod.natCast_mod, map_natCast]

/-- Subring of coherent profinite integer families `ℤ̂ = lim_{q ≥ 1} ZMod q`. -/
def zHatSubring : Subring (∀ q : {q : ℕ // 0 < q}, ZMod q.1) where
  carrier := {f | ∀ {q' q : {q : ℕ // 0 < q}} (h : q'.1 ∣ q.1),
    ZMod.castHom h (ZMod q'.1) (f q) = f q'}
  mul_mem' {a b} ha hb {q' q} h := by
    change ZMod.castHom h (ZMod q'.1) (a q * b q) = a q' * b q'
    rw [map_mul, ha h, hb h]
  one_mem' {q' q} h := by
    change ZMod.castHom h (ZMod q'.1) 1 = 1
    rw [map_one]
  add_mem' {a b} ha hb {q' q} h := by
    change ZMod.castHom h (ZMod q'.1) (a q + b q) = a q' + b q'
    rw [map_add, ha h, hb h]
  zero_mem' {q' q} h := by
    change ZMod.castHom h (ZMod q'.1) 0 = 0
    rw [map_zero]
  neg_mem' {a} ha {q' q} h := by
    change ZMod.castHom h (ZMod q'.1) (-a q) = -a q'
    rw [map_neg, ha h]

/-- The ring of profinite integers `ℤ̂ = lim_{q ≥ 1} ZMod q`. -/
abbrev ProfiniteZHat : Type := zHatSubring

theorem zHat_coh (z : ProfiniteZHat) {q' q : {q : ℕ // 0 < q}} (h : q'.1 ∣ q.1) :
    ZMod.castHom h (ZMod q'.1) (z.1 q) = z.1 q' :=
  @Subtype.property _ _ z q' q h

/-- The profinite lasso inverse limit `ℕ̂_lasso = lim_{(p,q)} L_{p,q}`. -/
@[ext]
structure ProfiniteLasso where
  val : ∀ (p q : ℕ) [NeZero q], LassoCarrier p q
  coh : ∀ {p' p q' q : ℕ} [NeZero q'] [NeZero q] (hp : p' ≤ p) (hq : q' ∣ q),
    lassoTransition hp hq (val p q) = val p' q'

/-- Canonical natural-number embedding `ℕ → ProfiniteLasso`. -/
def natToProfiniteLasso (n : ℕ) : ProfiniteLasso where
  val p q _ := lassoOfNat p q n
  coh hp hq := by
    have huniq := congrArg (fun φ : PointedDynHom natDynSys (lassoDynSys _ _) => φ n)
      (Subsingleton.elim ((lassoTransition hp hq).comp (natToLasso _ _)) (natToLasso _ _))
    simpa [natToLasso] using huniq

theorem natToProfiniteLasso_injective : Function.Injective natToProfiniteLasso := by
  intro m n h
  have h0 := congrArg (fun x : ProfiniteLasso => (x.val (max m n + 1) 1).1) h
  have hm : lassoOfNat (max m n + 1) 1 m = ⟨m, by omega⟩ := lassoOfNat_lt (by omega)
  have hn : lassoOfNat (max m n + 1) 1 n = ⟨n, by omega⟩ := lassoOfNat_lt (by omega)
  simpa [natToProfiniteLasso, hm, hn] using h0

instance instInfiniteProfiniteLasso : Infinite ProfiniteLasso :=
  Infinite.of_injective natToProfiniteLasso natToProfiniteLasso_injective

/-- Canonical periodic quotient projection `ℕ̂_lasso → ℤ̂` (evaluating along the `p = 0` slice). -/
def profiniteLassoToZHat (x : ProfiniteLasso) : ProfiniteZHat :=
  ⟨fun q => haveI : NeZero q.1 := ⟨q.2.ne'⟩; lassoZeroEquivZMod q.1 (x.val 0 q.1),
   fun {q' q} h => by
     haveI : NeZero q'.1 := ⟨q'.2.ne'⟩
     haveI : NeZero q.1 := ⟨q.2.ne'⟩
     rw [← lassoTransition_zero_comm_castHom h (x.val 0 q.1)]
     exact congrArg (lassoZeroEquivZMod q'.1) (x.coh (le_refl 0) h)⟩

private def zHatSectionVal (z : ProfiniteZHat) (p q : ℕ) [NeZero q] : LassoCarrier p q :=
  ⟨p + (z.1 ⟨q, NeZero.pos q⟩ - (p : ZMod q)).val,
    Nat.add_lt_add_left (ZMod.val_lt _) p⟩

private theorem zHatSection_coh (z : ProfiniteZHat) {p' p q' q : ℕ} [NeZero q'] [NeZero q]
    (hp : p' ≤ p) (hq : q' ∣ q) :
    lassoTransition hp hq (zHatSectionVal z p q) = zHatSectionVal z p' q' := by
  let qp : {n : ℕ // 0 < n} := ⟨q, NeZero.pos q⟩
  let q'p : {n : ℕ // 0 < n} := ⟨q', NeZero.pos q'⟩
  have hcast_z : ZMod.castHom hq (ZMod q') (z.1 qp) = z.1 q'p :=
    zHat_coh z (q' := q'p) (q := qp) hq
  have hle : ¬ (zHatSectionVal z p q).1 < p' := by
    simp [zHatSectionVal]
    omega
  have hsub_val : (p + (z.1 qp - (p : ZMod q)).val - p' : ℕ) =
      (p - p') + (z.1 qp - (p : ZMod q)).val := by omega
  have hmod_cast : (((zHatSectionVal z p q).1 - p') % q') =
      (((zHatSectionVal z p q).1 - p' : ℕ) : ZMod q').val := by
    rw [ZMod.val_natCast]
  have hcast_eq : (((zHatSectionVal z p q).1 - p' : ℕ) : ZMod q') = z.1 q'p - (p' : ZMod q') := by
    change (((p + (z.1 qp - (p : ZMod q)).val - p' : ℕ) : ZMod q')) = z.1 q'p - (p' : ZMod q')
    rw [hsub_val, Nat.cast_add, Nat.cast_sub hp]
    have hrem : ((z.1 qp - (p : ZMod q)).val : ZMod q') = z.1 q'p - (p : ZMod q') := by
      calc
        ((z.1 qp - (p : ZMod q)).val : ZMod q')
            = ZMod.castHom hq (ZMod q') ((z.1 qp - (p : ZMod q)).val : ZMod q) := by
                rw [map_natCast]
        _ = ZMod.castHom hq (ZMod q') (z.1 qp - (p : ZMod q)) := by
              rw [ZMod.natCast_zmod_val]
        _ = ZMod.castHom hq (ZMod q') (z.1 qp) - ZMod.castHom hq (ZMod q') (p : ZMod q) := by
              rw [map_sub]
        _ = z.1 q'p - (p : ZMod q') := by rw [hcast_z, map_natCast]
    rw [hrem, add_comm, sub_add_sub_cancel]
  ext
  change (lassoOfNat p' q' (zHatSectionVal z p q).1).1 =
      p' + (z.1 q'p - (p' : ZMod q')).val
  rw [lassoOfNat, dif_neg hle]
  dsimp only
  rw [hmod_cast, hcast_eq]

/-- Canonical infinite-stem lift `ℤ̂ → ℕ̂_lasso` witnessing non-natural profinite points. -/
def zHatToProfiniteLasso (z : ProfiniteZHat) : ProfiniteLasso where
  val := zHatSectionVal z
  coh := zHatSection_coh z

theorem profiniteLassoToZHat_zHatToProfiniteLasso (z : ProfiniteZHat) :
    profiniteLassoToZHat (zHatToProfiniteLasso z) = z := by
  apply Subtype.ext
  funext q
  haveI : NeZero q.1 := ⟨q.2.ne'⟩
  have heq : (z.1 q).val = (zHatSectionVal z 0 q.1).1 := by
    simp [zHatSectionVal]
  simp only [profiniteLassoToZHat, zHatToProfiniteLasso, lassoZeroEquivZMod]
  change (↑(zHatSectionVal z 0 q.1).1 : ZMod q.1) = z.1 q
  rw [← heq, ZMod.natCast_zmod_val]

/-- Every profinite integer lifts to the profinite lasso inverse limit (`ℕ̂_lasso ↠ ℤ̂`). -/
theorem profiniteLassoToZHat_surjective :
    Function.Surjective profiniteLassoToZHat :=
  fun z => ⟨zHatToProfiniteLasso z, profiniteLassoToZHat_zHatToProfiniteLasso z⟩

/-- The profinite integer `-1` lifts via `zHatToProfiniteLasso (-1)` to an element of `ℕ̂_lasso`
    outside `range natToProfiniteLasso`, witnessing proper extension `ℕ ⊊ ℕ̂_lasso`. -/
theorem zHatToProfiniteLasso_neg_one_not_mem_range_nat :
    zHatToProfiniteLasso (-1 : ProfiniteZHat) ∉ Set.range natToProfiniteLasso := by
  rintro ⟨n, hn⟩
  have h1 := congrArg (fun x : ProfiniteLasso => x.val (n + 2) 1) hn
  have hm : lassoOfNat (n + 2) 1 n = ⟨n, by omega⟩ := lassoOfNat_lt (by omega)
  have hsec : (zHatToProfiniteLasso (-1 : ProfiniteZHat)).val (n + 2) 1 =
      ⟨n + 2, by omega⟩ := by
    apply Fin.ext
    change (n + 2) + ((-1 : ProfiniteZHat).1 ⟨1, Nat.one_pos⟩ - ((n + 2 : ℕ) : ZMod 1)).val =
      n + 2
    have hzero : ((-1 : ProfiniteZHat).1 ⟨1, Nat.one_pos⟩ - ((n + 2 : ℕ) : ZMod 1)).val = 0 := by
      haveI : Subsingleton (ZMod 1) := inferInstance
      rw [Subsingleton.elim ((-1 : ProfiniteZHat).1 ⟨1, Nat.one_pos⟩ - ((n + 2 : ℕ) : ZMod 1)) 0,
        ZMod.val_zero]
    omega
  change lassoOfNat (n + 2) 1 n = (zHatToProfiniteLasso (-1 : ProfiniteZHat)).val (n + 2) 1 at h1
  rw [hm, hsec] at h1
  have hval : n = n + 2 := congrArg Fin.val h1
  omega

/-! ## Section 2: Dedekind / Pigeonhole Residuum and the Nominal Crossing Point (`𝔸 = ℕ`) -/

/-- The Dedekind residuum `Mono(X, X) \ Iso(X, X)` of injective non-bijective endomorphisms. -/
def DedekindResiduum (X : Type*) : Set (X → X) :=
  {f | Function.Injective f ∧ ¬ Function.Bijective f}

/-- **FinSet Pigeonhole:** in any finite type, injective endomorphisms are bijective. -/
theorem fintype_injective_iff_bijective {X : Type*} [Fintype X] (f : X → X) :
    Function.Injective f ↔ Function.Bijective f :=
  ⟨fun h => (Fintype.bijective_iff_injective_and_card f).mpr ⟨h, rfl⟩,
   fun h => h.injective⟩

/-- Inside `mathbf{FinSet}`, the Dedekind residuum vanishes identically. -/
theorem dedekindResiduum_eq_empty_of_fintype (X : Type*) [Fintype X] :
    DedekindResiduum X = ∅ := by
  ext f
  simp [DedekindResiduum, fintype_injective_iff_bijective f]

/-- `Nat.succ` witnesses non-emptiness of `DedekindResiduum ℕ`. -/
theorem nat_succ_mem_dedekindResiduum : Nat.succ ∈ DedekindResiduum ℕ := by
  refine ⟨Nat.succ_injective, fun h => ?_⟩
  obtain ⟨k, hk⟩ := h.surjective 0
  exact Nat.succ_ne_zero k hk

theorem dedekindResiduum_nat_nonempty : (DedekindResiduum ℕ).Nonempty :=
  ⟨Nat.succ, nat_succ_mem_dedekindResiduum⟩

/-- Finite support `S ⊆ 𝔸 = ℕ` for an endomorphism `f : ℕ → ℕ` under `Equiv.Perm ℕ`
    conjugation: every permutation fixing `S` pointwise commutes with `f`. -/
def SupportsMap (S : Finset ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ σ : Equiv.Perm ℕ, (∀ a ∈ S, σ a = a) → ∀ x : ℕ, σ (f x) = f (σ x)

/-- `f : ℕ → ℕ` is a morphism in `mathbf{Nom}` on the atom object `𝔸` iff it is supported
    by some finite set of atoms `S : Finset ℕ`. -/
def HasFiniteSupportMap (f : ℕ → ℕ) : Prop :=
  ∃ S : Finset ℕ, SupportsMap S f

/-- The Dedekind residuum inside `mathbf{Nom}` on the Kuratowski-infinite atom object `𝔸`. -/
def NominalDedekindResiduum : Set (ℕ → ℕ) :=
  {f | HasFiniteSupportMap f ∧ Function.Injective f ∧ ¬ Function.Bijective f}

private theorem outside_mem_or_fixed_of_supportsMap {S : Finset ℕ} {f : ℕ → ℕ}
    (hS : SupportsMap S f) (x : ℕ) :
    f x ∈ S ∨ f x = x := by
  by_contra hcon
  push_neg at hcon
  rcases hcon with ⟨hfxS, hfxne⟩
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (insert x (insert (f x) S))
  have hzx : z ≠ x := by
    intro h
    rw [h] at hz
    exact hz (Finset.mem_insert_self x _)
  have hzfx : z ≠ f x := by
    intro h
    rw [h] at hz
    exact hz (Finset.mem_insert_of_mem (Finset.mem_insert_self (f x) _))
  have hzS : z ∉ S :=
    fun h => hz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have hfixS : ∀ a ∈ S, Equiv.swap (f x) z a = a := by
    intro a haS
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hfxS (h ▸ haS)) (fun h => hzS (h ▸ haS))
  have hfixx : Equiv.swap (f x) z x = x :=
    Equiv.swap_apply_of_ne_of_ne hfxne.symm hzx.symm
  have hcomm := hS (Equiv.swap (f x) z) hfixS x
  rw [Equiv.swap_apply_left, hfixx] at hcomm
  exact hzfx hcomm

private theorem outside_fixed_of_supportsMap_of_injective {S : Finset ℕ} {f : ℕ → ℕ}
    (hS : SupportsMap S f) (hinj : Function.Injective f) {x : ℕ} (hx : x ∉ S) :
    f x = x := by
  rcases outside_mem_or_fixed_of_supportsMap hS x with hfxS | hfix
  · obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (insert x S)
    have hyx : y ≠ x := by
      intro h
      rw [h] at hy
      exact hy (Finset.mem_insert_self x _)
    have hyS : y ∉ S := fun h => hy (Finset.mem_insert_of_mem h)
    have hfixS : ∀ a ∈ S, Equiv.swap x y a = a := by
      intro a haS
      exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ haS)) (fun h => hyS (h ▸ haS))
    have hcomm := hS (Equiv.swap x y) hfixS x
    rw [hfixS (f x) hfxS, Equiv.swap_apply_left] at hcomm
    exact False.elim (hyx.symm (hinj hcomm))
  · exact hfix

private theorem mem_support_maps_into_of_injective {S : Finset ℕ} {f : ℕ → ℕ}
    (hS : SupportsMap S f) (hinj : Function.Injective f) {a : ℕ} (ha : a ∈ S) :
    f a ∈ S := by
  by_contra hfa
  have hfix := outside_fixed_of_supportsMap_of_injective hS hinj hfa
  have heq : f a = a := hinj hfix
  rw [heq] at hfa
  exact hfa ha

/-- Any finitely supported injective map `f : ℕ → ℕ` fixes the complement of `S` and restricts
    to a bijection on `S`, hence is globally bijective. -/
theorem bijective_of_supportsMap_of_injective {S : Finset ℕ} {f : ℕ → ℕ}
    (hS : SupportsMap S f) (hinj : Function.Injective f) :
    Function.Bijective f := by
  refine ⟨hinj, fun y => ?_⟩
  by_cases hyS : y ∈ S
  · let fS : S → S := fun a => ⟨f a.1, mem_support_maps_into_of_injective hS hinj a.2⟩
    have hfS_inj : Function.Injective fS := by
      intro a b hab
      ext
      exact hinj (congrArg Subtype.val hab)
    have hfS_bij : Function.Bijective fS :=
      (fintype_injective_iff_bijective fS).mp hfS_inj
    obtain ⟨a, ha⟩ := hfS_bij.surjective ⟨y, hyS⟩
    exact ⟨a.1, congrArg Subtype.val ha⟩
  · exact ⟨y, outside_fixed_of_supportsMap_of_injective hS hinj hyS⟩

/-- **Nominal Crossing Point:** for every morphism `f : 𝔸 → 𝔸` in `mathbf{Nom}`,
    injectivity still forces bijectivity despite `Infinite 𝔸`. -/
theorem nominal_injective_iff_bijective {f : ℕ → ℕ} (hf : HasFiniteSupportMap f) :
    Function.Injective f ↔ Function.Bijective f := by
  rcases hf with ⟨S, hS⟩
  exact ⟨fun hinj => bijective_of_supportsMap_of_injective hS hinj, fun h => h.injective⟩

/-- Inside `mathbf{Nom}`, `Mono(𝔸, 𝔸) = Iso(𝔸, 𝔸)` so `Res_Ded(𝔸) = ∅`, cleanly isolating
    `Inf ∧ ¬ AC_ω`. -/
theorem nominalDedekindResiduum_eq_empty : NominalDedekindResiduum = ∅ := by
  ext f
  simp only [NominalDedekindResiduum, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_and]
  intro hf hinj
  exact not_not.mpr ((nominal_injective_iff_bijective hf).mp hinj)

/-- Consequently `Nat.succ` cannot have finite support under `Equiv.Perm ℕ`. -/
theorem not_hasFiniteSupportMap_nat_succ : ¬ HasFiniteSupportMap Nat.succ := by
  intro hfs
  exact absurd ((nominal_injective_iff_bijective hfs).mp Nat.succ_injective)
    nat_succ_mem_dedekindResiduum.2

/-! ## Section 3: Biproduct-Tail Cokernel (`∏_I A / ⨁_I A`) -/

/-- Canonical embedding of finitely supported functions `(I →₀ A)` into arbitrary
    functions `(I → A)`. -/
def finsuppToPiAddHom (I A : Type*) [AddCommMonoid A] : (I →₀ A) →+ (I → A) where
  toFun := (⇑)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem finsuppToPiAddHom_apply {I A : Type*} [AddCommMonoid A] (f : I →₀ A) (i : I) :
    finsuppToPiAddHom I A f i = f i := rfl

theorem finsuppToPiAddHom_injective (I A : Type*) [AddCommMonoid A] :
    Function.Injective (finsuppToPiAddHom I A) :=
  fun _ _ h => DFunLike.coe_injective h

/-- The asymptotic biproduct-tail cokernel `∏_I A / ⨁_I A`. -/
abbrev TailCokernel (I A : Type*) [AddCommGroup A] : Type _ :=
  (I → A) ⧸ (finsuppToPiAddHom I A).range

/-- Additive equivalence `(I →₀ A) ≃+ (I → A)` whenever `I` is finite (`mathbf{FinSet}`). -/
noncomputable def finsuppEquivPiOfFintype (I A : Type*) [Fintype I] [AddCommMonoid A] :
    (I →₀ A) ≃+ (I → A) where
  toEquiv := Finsupp.equivFunOnFinite
  map_add' _ _ := rfl

theorem finsuppToPiAddHom_range_eq_top_of_fintype (I A : Type*) [Fintype I] [AddCommGroup A] :
    (finsuppToPiAddHom I A).range = ⊤ := by
  rw [eq_top_iff]
  intro f _
  refine ⟨(finsuppEquivPiOfFintype I A).symm f, ?_⟩
  ext i
  exact congrFun ((finsuppEquivPiOfFintype I A).apply_symm_apply f) i

/-- **FinSet Biproduct Collapse:** for any finite index `I`, the tail cokernel vanishes. -/
theorem subsingleton_tailCokernel_of_fintype (I A : Type*) [Fintype I] [AddCommGroup A] :
    Subsingleton (TailCokernel I A) :=
  QuotientAddGroup.subsingleton_iff.mpr (finsuppToPiAddHom_range_eq_top_of_fintype I A)

/-- No nonzero constant sequence `ℕ → A` is finitely supported. -/
theorem const_notMem_finsuppToPiAddHom_range {A : Type*} [AddCommGroup A] {a : A} (ha : a ≠ 0) :
    (fun _ : ℕ => a) ∉ (finsuppToPiAddHom ℕ A).range := by
  rintro ⟨f, hf⟩
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset f.support
  have hfn : f n = 0 := Finsupp.notMem_support_iff.mp hn
  have hev := congrFun hf n
  simp [hfn] at hev
  exact ha hev.symm

/-- **Infinite Biproduct-Tail Residuum:** over `ℕ` with nontrivial coefficients `A`,
    `∏_ℕ A / ⨁_ℕ A` is nontrivial. -/
theorem nontrivial_tailCokernel_nat (A : Type*) [AddCommGroup A] [Nontrivial A] :
    Nontrivial (TailCokernel ℕ A) := by
  rw [QuotientAddGroup.nontrivial_iff]
  intro htop
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have hmem : (fun _ : ℕ => a) ∈ (finsuppToPiAddHom ℕ A).range := by
    rw [htop]
    trivial
  exact const_notMem_finsuppToPiAddHom_range ha hmem

/-! ## Section 4: Unified Chapter 1 §1.6 Infinity Residua Summary -/

/-- **Chapter 1 §1.6 Unified Theorem (Pure Axis III Infinity Residua):**
    Simultaneously certifies inside `FinSet` vs. `NNO`-doctrines and `Nom`:
    1. External initiality of `natDynSys` vs. `FinSet` non-initiality against `L_{|A|,1}`, with
       surjective profinite projection `ℕ̂_lasso ↠ ℤ̂` and `ProfiniteLasso` strictly extending `ℕ`;
    2. `FinSet` Dedekind residuum triviality (`DedekindResiduum X = ∅`) vs. `ℕ` non-emptiness;
    3. The `Nom` crossing point (`NominalDedekindResiduum = ∅` despite `Infinite ℕ`, isolating
       `Inf ∧ ¬ AC_ω`);
    4. Finitary biproduct collapse `Subsingleton (TailCokernel I A)` vs. `Nontrivial (TailCokernel ℕ A)`. -/
theorem chapter1_pure_infinity_residua_summary :
    (∀ A : PointedDynSys.{0}, Nonempty (Unique (PointedDynHom natDynSys A))) ∧
    (∀ (A : PointedDynSys.{0}) [Fintype A.Carrier],
      IsEmpty (PointedDynHom A (lassoDynSys (Fintype.card A.Carrier) 1))) ∧
    (Function.Surjective profiniteLassoToZHat ∧
      zHatToProfiniteLasso (-1 : ProfiniteZHat) ∉ Set.range natToProfiniteLasso) ∧
    (∀ (X : Type) [Fintype X], DedekindResiduum X = ∅) ∧
    (DedekindResiduum ℕ).Nonempty ∧
    (NominalDedekindResiduum = ∅ ∧ Infinite ℕ) ∧
    (∀ (I A : Type) [Fintype I] [AddCommGroup A], Subsingleton (TailCokernel I A)) ∧
    (∀ (A : Type) [AddCommGroup A] [Nontrivial A], Nontrivial (TailCokernel ℕ A)) := by
  refine ⟨fun A => ⟨instUniqueNatDynHom A⟩, fun A _ => isEmpty_hom_of_fintype_to_succ_lasso A,
    ⟨profiniteLassoToZHat_surjective, zHatToProfiniteLasso_neg_one_not_mem_range_nat⟩,
    fun X _ => dedekindResiduum_eq_empty_of_fintype X, dedekindResiduum_nat_nonempty,
    ⟨nominalDedekindResiduum_eq_empty, inferInstance⟩,
    fun I A _ _ => subsingleton_tailCokernel_of_fintype I A,
    fun A _ _ => nontrivial_tailCokernel_nat A⟩

/-! ## Section 5: Mandatory 4-Layer Definition Check Gate (`namespace Checks`) -/

namespace Checks

/-! ### Layer 1: Carrier Inhabitation (`Nontrivial` Instances) -/

example : Nontrivial (LassoCarrier 1 2) := ⟨⟨0, 1, by decide⟩⟩

example : Nontrivial ProfiniteLasso :=
  ⟨⟨natToProfiniteLasso 0, natToProfiniteLasso 1,
    natToProfiniteLasso_injective.ne (by decide)⟩⟩

theorem inf_nontrivial_zHat_minus_one : (0 : ProfiniteZHat) ≠ (-1 : ProfiniteZHat) := by
  intro h
  have h2 := congrArg (fun z : ProfiniteZHat => z.1 ⟨2, by decide⟩) h
  revert h2
  decide

example : Nontrivial ProfiniteZHat := ⟨⟨0, -1, inf_nontrivial_zHat_minus_one⟩⟩

example : Nontrivial (TailCokernel ℕ (ZMod 2)) :=
  nontrivial_tailCokernel_nat (ZMod 2)

/-! ### Layer 2: Bidirectional Separation (Positive & Negative Witnesses) -/

theorem inf_positive_nat_succ_dedekind : Nat.succ ∈ DedekindResiduum ℕ :=
  nat_succ_mem_dedekindResiduum

theorem inf_negative_fin_four_dedekind : DedekindResiduum (Fin 4) = ∅ :=
  dedekindResiduum_eq_empty_of_fintype (Fin 4)

theorem inf_positive_swap_hasFiniteSupport : HasFiniteSupportMap (Equiv.swap 0 1) := by
  refine ⟨{0, 1}, fun σ hfix x => ?_⟩
  by_cases hx0 : x = 0
  · subst hx0
    rw [Equiv.swap_apply_left, hfix 0 (by decide), Equiv.swap_apply_left, hfix 1 (by decide)]
  · by_cases hx1 : x = 1
    · subst hx1
      rw [Equiv.swap_apply_right, hfix 1 (by decide), Equiv.swap_apply_right, hfix 0 (by decide)]
    · rw [Equiv.swap_apply_of_ne_of_ne hx0 hx1]
      have h0 : σ x ≠ 0 := fun h => hx0 (σ.injective (h.trans (hfix 0 (by decide)).symm))
      have h1 : σ x ≠ 1 := fun h => hx1 (σ.injective (h.trans (hfix 1 (by decide)).symm))
      rw [Equiv.swap_apply_of_ne_of_ne h0 h1]

theorem inf_negative_nat_succ_not_hasFiniteSupport : ¬ HasFiniteSupportMap Nat.succ :=
  not_hasFiniteSupportMap_nat_succ

theorem inf_positive_unique_natDynHom_lasso :
    Nonempty (Unique (PointedDynHom natDynSys (lassoDynSys 2 3))) :=
  ⟨instUniqueNatDynHom _⟩

theorem inf_negative_fintype_hom_empty :
    IsEmpty (PointedDynHom (lassoDynSys 1 1) (lassoDynSys 2 1)) :=
  isEmpty_hom_of_fintype_to_succ_lasso (lassoDynSys 1 1)

theorem inf_subsingleton_finite_tailCokernel :
    Subsingleton (TailCokernel (Fin 4) (ZMod 2)) :=
  subsingleton_tailCokernel_of_fintype (Fin 4) (ZMod 2)

theorem inf_nontrivial_nat_tailCokernel :
    Nontrivial (TailCokernel ℕ (ZMod 2)) :=
  nontrivial_tailCokernel_nat (ZMod 2)

/-! ### Layer 3: `mathlib4` Projections & Derived Sanity Lemmas -/

example : CategoryTheory.Category PointedDynSys.{0} := inferInstance
example : CommRing ProfiniteZHat := inferInstance
example : AddCommGroup (TailCokernel ℕ ℤ) := inferInstance

theorem inf_lasso_zero_cycle_cast_check :
    lassoTransition (le_refl 0) (by decide : (2 : ℕ) ∣ 4) ⟨3, by decide⟩ = ⟨1, by decide⟩ := by
  apply Fin.ext
  decide

theorem inf_lasso_stem_period_check :
    (lassoSucc 2 3)^[5] (lassoBase 2 3) = (lassoSucc 2 3)^[2] (lassoBase 2 3) :=
  lasso_stem_period_eq 2 3

theorem inf_lasso_transition_comp_check :
    ((lassoTransition (by decide : 1 ≤ 2) (by decide : (2 : ℕ) ∣ 4)).comp
      (lassoTransition (by decide : 2 ≤ 3) (by decide : (4 : ℕ) ∣ 8))) =
      lassoTransition (by decide : 1 ≤ 3) (by decide : (2 : ℕ) ∣ 8) :=
  lassoTransition_comp (by decide) (by decide) (by decide) (by decide)

theorem inf_finite_finsupp_equiv_card_check :
    (finsuppEquivPiOfFintype (Fin 3) (ZMod 2)).symm (fun i => (i.1 : ZMod 2)) 2 = 0 := by
  simp [finsuppEquivPiOfFintype]
  decide

/-! ### Layer 4: Kernel Axiom Gate (`#guard_msgs in #print axioms`) -/

section KernelAxiomGate

/-- info: 'HomotopyCRM.eq_natDynHom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.eq_natDynHom

/-- info: 'HomotopyCRM.lassoOfNat_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.lassoOfNat_succ

/-- info: 'HomotopyCRM.lassoOfNat_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.lassoOfNat_surjective

/-- info: 'HomotopyCRM.lasso_stem_period_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.lasso_stem_period_eq

/-- info: 'HomotopyCRM.isEmpty_hom_of_fintype_to_succ_lasso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.isEmpty_hom_of_fintype_to_succ_lasso

/-- info: 'HomotopyCRM.lassoTransition_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.lassoTransition_surjective

/-- info: 'HomotopyCRM.lassoTransition_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.lassoTransition_comp

/-- info: 'HomotopyCRM.lassoTransition_zero_comm_castHom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.lassoTransition_zero_comm_castHom

/-- info: 'HomotopyCRM.natToProfiniteLasso_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.natToProfiniteLasso_injective

/-- info: 'HomotopyCRM.profiniteLassoToZHat_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.profiniteLassoToZHat_surjective

/-- info: 'HomotopyCRM.zHatToProfiniteLasso_neg_one_not_mem_range_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.zHatToProfiniteLasso_neg_one_not_mem_range_nat

/-- info: 'HomotopyCRM.fintype_injective_iff_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.fintype_injective_iff_bijective

/-- info: 'HomotopyCRM.dedekindResiduum_eq_empty_of_fintype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.dedekindResiduum_eq_empty_of_fintype

/-- info: 'HomotopyCRM.nat_succ_mem_dedekindResiduum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HomotopyCRM.nat_succ_mem_dedekindResiduum

/-- info: 'HomotopyCRM.bijective_of_supportsMap_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.bijective_of_supportsMap_of_injective

/-- info: 'HomotopyCRM.nominalDedekindResiduum_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.nominalDedekindResiduum_eq_empty

/-- info: 'HomotopyCRM.not_hasFiniteSupportMap_nat_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.not_hasFiniteSupportMap_nat_succ

/-- info: 'HomotopyCRM.subsingleton_tailCokernel_of_fintype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.subsingleton_tailCokernel_of_fintype

/-- info: 'HomotopyCRM.nontrivial_tailCokernel_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.nontrivial_tailCokernel_nat

/-- info: 'HomotopyCRM.chapter1_pure_infinity_residua_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.chapter1_pure_infinity_residua_summary

end KernelAxiomGate

end Checks

end HomotopyCRM
