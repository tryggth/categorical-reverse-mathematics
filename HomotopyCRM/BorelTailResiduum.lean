/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HomotopyCRM Formalization Team
-/
import HomotopyCRM.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Exotic-$\mathbb{R}^4$ $E_0$ Borel Tail Residuum and Parity Torsor (`Ch. 4, §4.5`)

This module formalizes Chapter 4, §4.5 (`sec:exotic-r4-e0`, Theorem `thm:double-solvent-r4`)
of the *Categorical Reverse Mathematics* monograph on the Cantor tail quotient
$\mathcal{Q}_{E_0} = 2^{\mathbb{N}} / E_0 = (\prod_{\mathbb{N}} \mathbb{F}_2) / (\bigoplus_{\mathbb{N}} \mathbb{F}_2)$:

1. **`ZMod 2`-Linear Exact Sequence (`Section 1`):**
   - Formalizes $0 \to (\mathbb{N} \to_0 \mathrm{ZMod}\;2) \to (\mathbb{N} \to \mathrm{ZMod}\;2)
     \xrightarrow{q} \mathcal{Q}_{E_0} \to 0$ as `Module (ZMod 2)` spaces over the prime field
     `ZMod 2`, characterizes tail equivalence `E0Rel x y` (`x - y ∈ E0Submodule ↔ E0Rel x y`),
     and proves `Nontrivial E0Quotient` via `constOne`.

2. **Right Solvent — Classical $\mathsf{ZFC}$ Splitting (`Section 2`):**
   - Proves via `Submodule.exists_isCompl` (`Classical.choice`) that `e0QuotientMk` admits a
     `ZMod 2`-linear right-inverse section `s : E0Quotient →ₗ[ZMod 2] CantorSpace` and induces
     a non-canonical isomorphism `CantorSpace ≃ₗ[ZMod 2] FinFlipSpace × E0Quotient`.

3. **Polish / $T_1$ Blindness via Explicit Even-Flip Coset Density (`Section 3`):**
   - Equips `CantorSpace := ℕ → ZMod 2` with the compact Hausdorff product topology and defines
     the even-parity submodule `EvenE0Submodule := ker(finFlipParity).map finFlipIncl < E0Submodule`.
   - Constructs explicit finite-even approximants `evenApproxSeq x y N` converging to `y` in the
     product topology (`tendsto_evenApproxSeq`), proving **every** `EvenE0Submodule`-coset and
     every `E0Submodule`-coset is **dense** in Cantor space (`dense_evenE0Coset`, `dense_e0Coset`).
   - Deduces that every continuous $E_0^{\mathrm{even}}$-invariant (in particular every continuous
     $E_0$-invariant) map into a `T1Space Y` is constant ($\pi_0^{T_1}(\mathcal{Q}_{E_0}) \simeq 1$).

4. **The $E_0^{\mathrm{even}}$ Parity Torsor Dichotomy (`Section 4`):**
   - Proves without basis extension or Zorn's Lemma that **no continuous** single-flip-alternating
     parity map `χ : CantorSpace → ZMod 2` exists (`not_exists_continuous_flipAlternating`).
   - Proves via `LinearMap.exists_extend` (`Classical.choice`) that a (necessarily discontinuous)
     `ZMod 2`-linear parity functional `χ : CantorSpace →ₗ[ZMod 2] ZMod 2` exists and splits the
     nontrivial two-sheeted double cover `EvenE0Quotient ↠ E0Quotient`.

5. **Summary Theorem & Mandatory 4-Layer Definition Check Gate (`Sections 5–6`):**
   - Packages `chapter4_borel_tail_residuum_summary` and verifies all four check layers.
-/

namespace HomotopyCRM

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have hval : a.val = 0 ∨ a.val = 1 := by omega
  rcases hval with h0 | h1
  · left
    calc
      a = (a.val : ZMod 2) := (ZMod.natCast_zmod_val a).symm
      _ = 0 := by rw [h0]; rfl
  · right
    calc
      a = (a.val : ZMod 2) := (ZMod.natCast_zmod_val a).symm
      _ = 1 := by rw [h1]; rfl

/-! ## Section 1: `ZMod 2`-Linear Tail Exact Sequence -/

/-- Cantor space `2^ℕ` realized as the `ZMod 2`-vector space `ℕ → ZMod 2`. -/
abbrev CantorSpace : Type := ℕ → ZMod 2

/-- Finite-flip direct sum `⨁_ℕ 𝔽₂` realized as `(ℕ →₀ ZMod 2)`. -/
abbrev FinFlipSpace : Type := ℕ →₀ ZMod 2

/-- Canonical `ZMod 2`-linear embedding `FinFlipSpace ↪ CantorSpace`. -/
def finFlipIncl : FinFlipSpace →ₗ[ZMod 2] CantorSpace :=
  Finsupp.lcoeFun

@[simp]
theorem finFlipIncl_apply (g : FinFlipSpace) (n : ℕ) :
    finFlipIncl g n = g n := rfl

theorem finFlipIncl_injective : Function.Injective finFlipIncl :=
  fun _ _ h => DFunLike.coe_injective h

/-- The tail-equivalence submodule `E0Submodule := range finFlipIncl ⊆ CantorSpace`. -/
def E0Submodule : Submodule (ZMod 2) CantorSpace :=
  LinearMap.range finFlipIncl

/-- Tail equivalence relation `E0`: eventually equal binary sequences. -/
def E0Rel (x y : CantorSpace) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, x n = y n

theorem e0Rel_equivalence : Equivalence E0Rel where
  refl _ := ⟨0, fun _ _ => rfl⟩
  symm := fun ⟨N, h⟩ => ⟨N, fun n hn => (h n hn).symm⟩
  trans := fun ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ =>
    ⟨max N₁ N₂, fun n hn => (h₁ n (le_trans (le_max_left _ _) hn)).trans
      (h₂ n (le_trans (le_max_right _ _) hn))⟩

/-- Algebraic-relational identification: `x - y ∈ E0Submodule ↔ E0Rel x y`. -/
theorem sub_mem_E0Submodule_iff_e0Rel (x y : CantorSpace) :
    x - y ∈ E0Submodule ↔ E0Rel x y := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.support.sup id + 1, fun n hn => ?_⟩
    have hnot : n ∉ g.support := by
      intro hmem
      have hle : n ≤ g.support.sup id := Finset.le_sup (f := id) hmem
      omega
    have hgn : g n = 0 := Finsupp.notMem_support_iff.mp hnot
    have hev : finFlipIncl g n = (x - y) n := congrFun hg n
    simp only [finFlipIncl_apply, hgn, Pi.sub_apply] at hev
    exact (sub_eq_zero.mp hev.symm)
  · rintro ⟨N, hN⟩
    classical
    refine ⟨∑ i ∈ Finset.range N, Finsupp.single i (x i - y i), ?_⟩
    ext n
    rw [finFlipIncl_apply, Finsupp.finset_sum_apply, Pi.sub_apply]
    by_cases hn : n < N
    · rw [Finset.sum_eq_single n]
      · simp
      · intro i _ hne
        simp [hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr hn))
    · have hge : n ≥ N := Nat.not_lt.mp hn
      rw [hN n hge, sub_self, Finset.sum_eq_zero]
      intro i hi
      have hin : i < N := Finset.mem_range.mp hi
      have hne : i ≠ n := by omega
      simp [hne]

/-- The Cantor tail quotient `Q_{E_0} := CantorSpace / E0Submodule`. -/
abbrev E0Quotient : Type :=
  CantorSpace ⧸ E0Submodule

/-- Canonical `ZMod 2`-linear quotient epimorphism `q : CantorSpace ↠ Q_{E_0}`. -/
abbrev e0QuotientMk : CantorSpace →ₗ[ZMod 2] E0Quotient :=
  E0Submodule.mkQ

theorem e0QuotientMk_surjective : Function.Surjective e0QuotientMk :=
  E0Submodule.mkQ_surjective

theorem ker_e0QuotientMk : LinearMap.ker e0QuotientMk = E0Submodule :=
  E0Submodule.ker_mkQ

theorem exact_finFlipIncl_e0QuotientMk :
    LinearMap.range finFlipIncl = LinearMap.ker e0QuotientMk :=
  ker_e0QuotientMk.symm

/-- Constant sequence `1 : ℕ → ZMod 2` witnessing nontriviality of `Q_{E_0}`. -/
def constOne : CantorSpace := fun _ => 1

theorem constOne_notMem_E0Submodule : constOne ∉ E0Submodule := by
  rintro ⟨g, hg⟩
  have hzero : g (g.support.sup id + 1) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hle : g.support.sup id + 1 ≤ g.support.sup id := Finset.le_sup (f := id) hmem
    omega
  have hev := congrFun hg (g.support.sup id + 1)
  simp [finFlipIncl_apply, hzero, constOne] at hev

instance instNontrivialE0Quotient : Nontrivial E0Quotient where
  exists_pair_ne := by
    refine ⟨0, e0QuotientMk constOne, ?_⟩
    intro h
    have hmem : constOne ∈ E0Submodule := (Submodule.Quotient.mk_eq_zero E0Submodule).mp h.symm
    exact constOne_notMem_E0Submodule hmem

/-! ## Section 2: Right Solvent (`ZFC` Linear Section via `Classical.choice`) -/

/-- **Right Solvent (Vitali / Hamel Splitting):** over `ZMod 2`, `Classical.choice`
    (`Submodule.exists_isCompl`) provides a linear right-inverse section splitting
    `e0QuotientMk : CantorSpace ↠ E0Quotient`. -/
theorem exists_zfc_linear_section_e0Quotient :
    ∃ s : E0Quotient →ₗ[ZMod 2] CantorSpace, e0QuotientMk.comp s = LinearMap.id := by
  obtain ⟨q, hq⟩ := E0Submodule.exists_isCompl
  refine ⟨q.subtype.comp (E0Submodule.quotientEquivOfIsCompl q hq).toLinearMap, ?_⟩
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype,
    LinearMap.id_apply]
  exact Submodule.mk_quotientEquivOfIsCompl_apply E0Submodule q hq (E0Submodule.mkQ x)

/-- Consequence of the Right Solvent: `CantorSpace ≃ₗ[ZMod 2] FinFlipSpace × E0Quotient`
    non-canonically under `ZFC`. -/
theorem nonempty_linearEquiv_cantor_prod_e0Quotient :
    Nonempty (CantorSpace ≃ₗ[ZMod 2] FinFlipSpace × E0Quotient) := by
  obtain ⟨q, hq⟩ := E0Submodule.exists_isCompl
  let e₁ : FinFlipSpace ≃ₗ[ZMod 2] E0Submodule :=
    LinearEquiv.ofInjective finFlipIncl finFlipIncl_injective
  let e₂ : E0Quotient ≃ₗ[ZMod 2] q :=
    E0Submodule.quotientEquivOfIsCompl q hq
  let e₃ : (E0Submodule × q) ≃ₗ[ZMod 2] CantorSpace :=
    E0Submodule.prodEquivOfIsCompl q hq
  exact ⟨e₃.symm.trans (e₁.symm.prodCongr e₂.symm)⟩

/-! ## Section 3: Cantor Product Topology, Coset Density, & $T_1$ Blindness -/

/-- Finite-sum parity homomorphism `Σ : (ℕ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2`. -/
noncomputable def finFlipParity : FinFlipSpace →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.lsum (ZMod 2) (fun _ : ℕ => LinearMap.id)

@[simp]
theorem finFlipParity_single (n : ℕ) (a : ZMod 2) :
    finFlipParity (Finsupp.single n a) = a :=
  Finsupp.lsum_single (ZMod 2) (fun _ : ℕ => LinearMap.id) n a

/-- Even-parity finite flips `ker(finFlipParity) ⊂ FinFlipSpace`. -/
noncomputable def EvenFlipFinsupp : Submodule (ZMod 2) FinFlipSpace :=
  LinearMap.ker finFlipParity

/-- Index-2 parity tail submodule `E_0^even := EvenFlipFinsupp.map finFlipIncl ⊂ E0Submodule`. -/
noncomputable def EvenE0Submodule : Submodule (ZMod 2) CantorSpace :=
  EvenFlipFinsupp.map finFlipIncl

theorem evenE0Submodule_le_e0Submodule : EvenE0Submodule ≤ E0Submodule := by
  rintro _ ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

/-- Single coordinate bit flip `e_n ∈ CantorSpace` at index `n`. -/
noncomputable def singleFlip (n : ℕ) : CantorSpace :=
  finFlipIncl (Finsupp.single n 1)

@[simp]
theorem singleFlip_apply (n i : ℕ) :
    singleFlip n i = if n = i then (1 : ZMod 2) else 0 := by
  simp [singleFlip, finFlipIncl_apply, Finsupp.single_apply]

theorem singleFlip_mem_E0Submodule (n : ℕ) : singleFlip n ∈ E0Submodule :=
  ⟨Finsupp.single n 1, rfl⟩

theorem singleFlip_notMem_EvenE0Submodule (n : ℕ) : singleFlip n ∉ EvenE0Submodule := by
  rintro ⟨g, hg_ker, hgeq⟩
  have hfg : g = Finsupp.single n 1 := finFlipIncl_injective hgeq
  have hp0 : finFlipParity g = 0 := hg_ker
  rw [hfg, finFlipParity_single] at hp0
  revert hp0
  decide

theorem evenE0Submodule_lt_e0Submodule : EvenE0Submodule < E0Submodule :=
  lt_of_le_of_ne evenE0Submodule_le_e0Submodule fun heq =>
    singleFlip_notMem_EvenE0Submodule 0 (heq.symm ▸ singleFlip_mem_E0Submodule 0)

/-- Explicit finite-even difference agreeing with `y - x` on all coordinates `j < N`
    with an optional balancing flip at `N` to maintain even parity. -/
noncomputable def evenDiffFinsupp (x y : CantorSpace) (N : ℕ) : FinFlipSpace :=
  (∑ j ∈ Finset.range N, (y j - x j) • Finsupp.single j (1 : ZMod 2)) +
    (∑ j ∈ Finset.range N, (y j - x j)) • Finsupp.single N (1 : ZMod 2)

theorem evenDiffFinsupp_mem_evenFlipFinsupp (x y : CantorSpace) (N : ℕ) :
    evenDiffFinsupp x y N ∈ EvenFlipFinsupp := by
  change finFlipParity (evenDiffFinsupp x y N) = 0
  simp only [evenDiffFinsupp, map_add, map_sum, map_smul, finFlipParity_single, smul_eq_mul,
    mul_one]
  exact zmod2_add_self (∑ j ∈ Finset.range N, (y j - x j))

/-- Constructive sequence inside the `EvenE0Submodule`-coset of `x` approximating `y`. -/
noncomputable def evenApproxSeq (x y : CantorSpace) (N : ℕ) : CantorSpace :=
  x + finFlipIncl (evenDiffFinsupp x y N)

theorem evenApproxSeq_sub_mem_evenE0Submodule (x y : CantorSpace) (N : ℕ) :
    evenApproxSeq x y N - x ∈ EvenE0Submodule := by
  refine ⟨evenDiffFinsupp x y N, evenDiffFinsupp_mem_evenFlipFinsupp x y N, ?_⟩
  simp [evenApproxSeq]

theorem evenApproxSeq_apply_of_lt {x y : CantorSpace} {i N : ℕ} (hi : i < N) :
    evenApproxSeq x y N i = y i := by
  have hneN : i ≠ N := by omega
  have hsingleN : Finsupp.single N (1 : ZMod 2) i = 0 := Finsupp.single_eq_of_ne hneN
  have hsum :
      (∑ j ∈ Finset.range N, (y j - x j) • (Finsupp.single j (1 : ZMod 2) i)) =
        y i - x i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Finsupp.single_eq_of_ne hji.symm, smul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hi))
  simp only [evenApproxSeq, evenDiffFinsupp, Pi.add_apply, finFlipIncl_apply,
    Finsupp.coe_add, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, hsingleN, smul_zero, add_zero]
  change x i + (∑ j ∈ Finset.range N, (y j - x j) • (Finsupp.single j (1 : ZMod 2) i)) = y i
  rw [hsum, add_sub_cancel]

/-- **Coordinatewise Cantor Convergence:** `evenApproxSeq x y N → y` as `N → ∞`
    in the product topology on `2^ℕ`. -/
theorem tendsto_evenApproxSeq (x y : CantorSpace) :
    Filter.Tendsto (evenApproxSeq x y) Filter.atTop (nhds y) := by
  refine tendsto_pi_nhds.mpr fun i => ?_
  refine tendsto_const_nhds.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨i + 1, fun N hN => ?_⟩
  exact (evenApproxSeq_apply_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hN)).symm

/-- **Even-Coset Density:** every `E_0^even`-coset is dense in `CantorSpace`. -/
theorem dense_evenE0Coset (x : CantorSpace) :
    Dense {z : CantorSpace | z - x ∈ EvenE0Submodule} := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hev : ∀ᶠ N in Filter.atTop, evenApproxSeq x y N ∈ U :=
    (tendsto_evenApproxSeq x y).eventually hU
  obtain ⟨N, hN⟩ := hev.exists
  exact ⟨evenApproxSeq x y N, hN, evenApproxSeq_sub_mem_evenE0Submodule x y N⟩

/-- **Full `E_0`-Coset Density:** every `E_0`-coset is dense in `CantorSpace`. -/
theorem dense_e0Coset (x : CantorSpace) :
    Dense {z : CantorSpace | z - x ∈ E0Submodule} :=
  (dense_evenE0Coset x).mono fun _ hz => evenE0Submodule_le_e0Submodule hz

/-- Relational reformulation of `E_0`-coset density. -/
theorem dense_e0Rel_class (x : CantorSpace) :
    Dense {z : CantorSpace | E0Rel z x} := by
  convert dense_e0Coset x using 1
  ext z
  exact (sub_mem_E0Submodule_iff_e0Rel z x).symm

/-- **Polish / Hausdorff Blindness (`E_0^even` Version):** every continuous
    `E_0^even`-invariant map `f : 2^ℕ → Y` into a `T_1` space is constant. -/
theorem continuous_evenE0Invariant_const {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    {f : CantorSpace → Y} (hf : Continuous f)
    (hinv : ∀ z w : CantorSpace, z - w ∈ EvenE0Submodule → f z = f w) :
    ∀ x y : CantorSpace, f x = f y := by
  intro x y
  have hclosed : IsClosed (f ⁻¹' {f x}) := isClosed_singleton.preimage hf
  have hsub : {z : CantorSpace | z - x ∈ EvenE0Submodule} ⊆ f ⁻¹' {f x} := by
    intro z hz
    exact hinv z x hz
  have huniv : f ⁻¹' {f x} = Set.univ := by
    rw [← hclosed.closure_eq, Set.eq_univ_iff_forall]
    intro w
    exact closure_mono hsub ((dense_evenE0Coset x) w)
  have hy : y ∈ f ⁻¹' {f x} := huniv ▸ Set.mem_univ y
  exact hy.symm

/-- **Polish / Hausdorff Blindness (`π_0^{T_1}(Q_{E_0}) ≃ 1`):** every continuous
    `E_0`-invariant map `f : 2^ℕ → Y` into a `T_1` (or Hausdorff / Polish) space is
    constant, proved explicitly from `evenApproxSeq` without Hamel-basis extension. -/
theorem continuous_e0Invariant_const {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    {f : CantorSpace → Y} (hf : Continuous f)
    (hinv : ∀ z w : CantorSpace, E0Rel z w → f z = f w) :
    ∀ x y : CantorSpace, f x = f y :=
  continuous_evenE0Invariant_const hf fun z w hw =>
    hinv z w ((sub_mem_E0Submodule_iff_e0Rel z w).mp (evenE0Submodule_le_e0Submodule hw))

/-- No continuous `T_1`-valued invariant can distinguish distinct `E_0`-tail classes. -/
theorem not_exists_continuous_t1_e0Separator :
    ¬ ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T1Space Y) (f : CantorSpace → Y),
      Continuous f ∧ (∀ z w : CantorSpace, E0Rel z w → f z = f w) ∧ ∃ a b, f a ≠ f b := by
  rintro ⟨Y, _, _, f, hf, hinv, a, b, hne⟩
  exact hne (continuous_e0Invariant_const hf hinv a b)

/-! ## Section 4: The $E_0^{\mathrm{even}}$ Parity Torsor Dichotomy -/

/-- A parity cocycle alternates sign modulo `2` under every single coordinate bit flip `e_n`. -/
def IsFlipAlternating (χ : CantorSpace → ZMod 2) : Prop :=
  ∀ (x : CantorSpace) (n : ℕ), χ (x + singleFlip n) = χ x + 1

private theorem isFlipAlternating_add_finFlip {χ : CantorSpace → ZMod 2}
    (hχ : IsFlipAlternating χ) (x : CantorSpace) (g : FinFlipSpace) :
    χ (x + finFlipIncl g) = χ x + finFlipParity g := by
  induction g using Finsupp.induction with
  | zero => simp
  | single_add n a g _ _ ih =>
    rcases zmod2_eq_zero_or_one a with rfl | rfl
    · simp [ih]
    · have hvec : x + finFlipIncl (Finsupp.single n 1 + g) =
          (x + finFlipIncl g) + singleFlip n := by
        simp only [singleFlip, map_add]
        abel
      rw [hvec, hχ, ih, map_add, finFlipParity_single, add_assoc, add_comm (finFlipParity g) 1]

theorem isFlipAlternating_evenE0Invariant {χ : CantorSpace → ZMod 2}
    (hχ : IsFlipAlternating χ) {z w : CantorSpace} (hzw : z - w ∈ EvenE0Submodule) :
    χ z = χ w := by
  rcases hzw with ⟨g, hg_ker, hgeq⟩
  have hz : z = w + finFlipIncl g := eq_add_of_sub_eq' hgeq.symm
  rw [hz, isFlipAlternating_add_finFlip hχ]
  have hp0 : finFlipParity g = 0 := hg_ker
  rw [hp0, add_zero]

/-- **Constructive Parity Obstruction:** since every `E_0^even`-coset is dense and `ZMod 2` is
    `T_1`, NO continuous single-flip-alternating parity functional exists on Cantor space. -/
theorem not_exists_continuous_flipAlternating :
    ¬ ∃ χ : CantorSpace → ZMod 2, Continuous χ ∧ IsFlipAlternating χ := by
  rintro ⟨χ, hcont, halt⟩
  have hconst := continuous_evenE0Invariant_const hcont
    (fun z w hzw => isFlipAlternating_evenE0Invariant halt hzw) 0 (singleFlip 0)
  have hflip := halt 0 0
  rw [zero_add, ← hconst] at hflip
  have := congrArg (fun u : ZMod 2 => u - χ 0) hflip
  simp at this

/-- Parity functional transported to `E0Submodule` via `finFlipIncl_injective`. -/
noncomputable def e0SubmoduleParity : E0Submodule →ₗ[ZMod 2] ZMod 2 :=
  finFlipParity.comp (LinearEquiv.ofInjective finFlipIncl finFlipIncl_injective).symm.toLinearMap

@[simp]
theorem e0SubmoduleParity_singleFlip (n : ℕ) :
    e0SubmoduleParity ⟨singleFlip n, singleFlip_mem_E0Submodule n⟩ = 1 := by
  have heq : (LinearEquiv.ofInjective finFlipIncl finFlipIncl_injective).symm
      ⟨singleFlip n, singleFlip_mem_E0Submodule n⟩ = Finsupp.single n 1 := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  change finFlipParity ((LinearEquiv.ofInjective finFlipIncl finFlipIncl_injective).symm
    ⟨singleFlip n, singleFlip_mem_E0Submodule n⟩) = 1
  rw [heq, finFlipParity_single]

/-- **`ZFC` Discontinuous Parity Extension:** via `LinearMap.exists_extend` (`Classical.choice`),
    `e0SubmoduleParity` extends to a `ZMod 2`-linear single-flip-alternating map on all of
    `CantorSpace` (which is necessarily discontinuous). -/
theorem exists_zfc_linear_flipAlternating :
    ∃ χ : CantorSpace →ₗ[ZMod 2] ZMod 2, IsFlipAlternating χ ∧ ¬ Continuous χ := by
  obtain ⟨χ, hχ⟩ := e0SubmoduleParity.exists_extend
  have halt : IsFlipAlternating χ := by
    intro x n
    have hval : χ (singleFlip n) = 1 := by
      have hsub := congrArg (fun f : E0Submodule →ₗ[ZMod 2] ZMod 2 =>
        f ⟨singleFlip n, singleFlip_mem_E0Submodule n⟩) hχ
      simpa using hsub
    rw [map_add, hval]
  refine ⟨χ, halt, fun hcont => not_exists_continuous_flipAlternating ⟨χ, hcont, halt⟩⟩

/-- Two-sheeted parity quotient `2^ℕ / E_0^even` carrying a `ZMod 2`-vector space structure. -/
abbrev EvenE0Quotient : Type :=
  CantorSpace ⧸ EvenE0Submodule

/-- Canonical double-cover epimorphism `(2^ℕ / E_0^even) ↠ Q_{E_0}`. -/
noncomputable def evenToE0Quotient : EvenE0Quotient →ₗ[ZMod 2] E0Quotient :=
  EvenE0Submodule.mapQ E0Submodule LinearMap.id evenE0Submodule_le_e0Submodule

theorem evenToE0Quotient_surjective : Function.Surjective evenToE0Quotient := by
  intro y
  obtain ⟨x, rfl⟩ := e0QuotientMk_surjective y
  refine ⟨EvenE0Submodule.mkQ x, ?_⟩
  rfl

theorem singleFlip_zero_mem_ker_evenToE0Quotient :
    EvenE0Submodule.mkQ (singleFlip 0) ∈ LinearMap.ker evenToE0Quotient ∧
      EvenE0Submodule.mkQ (singleFlip 0) ≠ 0 := by
  constructor
  · change evenToE0Quotient (EvenE0Submodule.mkQ (singleFlip 0)) = 0
    change e0QuotientMk (singleFlip 0) = 0
    exact (Submodule.Quotient.mk_eq_zero E0Submodule).mpr (singleFlip_mem_E0Submodule 0)
  · intro h0
    have hmem : singleFlip 0 ∈ EvenE0Submodule :=
      (Submodule.Quotient.mk_eq_zero EvenE0Submodule).mp h0
    exact singleFlip_notMem_EvenE0Submodule 0 hmem

instance instNontrivialKerEvenToE0Quotient : Nontrivial (LinearMap.ker evenToE0Quotient) :=
  ⟨⟨0, ⟨EvenE0Submodule.mkQ (singleFlip 0), singleFlip_zero_mem_ker_evenToE0Quotient.1⟩,
    fun h => singleFlip_zero_mem_ker_evenToE0Quotient.2 (congrArg Subtype.val h).symm⟩⟩

/-- **`ZFC` Torsor Splitting:** `Classical.choice` splits the double cover
    `(2^ℕ / E_0^even) ↠ Q_{E_0}` via a `ZMod 2`-linear right inverse. -/
theorem exists_zfc_linear_section_evenToE0Quotient :
    ∃ s : E0Quotient →ₗ[ZMod 2] EvenE0Quotient, evenToE0Quotient.comp s = LinearMap.id := by
  obtain ⟨χ, halt, _⟩ := exists_zfc_linear_flipAlternating
  let g : CantorSpace →ₗ[ZMod 2] EvenE0Quotient :=
    EvenE0Submodule.mkQ.comp (LinearMap.id - χ.smulRight (singleFlip 0))
  have hker : E0Submodule ≤ LinearMap.ker g := by
    rintro u ⟨f, rfl⟩
    change g (finFlipIncl f) = 0
    change (Submodule.Quotient.mk (finFlipIncl f - χ (finFlipIncl f) • singleFlip 0) :
      EvenE0Quotient) = 0
    rw [Submodule.Quotient.mk_eq_zero EvenE0Submodule]
    have hχf : χ (finFlipIncl f) = finFlipParity f := by
      have h0 : χ 0 = 0 := map_zero χ
      have h1 := isFlipAlternating_add_finFlip halt 0 f
      rw [zero_add, h0, zero_add] at h1
      exact h1
    refine ⟨f - χ (finFlipIncl f) • Finsupp.single 0 1, ?_, ?_⟩
    · change finFlipParity (f - χ (finFlipIncl f) • Finsupp.single 0 1) = 0
      rw [map_sub, map_smul, finFlipParity_single, smul_eq_mul, mul_one, hχf, sub_self]
    · rw [map_sub, map_smul]
      rfl
  refine ⟨E0Submodule.liftQ g hker, ?_⟩
  ext x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  change evenToE0Quotient (g x) = e0QuotientMk x
  change evenToE0Quotient (EvenE0Submodule.mkQ (x - χ x • singleFlip 0)) = e0QuotientMk x
  change e0QuotientMk (x - χ x • singleFlip 0) = e0QuotientMk x
  rw [map_sub, map_smul]
  have hsf : e0QuotientMk (singleFlip 0) = 0 :=
    (Submodule.Quotient.mk_eq_zero E0Submodule).mpr (singleFlip_mem_E0Submodule 0)
  rw [hsf, smul_zero, sub_zero]

/-! ## Section 5: Unified Chapter 4 §4.5 Borel Tail Residuum Summary -/

/-- **Chapter 4 §4.5 Unified Theorem (`thm:double-solvent-r4` & `E_0^even` Parity Torsor):**
    Combines:
    1. Exactness & nontriviality of `0 → FinFlipSpace → CantorSpace → Q_{E_0} → 0`;
    2. Classical `ZFC` linear section splitting (`Classical.choice`);
    3. Universal coset density of `E_0^even` and `E_0` in Cantor space, forcing all
       continuous `E_0^even`- and `E_0`-invariant `T_1` maps to be constant (constructive);
    4. Constructive impossibility of continuous single-flip-alternating parity functionals vs.
       `ZFC` discontinuous linear parity extensions splitting `(2^ℕ / E_0^even) ↠ Q_{E_0}`. -/
theorem chapter4_borel_tail_residuum_summary :
    (LinearMap.range finFlipIncl = LinearMap.ker e0QuotientMk ∧ Nontrivial E0Quotient) ∧
    (∃ s : E0Quotient →ₗ[ZMod 2] CantorSpace, e0QuotientMk.comp s = LinearMap.id) ∧
    (∀ x : CantorSpace, Dense {z : CantorSpace | z - x ∈ EvenE0Submodule} ∧
      Dense {z : CantorSpace | E0Rel z x}) ∧
    (∀ (Y : Type) [TopologicalSpace Y] [T1Space Y] (f : CantorSpace → Y),
      Continuous f → (∀ z w, E0Rel z w → f z = f w) → ∀ x y, f x = f y) ∧
    (¬ ∃ χ : CantorSpace → ZMod 2, Continuous χ ∧ IsFlipAlternating χ) ∧
    (∃ χ : CantorSpace →ₗ[ZMod 2] ZMod 2, IsFlipAlternating χ ∧ ¬ Continuous χ) ∧
    (∃ s : E0Quotient →ₗ[ZMod 2] EvenE0Quotient, evenToE0Quotient.comp s = LinearMap.id) := by
  refine ⟨⟨exact_finFlipIncl_e0QuotientMk, instNontrivialE0Quotient⟩,
    exists_zfc_linear_section_e0Quotient,
    fun x => ⟨dense_evenE0Coset x, dense_e0Rel_class x⟩,
    fun Y _ _ f hf hinv x y => continuous_e0Invariant_const hf hinv x y,
    not_exists_continuous_flipAlternating,
    exists_zfc_linear_flipAlternating,
    exists_zfc_linear_section_evenToE0Quotient⟩

/-! ## Section 6: Mandatory 4-Layer Definition Check Gate (`namespace Checks`) -/

namespace Checks

/-! ### Layer 1: Carrier Inhabitation (`Nontrivial` Instances) -/

example : Nontrivial CantorSpace := inferInstance
example : Nontrivial FinFlipSpace := inferInstance
example : Nontrivial E0Quotient := inferInstance
example : Nontrivial (LinearMap.ker evenToE0Quotient) := inferInstance

theorem borel_nontrivial_evenE0Quotient : Nontrivial EvenE0Quotient := by
  refine ⟨⟨0, EvenE0Submodule.mkQ (singleFlip 0), ?_⟩⟩
  intro h
  exact singleFlip_zero_mem_ker_evenToE0Quotient.2 h.symm

/-! ### Layer 2: Bidirectional Separation (Positive & Negative Witnesses) -/

theorem borel_positive_singleFlip_mem_e0 : singleFlip 0 ∈ E0Submodule :=
  singleFlip_mem_E0Submodule 0

theorem borel_negative_constOne_notMem_e0 : constOne ∉ E0Submodule :=
  constOne_notMem_E0Submodule

theorem borel_positive_pairFlip_mem_evenE0 :
    singleFlip 0 + singleFlip 1 ∈ EvenE0Submodule := by
  refine ⟨Finsupp.single 0 1 + Finsupp.single 1 1, ?_, ?_⟩
  · change finFlipParity (Finsupp.single 0 1 + Finsupp.single 1 1) = 0
    rw [map_add, finFlipParity_single, finFlipParity_single]
    decide
  · simp [singleFlip]

theorem borel_negative_singleFlip_notMem_evenE0 :
    singleFlip 0 ∉ EvenE0Submodule :=
  singleFlip_notMem_EvenE0Submodule 0

theorem borel_continuous_eval_zero_non_e0Invariant :
    Continuous (fun x : CantorSpace => x 0) ∧
      ∃ x y : CantorSpace, E0Rel x y ∧ x 0 ≠ y 0 := by
  refine ⟨continuous_apply 0, 0, singleFlip 0, ?_, ?_⟩
  · refine ⟨1, fun n hn => ?_⟩
    simp [singleFlip_apply, show 0 ≠ n by omega]
  · simp [singleFlip_apply]

theorem borel_no_continuous_vs_zfc_linear_flipAlternating :
    (¬ ∃ χ : CantorSpace → ZMod 2, Continuous χ ∧ IsFlipAlternating χ) ∧
      (∃ χ : CantorSpace →ₗ[ZMod 2] ZMod 2, IsFlipAlternating χ ∧ ¬ Continuous χ) :=
  ⟨not_exists_continuous_flipAlternating, exists_zfc_linear_flipAlternating⟩

/-! ### Layer 3: `mathlib4` Projections & Derived Sanity Lemmas -/

example : Module (ZMod 2) E0Quotient := inferInstance
noncomputable def borel_module_evenE0Quotient : Module (ZMod 2) EvenE0Quotient := inferInstance
example : CompactSpace CantorSpace := inferInstance
example : T2Space CantorSpace := inferInstance
example : TotallyDisconnectedSpace CantorSpace := inferInstance

theorem borel_evenApproxSeq_agree_first_two_check :
    evenApproxSeq 0 constOne 2 0 = 1 ∧ evenApproxSeq 0 constOne 2 1 = 1 :=
  ⟨evenApproxSeq_apply_of_lt (by decide), evenApproxSeq_apply_of_lt (by decide)⟩

theorem borel_zfc_direct_sum_decomposition_check :
    Nonempty (CantorSpace ≃ₗ[ZMod 2] FinFlipSpace × E0Quotient) :=
  nonempty_linearEquiv_cantor_prod_e0Quotient

theorem borel_ker_double_cover_check :
    EvenE0Submodule.mkQ (singleFlip 0) ∈ LinearMap.ker evenToE0Quotient ∧
      EvenE0Submodule.mkQ (singleFlip 0) ≠ 0 :=
  singleFlip_zero_mem_ker_evenToE0Quotient

/-! ### Layer 4: Kernel Axiom Gate (`#guard_msgs in #print axioms`) -/

section KernelAxiomGate

/-- info: 'HomotopyCRM.finFlipIncl_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.finFlipIncl_injective

/-- info: 'HomotopyCRM.sub_mem_E0Submodule_iff_e0Rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.sub_mem_E0Submodule_iff_e0Rel

/-- info: 'HomotopyCRM.constOne_notMem_E0Submodule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.constOne_notMem_E0Submodule

/-- info: 'HomotopyCRM.exists_zfc_linear_section_e0Quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.exists_zfc_linear_section_e0Quotient

/-- info: 'HomotopyCRM.nonempty_linearEquiv_cantor_prod_e0Quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.nonempty_linearEquiv_cantor_prod_e0Quotient

/-- info: 'HomotopyCRM.singleFlip_notMem_EvenE0Submodule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.singleFlip_notMem_EvenE0Submodule

/-- info: 'HomotopyCRM.evenDiffFinsupp_mem_evenFlipFinsupp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.evenDiffFinsupp_mem_evenFlipFinsupp

/-- info: 'HomotopyCRM.evenApproxSeq_apply_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.evenApproxSeq_apply_of_lt

/-- info: 'HomotopyCRM.tendsto_evenApproxSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.tendsto_evenApproxSeq

/-- info: 'HomotopyCRM.dense_evenE0Coset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.dense_evenE0Coset

/-- info: 'HomotopyCRM.dense_e0Coset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.dense_e0Coset

/-- info: 'HomotopyCRM.continuous_evenE0Invariant_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.continuous_evenE0Invariant_const

/-- info: 'HomotopyCRM.continuous_e0Invariant_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.continuous_e0Invariant_const

/-- info: 'HomotopyCRM.not_exists_continuous_t1_e0Separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.not_exists_continuous_t1_e0Separator

/-- info: 'HomotopyCRM.not_exists_continuous_flipAlternating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.not_exists_continuous_flipAlternating

/-- info: 'HomotopyCRM.exists_zfc_linear_flipAlternating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.exists_zfc_linear_flipAlternating

/-- info: 'HomotopyCRM.evenToE0Quotient_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.evenToE0Quotient_surjective

/-- info: 'HomotopyCRM.exists_zfc_linear_section_evenToE0Quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.exists_zfc_linear_section_evenToE0Quotient

/-- info: 'HomotopyCRM.chapter4_borel_tail_residuum_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.chapter4_borel_tail_residuum_summary

end KernelAxiomGate

end Checks

end HomotopyCRM
