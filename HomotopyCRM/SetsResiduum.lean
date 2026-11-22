import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.AddTorsor.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.ZFC.Basic

/-!
# Chapter 7: Residuums and "Sets" (`HomotopyCRM.SetsResiduum`)

This module mechanizes the core algebraic, coalgebraic, and categorical witnesses of Chapter 7
(*Residuums and "Sets"*), calibrating the double-clamped characterization of `Set_ZFC` and `NBG`
along Coordinate Axes I, V, VI, and VII:

1. **Baseline Definable-Class Coreflection (`Def ⊣ π_Set`, `def:set-projection-fibration`):**
   Constructs concrete two-sorted set-and-class structures, proves via an explicit embedding
   `finOmegaModel ↪ powOmegaModel` that naive class pullback breaks `SatisfiesSubclassSeparation`,
   and establishes the coreflective adjunction `defSetProjAdjunction : defFunctor ⊣ piSetFunctor`.
2. **Large Equivalence-Splitting & Global Choice (Proposition `prop:large-equiv-splitting`):**
   * `card_split_iff_global_choice` *(axiom-free)*: proves over an abstract skeletal cardinal base
     that a pointwise homotopy-functorial quasi-inverse splitting of `Card ↪ Set` is equivalent to
     uniform small-set choice `G(X) = η_X⁻¹(∅)`, avoiding hidden `funext` (`Quot.sound`) axioms.
   * `type_equiv_splitting_global_choice`: instantiates the equivalence over `Type u` via
     `CategoryTheory.Skeleton`, `CategoryTheory.Functor`, and von Neumann initial ordinals
     `Cardinal.ord`, exhibiting global functorial skeleton splitting via `Classical.choice`.
3. **Axis VII Foundation vs. Anti-Foundation (`μ P_S ↪ ν P_S`, Theorem `thm:axis-vii-foundation`):**
   * Embeds `PSet.{u}` into small accessible pointed graph coalgebras `APG.{u}` via pure structural
     recursion `psetToAPG` (`PSet.rec`), proves `pset_equiv_iff_bisimilar` *(axiom-free)* showing
     `μ P_S / ~` embeds monomorphically into bisimulation classes, and proves
     `quine_atom_outside_wf` *(axiom-free)* certifying that the self-loop Quine coalgebra
     `quineAPG` (`q = {q}`) is not bisimilar to `psetToAPG x` for any well-founded `x : PSet.{u}`.
4. **Boffa Hyperset Torsors (Proposition `prop:boffa-torsors`):**
   * Separates `APG.Bisimilar` from pointed graph isomorphism `APG.Iso` via `quineAPG` (`|V| = 1`)
     versus the mutual `2`-cycle `quineTwoCycleAPG` (`|V| = 2`).
   * `boffa_twin_torsor` *(axiom-free)*: proves the `Bool` (`ℤ/2ℤ`) swap action on ordered distinct
     twin Quine pairs is free, simply transitive, and admits no swap-equivariant global section.
   * `boffa_twin_addTorsor`: projects the twin-pair fiber onto stock `Mathlib` `AddTorsor (ZMod 2)`
     over the quotient unordered-pair orbit (`[propext, Quot.sound]`, without `Classical.choice`).
5. **Material Extensionality & Quotient Gate (Proposition `prop:extensionality-truncation`):**
   * `zfset_ext_quot_gate`: proves via `Quotient.sound` over `PSet.Equiv` (`[propext, Quot.sound]`,
     no `Classical.choice`) that passing from intensional trees `PSet` (`μ P_Anima` at `0`-types)
     to extensional `ZFSet` collapses both element multiplicity (`[∅, ∅] ~ [∅]`) and arbitrary
     branch permutations `σ : α ≃ α` (killing loop automorphisms `Aut(α)`), while both remain
     strictly distinct in `PSet`.
-/

namespace HomotopyCRM.SetsResiduum

open CategoryTheory

universe u v

/-! ## Section 1: Class-Set Model Spaces and the Baseline Adjunction `Def ⊣ π_Set` -/

/-- Parameterized Boolean-membership formulas over a set carrier `M`, generating the minimal
predicative definable class algebra `Def(M)`. -/
inductive ParamClassFormula (P : Type u) : Type u
  | eqParam : P → ParamClassFormula P
  | memParam : P → ParamClassFormula P
  | compl : ParamClassFormula P → ParamClassFormula P
  | inter : ParamClassFormula P → ParamClassFormula P → ParamClassFormula P

namespace ParamClassFormula

/-- Syntactic parameter translation along a map `f : P → Q`. -/
def map {P Q : Type u} (f : P → Q) : ParamClassFormula P → ParamClassFormula Q
  | .eqParam p => .eqParam (f p)
  | .memParam p => .memParam (f p)
  | .compl φ => .compl (φ.map f)
  | .inter φ ψ => .inter (φ.map f) (ψ.map f)

@[simp]
theorem map_id {P : Type u} : ∀ φ : ParamClassFormula P, φ.map id = φ
  | .eqParam _ => rfl
  | .memParam _ => rfl
  | .compl φ => congrArg compl (map_id φ)
  | .inter φ ψ => congrArg₂ inter (map_id φ) (map_id ψ)

@[simp]
theorem map_comp {P Q R : Type u} (f : P → Q) (g : Q → R) :
    ∀ φ : ParamClassFormula P, φ.map (g ∘ f) = (φ.map f).map g
  | .eqParam _ => rfl
  | .memParam _ => rfl
  | .compl φ => congrArg compl (map_comp f g φ)
  | .inter φ ψ => congrArg₂ inter (map_comp f g φ) (map_comp f g ψ)

end ParamClassFormula

/-- A concrete first-order membership structure `(M, ∈)`. -/
structure SetStructure : Type (u + 1) where
  Carrier : Type u
  mem : Carrier → Carrier → Prop

/-- Extensional evaluation of a parameterized class formula inside a `SetStructure`. -/
def evalClassFormula (M : SetStructure.{u}) : ParamClassFormula M.Carrier → Set M.Carrier
  | .eqParam p => {x | x = p}
  | .memParam p => {x | M.mem x p}
  | .compl φ => (evalClassFormula M φ)ᶜ
  | .inter φ ψ => evalClassFormula M φ ∩ evalClassFormula M ψ

/-- Morphisms in `SetElemCat`: embeddings preserving `∈` and reflecting/preserving nonemptiness
of parameter-definable Boolean combinations (ensuring well-definedness of `Def` transport). -/
structure SetElemHom (M N : SetStructure.{u}) : Type u where
  toFun : M.Carrier → N.Carrier
  mem_iff : ∀ x y : M.Carrier, M.mem x y ↔ N.mem (toFun x) (toFun y)
  elem_ext : ∀ φ ψ : ParamClassFormula M.Carrier,
    evalClassFormula M φ = evalClassFormula M ψ →
      evalClassFormula N (φ.map toFun) = evalClassFormula N (ψ.map toFun)

namespace SetElemHom

@[ext]
theorem ext {M N : SetStructure.{u}} {f g : SetElemHom M N} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- Identity morphism on a `SetStructure`. -/
def id (M : SetStructure.{u}) : SetElemHom M M where
  toFun := _root_.id
  mem_iff _ _ := Iff.rfl
  elem_ext φ ψ h := by simpa [ParamClassFormula.map_id] using h

/-- Composition of elementary set morphisms. -/
def comp {L M N : SetStructure.{u}} (f : SetElemHom L M) (g : SetElemHom M N) :
    SetElemHom L N where
  toFun := g.toFun ∘ f.toFun
  mem_iff x y := (f.mem_iff x y).trans (g.mem_iff (f.toFun x) (f.toFun y))
  elem_ext φ ψ h := by
    rw [ParamClassFormula.map_comp, ParamClassFormula.map_comp]
    exact g.elem_ext (φ.map f.toFun) (ψ.map f.toFun) (f.elem_ext φ ψ h)

end SetElemHom

instance instCategorySetStructure : Category.{u} SetStructure.{u} where
  Hom := SetElemHom
  id := SetElemHom.id
  comp := SetElemHom.comp

/-- An admissible class expansion `(M, C)` over a `SetStructure`, closed under all
parameter-definable classes, complements, and intersections. -/
structure ClassSetModel : Type (u + 1) where
  base : SetStructure.{u}
  IsClass : Set base.Carrier → Prop
  def_mem : ∀ φ : ParamClassFormula base.Carrier, IsClass (evalClassFormula base φ)
  compl_mem : ∀ {S}, IsClass S → IsClass Sᶜ
  inter_mem : ∀ {S T}, IsClass S → IsClass T → IsClass (S ∩ T)

/-- Two-sorted morphisms `(f, F) : (M, C) ⟶ (N, D)` whose first coordinate `baseHom` is a
`ParamClassFormula`-elementary embedding (`SetElemHom M N`, preserving `∈` and extensional
equalities of first-order parameter-definable Boolean combinations) and whose class map transports
parameter-definable classes canonically via `φ(x, p) ↦ φ(x, f(p))`. -/
structure ClassSetHom (X Y : ClassSetModel.{u}) : Type u where
  baseHom : X.base ⟶ Y.base
  classMap : {S : Set X.base.Carrier // X.IsClass S} → {T : Set Y.base.Carrier // Y.IsClass T}
  map_def : ∀ φ : ParamClassFormula X.base.Carrier,
    (classMap ⟨evalClassFormula X.base φ, X.def_mem φ⟩).1 =
      evalClassFormula Y.base (φ.map baseHom.toFun)

namespace ClassSetHom

@[ext]
theorem ext {X Y : ClassSetModel.{u}} {f g : ClassSetHom X Y}
    (hb : f.baseHom = g.baseHom)
    (hc : ∀ S : {S // X.IsClass S}, (f.classMap S).1 = (g.classMap S).1) : f = g := by
  cases f with
  | mk bf cf mf =>
    cases g with
    | mk bg cg mg =>
      cases hb
      have hfun : cf = cg := funext fun S => Subtype.ext (hc S)
      cases hfun
      rfl

/-- Identity two-sorted morphism. -/
def id (X : ClassSetModel.{u}) : ClassSetHom X X where
  baseHom := 𝟙 X.base
  classMap := _root_.id
  map_def φ := by
    change evalClassFormula X.base φ = evalClassFormula X.base (φ.map _root_.id)
    rw [ParamClassFormula.map_id]

/-- Composition of two-sorted class-set morphisms. -/
def comp {X Y Z : ClassSetModel.{u}} (f : ClassSetHom X Y) (g : ClassSetHom Y Z) :
    ClassSetHom X Z where
  baseHom := f.baseHom ≫ g.baseHom
  classMap := g.classMap ∘ f.classMap
  map_def φ := by
    have h₁ : f.classMap ⟨evalClassFormula X.base φ, X.def_mem φ⟩ =
        ⟨evalClassFormula Y.base (φ.map f.baseHom.toFun), Y.def_mem (φ.map f.baseHom.toFun)⟩ :=
      Subtype.ext (f.map_def φ)
    change (g.classMap (f.classMap ⟨evalClassFormula X.base φ, X.def_mem φ⟩)).1 = _
    rw [h₁, g.map_def (φ.map f.baseHom.toFun)]
    change _ = evalClassFormula Z.base (φ.map (g.baseHom.toFun ∘ f.baseHom.toFun))
    rw [ParamClassFormula.map_comp]

end ClassSetHom

instance instCategoryClassSetModel : Category.{u} ClassSetModel.{u} where
  Hom := ClassSetHom
  id := ClassSetHom.id
  comp := ClassSetHom.comp

/-- The forgetful projection functor `π_Set : ClassSetModel ⥤ SetStructure`. -/
@[simps]
def piSetFunctor : ClassSetModel.{u} ⥤ SetStructure.{u} where
  obj X := X.base
  map f := f.baseHom

/-- The minimal definable class expansion `Def(M)` of a `SetStructure`. -/
@[simps]
def defModel (M : SetStructure.{u}) : ClassSetModel.{u} where
  base := M
  IsClass S := ∃ φ : ParamClassFormula M.Carrier, S = evalClassFormula M φ
  def_mem φ := ⟨φ, rfl⟩
  compl_mem := fun ⟨φ, hφ⟩ => ⟨.compl φ, by simp [hφ, evalClassFormula]⟩
  inter_mem := fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ => ⟨.inter φ ψ, by simp [hφ, hψ, evalClassFormula]⟩

/-- Canonical extension of an elementary set embedding `f : M ⟶ Y.base` to `(Def(M)) ⟶ Y`. -/
noncomputable def liftFromDef {M : SetStructure.{u}} {Y : ClassSetModel.{u}}
    (f : M ⟶ Y.base) : defModel M ⟶ Y where
  baseHom := f
  classMap S :=
    let φ := Classical.choose S.2
    ⟨evalClassFormula Y.base (φ.map f.toFun), Y.def_mem (φ.map f.toFun)⟩
  map_def φ := by
    dsimp
    set ψ := Classical.choose (defModel M |>.def_mem φ)
    have hψ : evalClassFormula M φ = evalClassFormula M ψ :=
      Classical.choose_spec (defModel M |>.def_mem φ)
    exact (f.elem_ext φ ψ hψ).symm

theorem liftFromDef_unique {M : SetStructure.{u}} {Y : ClassSetModel.{u}}
    (g : defModel M ⟶ Y) : g = liftFromDef g.baseHom := by
  apply ClassSetHom.ext
  · rfl
  · rintro ⟨S, φ, rfl⟩
    have hg := g.map_def φ
    have hl := (liftFromDef g.baseHom).map_def φ
    exact hg.trans hl.symm

/-- Action of `Def` on morphisms `f : M ⟶ N`. -/
noncomputable def defMap {M N : SetStructure.{u}} (f : M ⟶ N) : defModel M ⟶ defModel N :=
  liftFromDef (Y := defModel N) f

/-- The baseline definable-class embedding functor `Def : SetStructure ⥤ ClassSetModel`. -/
@[simps]
noncomputable def defFunctor : SetStructure.{u} ⥤ ClassSetModel.{u} where
  obj := defModel
  map f := defMap f
  map_id M := (liftFromDef_unique (𝟙 (defModel M))).symm
  map_comp {_ _ Z} f g :=
    (liftFromDef_unique (Y := defModel Z) (defMap f ≫ defMap g)).symm

/-- Definition `def:set-projection-fibration`(ii): the baseline definable-class functor `Def` is
left adjoint to the set-projection functor `π_Set` (`Def ⊣ π_Set`). -/
noncomputable def defSetProjAdjunction : defFunctor.{u} ⊣ piSetFunctor.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun g => g.baseHom
          invFun := fun f => liftFromDef f
          left_inv := fun g => (liftFromDef_unique g).symm
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := fun {_ _ Y} h f =>
        (liftFromDef_unique (Y := Y) (defMap h ≫ liftFromDef f)).symm
      homEquiv_naturality_right := fun _ _ => rfl }

/-- Subclass Separation (Aussonderung) on a two-sorted `ClassSetModel`: every class `C` in `M`
bounded by some set `a : M.base.Carrier` (`∀ x ∈ C, M.base.mem x a`) is extensionally
represented by a set `b : M.base.Carrier` (`∀ x, M.base.mem x b ↔ x ∈ C`). -/
def SatisfiesSubclassSeparation (M : ClassSetModel.{u}) : Prop :=
  ∀ C : Set M.base.Carrier, M.IsClass C →
    (∃ a : M.base.Carrier, ∀ x ∈ C, M.base.mem x a) →
    ∃ b : M.base.Carrier, ∀ x : M.base.Carrier, M.base.mem x b ↔ x ∈ C

/-- Set carrier for the minimal finite-and-cofinite `ℕ`-submodel (`finOmegaModel`):
`.atom n` encodes natural numbers `n : Nat`, while `.set S` encodes finite or cofinite subsets
of `Nat` (needed because `ClassSetModel` is closed under `eqParam` singletons, complements
`compl_mem`, and intersections `inter_mem`, so the definable Boolean algebra on `ω` consists
precisely of finite and cofinite subsets, including finite subsets and `ω = Set.univ`). -/
inductive FinOmegaCarrier : Type where
  | atom : Nat → FinOmegaCarrier
  | set : {A : Set Nat // A.Finite ∨ Aᶜ.Finite} → FinOmegaCarrier

/-- Distinguished infinite ordinal set `ω = Set.univ` inside `FinOmegaCarrier`. -/
def omegaFinSet : FinOmegaCarrier :=
  .set ⟨Set.univ, Or.inr (Set.compl_univ ▸ Set.finite_empty)⟩

/-- Base membership structure `(FinOmegaCarrier, ∈)`. -/
def finOmegaBase : SetStructure.{0} where
  Carrier := FinOmegaCarrier
  mem x y :=
    match x, y with
    | .atom n, .set S => n ∈ S.1
    | _, _ => False

/-- Minimal definable `ClassSetModel` over `finOmegaBase`. -/
def finOmegaModel : ClassSetModel.{0} :=
  defModel finOmegaBase

/-- Set carrier for the ambient powerset model `powOmegaModel`, containing all `A : Set Nat`. -/
inductive PowOmegaCarrier : Type where
  | atom : Nat → PowOmegaCarrier
  | set : Set Nat → PowOmegaCarrier

/-- Base membership structure `(PowOmegaCarrier, ∈)`. -/
def powOmegaBase : SetStructure.{0} where
  Carrier := PowOmegaCarrier
  mem x y :=
    match x, y with
    | .atom n, .set S => n ∈ S
    | _, _ => False

/-- Minimal definable `ClassSetModel` over `powOmegaBase`. -/
def powOmegaModel : ClassSetModel.{0} :=
  defModel powOmegaBase

/-- Canonical `∈`-preserving embedding from `FinOmegaCarrier` into `PowOmegaCarrier`. -/
def finToPow : FinOmegaCarrier → PowOmegaCarrier
  | .atom n => .atom n
  | .set S => .set S.1

theorem finToPow_injective : Function.Injective finToPow := by
  intro x y hxy
  cases x with
  | atom m =>
    cases y with
    | atom n => exact congrArg FinOmegaCarrier.atom (PowOmegaCarrier.atom.inj hxy)
    | set T => cases hxy
  | set S =>
    cases y with
    | atom n => cases hxy
    | set T => exact congrArg FinOmegaCarrier.set (Subtype.ext (PowOmegaCarrier.set.inj hxy))

theorem finToPow_mem_iff (x y : FinOmegaCarrier) :
    finOmegaBase.mem x y ↔ powOmegaBase.mem (finToPow x) (finToPow y) := by
  cases x <;> cases y <;> rfl

theorem evalClassFormula_finOmega_atom_finCofin :
    ∀ φ : ParamClassFormula FinOmegaCarrier,
      ({n : Nat | FinOmegaCarrier.atom n ∈ evalClassFormula finOmegaBase φ}).Finite ∨
        ({n : Nat | FinOmegaCarrier.atom n ∈ evalClassFormula finOmegaBase φ})ᶜ.Finite
  | .eqParam p => by
    cases p with
    | atom m =>
      refine Or.inl ((Set.finite_singleton m).subset ?_)
      intro n hn
      exact FinOmegaCarrier.atom.inj hn
    | set S =>
      refine Or.inl (Set.finite_empty.subset ?_)
      intro n hn
      cases hn
  | .memParam p => by
    cases p with
    | atom m =>
      refine Or.inl (Set.finite_empty.subset ?_)
      intro n hn
      cases hn
    | set S => exact S.2
  | .compl φ => by
    rcases evalClassFormula_finOmega_atom_finCofin φ with h | h
    · refine Or.inr (h.subset fun n hn => ?_)
      simpa [evalClassFormula] using hn
    · exact Or.inl h
  | .inter φ ψ => by
    rcases evalClassFormula_finOmega_atom_finCofin φ with hφ | hφ
    · exact Or.inl (hφ.subset fun _ hx => hx.1)
    · rcases evalClassFormula_finOmega_atom_finCofin ψ with hψ | hψ
      · exact Or.inl (hψ.subset fun _ hx => hx.2)
      · refine Or.inr ?_
        have hsub :
            ({n : Nat | FinOmegaCarrier.atom n ∈
              evalClassFormula finOmegaBase (.inter φ ψ)})ᶜ ⊆
              ({n : Nat | FinOmegaCarrier.atom n ∈ evalClassFormula finOmegaBase φ})ᶜ ∪
                ({n : Nat | FinOmegaCarrier.atom n ∈ evalClassFormula finOmegaBase ψ})ᶜ := by
          intro n hn
          change ¬ (FinOmegaCarrier.atom n ∈ evalClassFormula finOmegaBase φ ∧
            FinOmegaCarrier.atom n ∈ evalClassFormula finOmegaBase ψ) at hn
          by_cases h1 : FinOmegaCarrier.atom n ∈ evalClassFormula finOmegaBase φ
          · exact Or.inr fun h2 => hn ⟨h1, h2⟩
          · exact Or.inl h1
        exact (hφ.union hψ).subset hsub

theorem satisfiesSubclassSeparation_finOmegaModel :
    SatisfiesSubclassSeparation finOmegaModel := by
  rintro C ⟨φ, rfl⟩ ⟨a, hbound⟩
  let A : Set Nat := {n : Nat | FinOmegaCarrier.atom n ∈ evalClassFormula finOmegaBase φ}
  refine ⟨.set ⟨A, evalClassFormula_finOmega_atom_finCofin φ⟩, ?_⟩
  intro x
  cases x with
  | atom n => rfl
  | set S =>
    constructor
    · intro hmem
      cases hmem
    · intro hx
      have hba := hbound (.set S) hx
      cases a <;> cases hba

theorem satisfiesSubclassSeparation_powOmegaModel :
    SatisfiesSubclassSeparation powOmegaModel := by
  rintro D _ ⟨a, hbound⟩
  refine ⟨.set {n : Nat | PowOmegaCarrier.atom n ∈ D}, ?_⟩
  intro x
  cases x with
  | atom n => rfl
  | set S =>
    constructor
    · intro hmem
      cases hmem
    · intro hx
      have hba := hbound (.set S) hx
      cases a <;> cases hba

/-- The set `{n | n % 2 = 0}` of even natural numbers. -/
def evenNatSet : Set Nat := {n : Nat | n % 2 = 0}

theorem evenNatSet_infinite : Set.Infinite evenNatSet := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : Nat => 2 * k) ?_ ?_
  · intro a b hab; dsimp at hab; omega
  · intro k; change (2 * k) % 2 = 0; omega

theorem oddNatSet_infinite : Set.Infinite evenNatSetᶜ := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : Nat => 2 * k + 1) ?_ ?_
  · intro a b hab; dsimp at hab; omega
  · intro k; change ¬ ((2 * k + 1) % 2 = 0); omega

/-- Definable class in `powOmegaModel` representing all even natural numbers. -/
def evenPowClass : Set PowOmegaCarrier :=
  evalClassFormula powOmegaBase (.memParam (.set evenNatSet))

theorem evalClassFormula_finOmega_eq_preimage :
    ∀ φ : ParamClassFormula FinOmegaCarrier,
      evalClassFormula finOmegaBase φ =
        finToPow ⁻¹' evalClassFormula powOmegaBase (φ.map finToPow)
  | .eqParam p => by
    ext x
    simp [evalClassFormula, ParamClassFormula.map, finToPow_injective.eq_iff]
  | .memParam p => by
    ext x
    exact finToPow_mem_iff x p
  | .compl φ => by
    ext x
    simp [evalClassFormula, ParamClassFormula.map, evalClassFormula_finOmega_eq_preimage φ]
  | .inter φ ψ => by
    ext x
    simp [evalClassFormula, ParamClassFormula.map,
      evalClassFormula_finOmega_eq_preimage φ, evalClassFormula_finOmega_eq_preimage ψ]

private def finFormulaParamList : ParamClassFormula FinOmegaCarrier → List (Set Nat)
  | .eqParam (.set S) => [S.1]
  | .eqParam (.atom _) => []
  | .memParam _ => []
  | .compl φ => finFormulaParamList φ
  | .inter φ ψ => finFormulaParamList φ ++ finFormulaParamList ψ

private noncomputable def finFormulaSingletonBound : List (Set Nat) → Nat
  | [] => 0
  | T :: ts =>
    letI := Classical.propDecidable
    Nat.max (if h : ∃ n : Nat, T = {n} then h.choose + 1 else 0) (finFormulaSingletonBound ts)

private theorem singleton_lt_bound_of_mem :
    ∀ {L : List (Set Nat)} {n : Nat}, ({n} : Set Nat) ∈ L → n < finFormulaSingletonBound L
  | [], _, h => by cases h
  | T :: ts, n, h => by
    rcases List.mem_cons.mp h with hEq | hTail
    · have hex : ∃ k : Nat, T = {k} := ⟨n, hEq.symm⟩
      dsimp only [finFormulaSingletonBound]
      rw [dif_pos hex]
      have hkn : hex.choose = n := by
        have h1 : ({hex.choose} : Set Nat) = {n} := hex.choose_spec.symm.trans hEq.symm
        exact Set.mem_singleton_iff.mp (h1 ▸ Set.mem_singleton hex.choose)
      rw [← hkn]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · dsimp only [finFormulaSingletonBound]
      have hlt := singleton_lt_bound_of_mem hTail
      exact Nat.lt_of_lt_of_le hlt (Nat.le_max_right _ _)

private def evalUnmatchedSet : ParamClassFormula FinOmegaCarrier → Bool
  | .eqParam _ => false
  | .memParam _ => false
  | .compl φ => !evalUnmatchedSet φ
  | .inter φ ψ => evalUnmatchedSet φ && evalUnmatchedSet ψ

private theorem set_mem_finOmega_iff_evalUnmatched (φ : ParamClassFormula FinOmegaCarrier)
    (T : {A : Set Nat // A.Finite ∨ Aᶜ.Finite}) (hT : T.1 ∉ finFormulaParamList φ) :
    FinOmegaCarrier.set T ∈ evalClassFormula finOmegaBase φ ↔ evalUnmatchedSet φ = true := by
  induction φ with
  | eqParam p =>
    cases p with
    | atom _ => simp [evalClassFormula, evalUnmatchedSet]
    | set S =>
      simp only [evalClassFormula, evalUnmatchedSet, Bool.false_eq_true, iff_false]
      intro h
      exact hT (List.mem_singleton.mpr (congrArg Subtype.val (FinOmegaCarrier.set.inj h)))
  | memParam p =>
    cases p <;> simp [evalClassFormula, evalUnmatchedSet, finOmegaBase]
  | compl φ ih =>
    simpa [evalClassFormula, evalUnmatchedSet] using not_congr (ih hT)
  | inter φ ψ ih₁ ih₂ =>
    have h₁ : T.1 ∉ finFormulaParamList φ := fun h => hT (List.mem_append_left _ h)
    have h₂ : T.1 ∉ finFormulaParamList ψ := fun h => hT (List.mem_append_right _ h)
    simp [evalClassFormula, evalUnmatchedSet, ih₁ h₁, ih₂ h₂]

private theorem set_mem_powOmega_iff_evalUnmatched (φ : ParamClassFormula FinOmegaCarrier)
    (T : Set Nat) (hT : T ∉ finFormulaParamList φ) :
    PowOmegaCarrier.set T ∈ evalClassFormula powOmegaBase (φ.map finToPow) ↔
      evalUnmatchedSet φ = true := by
  induction φ with
  | eqParam p =>
    cases p with
    | atom _ => simp [evalClassFormula, ParamClassFormula.map, finToPow, evalUnmatchedSet]
    | set S =>
      simp only [evalClassFormula, ParamClassFormula.map, finToPow, evalUnmatchedSet,
        Bool.false_eq_true, iff_false]
      intro h
      exact hT (List.mem_singleton.mpr (PowOmegaCarrier.set.inj h))
  | memParam p =>
    cases p <;> simp [evalClassFormula, ParamClassFormula.map, finToPow, powOmegaBase,
      evalUnmatchedSet]
  | compl φ ih =>
    simpa [evalClassFormula, ParamClassFormula.map, evalUnmatchedSet] using not_congr (ih hT)
  | inter φ ψ ih₁ ih₂ =>
    have h₁ : T ∉ finFormulaParamList φ := fun h => hT (List.mem_append_left _ h)
    have h₂ : T ∉ finFormulaParamList ψ := fun h => hT (List.mem_append_right _ h)
    simp [evalClassFormula, ParamClassFormula.map, evalUnmatchedSet, ih₁ h₁, ih₂ h₂]

private theorem exists_finOmega_witness_for_formula_eq (φ : ParamClassFormula FinOmegaCarrier)
    {T : Set Nat} (hT : T ∈ finFormulaParamList φ) :
    ∃ x : FinOmegaCarrier, finToPow x = PowOmegaCarrier.set T := by
  induction φ with
  | eqParam p =>
    cases p with
    | atom _ => simp [finFormulaParamList] at hT
    | set S =>
      rw [finFormulaParamList, List.mem_singleton] at hT
      exact ⟨.set S, by simp [finToPow, hT]⟩
  | memParam _ => simp [finFormulaParamList] at hT
  | compl φ ih => exact ih hT
  | inter φ ψ ih₁ ih₂ =>
    rw [finFormulaParamList, List.mem_append] at hT
    rcases hT with h | h
    · exact ih₁ h
    · exact ih₂ h

/-- Upgrade of `finToPow : finOmegaBase → powOmegaBase` to a full `SetElemHom`, proving
extensional `ParamClassFormula` elementarity (`elem_ext`) between `finOmegaBase` and `powOmegaBase`.
Note: only parameters `φ, ψ` coming from `FinOmegaCarrier` (finite/cofinite sets of atoms) are
permitted in `SetElemHom`, so any new infinite-coinfinite subset of `ℕ` satisfies the same unmatched
Boolean parity `evalUnmatchedSet` as an unmentioned singleton `{N} ∈ finOmegaBase`. -/
noncomputable def finToPowElemHom : SetElemHom finOmegaBase powOmegaBase where
  toFun := finToPow
  mem_iff := finToPow_mem_iff
  elem_ext φ ψ hEq := by
    let N : Nat := finFormulaSingletonBound (finFormulaParamList φ ++ finFormulaParamList ψ)
    have hNNotMem : ({N} : Set Nat) ∉ finFormulaParamList φ ++ finFormulaParamList ψ := by
      intro hmem
      have hlt := singleton_lt_bound_of_mem hmem
      omega
    have hNPhi : ({N} : Set Nat) ∉ finFormulaParamList φ :=
      fun h => hNNotMem (List.mem_append_left _ h)
    have hNPsi : ({N} : Set Nat) ∉ finFormulaParamList ψ :=
      fun h => hNNotMem (List.mem_append_right _ h)
    let z₀ : FinOmegaCarrier := .set ⟨{N}, Or.inl (Set.finite_singleton N)⟩
    have hUnmatched : evalUnmatchedSet φ = evalUnmatchedSet ψ := by
      have hz := congrArg (fun S : Set FinOmegaCarrier => z₀ ∈ S) hEq
      have hL :=
        (set_mem_finOmega_iff_evalUnmatched φ ⟨{N}, Or.inl (Set.finite_singleton N)⟩ hNPhi).mp
      have hR :=
        (set_mem_finOmega_iff_evalUnmatched ψ ⟨{N}, Or.inl (Set.finite_singleton N)⟩ hNPsi).mp
      have hEquiv : evalUnmatchedSet φ = true ↔ evalUnmatchedSet ψ = true := by
        constructor
        · intro h
          exact hR (hz.mp
            ((set_mem_finOmega_iff_evalUnmatched φ
              ⟨{N}, Or.inl (Set.finite_singleton N)⟩ hNPhi).mpr h))
        · intro h
          exact hL (hz.mpr
            ((set_mem_finOmega_iff_evalUnmatched ψ
              ⟨{N}, Or.inl (Set.finite_singleton N)⟩ hNPsi).mpr h))
      cases hb₁ : evalUnmatchedSet φ <;> cases hb₂ : evalUnmatchedSet ψ <;> simp_all
    have hPreimage :
        finToPow ⁻¹' evalClassFormula powOmegaBase (φ.map finToPow) =
          finToPow ⁻¹' evalClassFormula powOmegaBase (ψ.map finToPow) := by
      simpa [← evalClassFormula_finOmega_eq_preimage] using hEq
    ext y
    cases y with
    | atom n =>
      exact iff_of_eq (congrArg (fun S => FinOmegaCarrier.atom n ∈ S) hPreimage)
    | set T =>
      by_cases hT : T ∈ finFormulaParamList φ ∨ T ∈ finFormulaParamList ψ
      · have hex : ∃ x : FinOmegaCarrier, finToPow x = PowOmegaCarrier.set T := by
          rcases hT with h | h
          · exact exists_finOmega_witness_for_formula_eq φ h
          · exact exists_finOmega_witness_for_formula_eq ψ h
        rcases hex with ⟨x, hx⟩
        rw [← hx]
        exact iff_of_eq (congrArg (fun S => x ∈ S) hPreimage)
      · rw [not_or] at hT
        rw [set_mem_powOmega_iff_evalUnmatched φ T hT.1,
          set_mem_powOmega_iff_evalUnmatched ψ T hT.2, hUnmatched]

/-- Induced `ClassSetModel` morphism `finOmegaModel ⟶ powOmegaModel` over `finToPowElemHom` via
`Def : SetStructure ⥤ ClassSetModel`. -/
noncomputable def finToPowClassHom : finOmegaModel ⟶ powOmegaModel :=
  defMap finToPowElemHom

/-- Naive pullback class expansion of `finOmegaBase` adjoining `finToPow ⁻¹' D` for every
class `D` of `powOmegaModel`. -/
def naivePullbackModel : ClassSetModel.{0} where
  base := finOmegaBase
  IsClass S := ∃ D : Set PowOmegaCarrier, powOmegaModel.IsClass D ∧ S = finToPow ⁻¹' D
  def_mem φ := ⟨evalClassFormula powOmegaBase (φ.map finToPow),
    powOmegaModel.def_mem (φ.map finToPow), evalClassFormula_finOmega_eq_preimage φ⟩
  compl_mem := fun ⟨D, hD, hS⟩ => ⟨Dᶜ, powOmegaModel.compl_mem hD, by simp [hS]⟩
  inter_mem := fun ⟨D₁, hD₁, hS₁⟩ ⟨D₂, hD₂, hS₂⟩ =>
    ⟨D₁ ∩ D₂, powOmegaModel.inter_mem hD₁ hD₂, by simp [hS₁, hS₂]⟩

/-- Definition `def:set-projection-fibration`(i) obstruction: naive pullback `f⁻¹[D]` of a
definable class `D` from a `SatisfiesSubclassSeparation` ambient model `powOmegaModel` along an
`∈`-preserving embedding `finToPow : finOmegaModel ↪ powOmegaModel` yields a bounded subclass of
`omegaFinSet` with no representing set in `finOmegaModel`, so `naivePullbackModel` refutes
`SatisfiesSubclassSeparation`. -/
theorem naive_pullback_breaks_subclass_separation :
    SatisfiesSubclassSeparation finOmegaModel ∧
      SatisfiesSubclassSeparation powOmegaModel ∧
      Function.Injective finToPow ∧
      (∀ x y : FinOmegaCarrier,
        finOmegaBase.mem x y ↔ powOmegaBase.mem (finToPow x) (finToPow y)) ∧
      powOmegaModel.IsClass evenPowClass ∧
      (∀ x ∈ finToPow ⁻¹' evenPowClass, finOmegaBase.mem x omegaFinSet) ∧
      (¬ ∃ b : FinOmegaCarrier,
        ∀ x : FinOmegaCarrier, finOmegaBase.mem x b ↔ x ∈ finToPow ⁻¹' evenPowClass) ∧
      ¬ SatisfiesSubclassSeparation naivePullbackModel := by
  have hEvenClass : powOmegaModel.IsClass evenPowClass :=
    powOmegaModel.def_mem (.memParam (.set evenNatSet))
  have hBound : ∀ x ∈ finToPow ⁻¹' evenPowClass, finOmegaBase.mem x omegaFinSet := by
    intro x hx
    cases x with
    | atom n => exact Set.mem_univ n
    | set S => cases hx
  have hNoSet : ¬ ∃ b : FinOmegaCarrier,
      ∀ x : FinOmegaCarrier, finOmegaBase.mem x b ↔ x ∈ finToPow ⁻¹' evenPowClass := by
    rintro ⟨b, hb⟩
    cases b with
    | atom m =>
      have h0 : FinOmegaCarrier.atom 0 ∈ finToPow ⁻¹' evenPowClass := by
        change (0 : Nat) % 2 = 0
        omega
      have hf := (hb (.atom 0)).2 h0
      cases hf
    | set S =>
      have hEq : S.1 = evenNatSet := by
        ext n
        exact hb (.atom n)
      rcases S.2 with hfin | hcofin
      · rw [hEq] at hfin
        exact evenNatSet_infinite hfin
      · rw [hEq] at hcofin
        exact oddNatSet_infinite hcofin
  refine ⟨satisfiesSubclassSeparation_finOmegaModel, satisfiesSubclassSeparation_powOmegaModel,
    finToPow_injective, finToPow_mem_iff, hEvenClass, hBound, hNoSet, ?_⟩
  intro hSep
  exact hNoSet (hSep (finToPow ⁻¹' evenPowClass) ⟨evenPowClass, hEvenClass, rfl⟩
    ⟨omegaFinSet, hBound⟩)

/-! ## Section 2: Large Equivalence-Splitting & Global Choice (`prop:large-equiv-splitting`) -/

/-- An abstract skeletal cardinal system over `Type u`: assigns to every small type `X : Type u` a
canonical cardinal representative `incl (cardOf X) : Type u` that is equipollent to `X`, together
with a distinguished zero element (`∅ ∈ |X|`) on every inhabited cardinal carrier. -/
structure SkeletalCardBase : Type (max (u + 1) (v + 1)) where
  Card : Type v
  incl : Card → Type u
  cardOf : Type u → Card
  card_bij : ∀ X : Type u, Nonempty (X ≃ incl (cardOf X))
  skel_zero : ∀ c : Card, Nonempty (incl c) → incl c

/-- Pointwise homotopy-functorial quasi-inverse splitting of `incl : Card ↪ Type u`. Formulated
pointwise (`∀ z, ...` and `∀ x, ...`) using raw `Equiv.toFun` / `Equiv.invFun` fields so that
functoriality and naturality avoid `DFunLike`'s `funext` (`Quot.sound`) dependency. -/
structure CardQuasiInverse (M : SkeletalCardBase.{u, v}) : Type (max (u + 1) v) where
  obj : Type u → M.Card
  map : ∀ {X Y : Type u}, (X → Y) → (M.incl (obj X) → M.incl (obj Y))
  eta : ∀ X : Type u, X ≃ M.incl (obj X)
  map_id : ∀ (X : Type u) (z : M.incl (obj X)), map (@id X) z = z
  map_comp : ∀ {X Y Z : Type u} (f : X → Y) (g : Y → Z) (z : M.incl (obj X)),
    map (g ∘ f) z = map g (map f z)
  naturality : ∀ {X Y : Type u} (f : X → Y) (x : X),
    map f ((eta X).toFun x) = (eta Y).toFun (f x)

/-- Existence of a pointwise homotopy-functorial quasi-inverse to `Card ↪ Type u`. -/
def HomotopyCardSplitting (M : SkeletalCardBase.{u, v}) : Prop :=
  Nonempty (CardQuasiInverse M)

/-- Uniform small-set Global Choice on `Type u`, selecting an element of every nonempty
`X : Type u`. -/
def UniformSmallChoice : Prop :=
  Nonempty (∀ X : Type u, Nonempty X → X)

/-- Proposition `prop:large-equiv-splitting`(ii) *(axiom-free kernel core)*: over any skeletal
cardinal base `M`, splitting the weak equivalence `Card ↪ Set` via a pointwise homotopy-functorial
quasi-inverse is strictly equivalent to uniform small-set Global Choice `G(X) = η_X⁻¹(∅)`. -/
theorem card_split_iff_global_choice (M : SkeletalCardBase.{u, v}) :
    HomotopyCardSplitting M ↔ UniformSmallChoice.{u} := by
  constructor
  · rintro ⟨Q⟩
    refine ⟨fun X hX => (Q.eta X).invFun (M.skel_zero (Q.obj X) ?_)⟩
    exact let ⟨x⟩ := hX; ⟨(Q.eta X).toFun x⟩
  · rintro ⟨G⟩
    let chosenEta : ∀ X : Type u, X ≃ M.incl (M.cardOf X) :=
      fun X => G (X ≃ M.incl (M.cardOf X)) (M.card_bij X)
    refine ⟨{
      obj := M.cardOf
      map := fun {X Y} f z => (chosenEta Y).toFun (f ((chosenEta X).invFun z))
      eta := chosenEta
      map_id := fun X z => (chosenEta X).right_inv z
      map_comp := fun {X Y Z} f g z =>
        congrArg (chosenEta Z).toFun
          (congrArg g ((chosenEta Y).left_inv (f ((chosenEta X).invFun z)))).symm
      naturality := fun {X Y} f x =>
        congrArg (chosenEta Y).toFun (congrArg f ((chosenEta X).left_inv x))
    }⟩

/-- Von Neumann initial-ordinal realization of `SkeletalCardBase` over `Type u`, using
`Cardinal.ord c` and well-founded minimum `WellFounded.min` for `∅ ∈ |X|`. -/
noncomputable def vonNeumannCardBase : SkeletalCardBase.{u, u + 1} where
  Card := Cardinal.{u}
  incl c := c.ord.ToType
  cardOf X := Cardinal.mk X
  card_bij X := by
    have hcard : Cardinal.mk (Cardinal.mk X).ord.ToType = Cardinal.mk X := by
      rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact Cardinal.eq.1 hcard.symm
  skel_zero c hc :=
    (wellFounded_lt (α := c.ord.ToType)).min Set.univ ⟨hc.some, trivial⟩

/-- Proposition `prop:large-equiv-splitting` + `CategoryTheory.Functor`: using `Classical.choice`,
`Type u` admits both a genuine `CategoryTheory.Functor` skeletal equivalence splitting
`toSkeletonFunctor (Type u) : Type u ⥤ Skeleton (Type u)` with natural isomorphism
`𝟭 (Type u) ≅ toSkeletonFunctor (Type u) ⋙ fromSkeleton (Type u)` and uniform global choice
splitting `vonNeumannCardBase`. -/
theorem type_equiv_splitting_global_choice :
    IsSkeletonOf (Type u) (Skeleton (Type u)) (fromSkeleton (Type u)) ∧
      (∃ F : Type u ⥤ Skeleton (Type u), Nonempty (𝟭 (Type u) ≅ F ⋙ fromSkeleton (Type u))) ∧
      HomotopyCardSplitting vonNeumannCardBase.{u} ∧
      UniformSmallChoice.{u} := by
  have hChoice : UniformSmallChoice.{u} := ⟨fun _ hX => Classical.choice hX⟩
  refine ⟨skeleton_isSkeleton (Type u), ?_, (card_split_iff_global_choice _).2 hChoice, hChoice⟩
  exact ⟨toSkeletonFunctor (Type u), ⟨(skeletonEquivalence (Type u)).counitIso.symm⟩⟩

/-! ## Section 3: Accessible Pointed Graphs (`APG`), `PSet` Monomorphism, & `quine_atom_outside_wf`
-/

/-- A small pointed directed graph `(V, →, root)` modeling an `S`-small coalgebra for the covariant
powerset functor `P_S` in Aczel's Anti-Foundation semantics (`thm:axis-vii-foundation`). -/
structure APG : Type (u + 1) where
  V : Type u
  edge : V → V → Prop
  root : V

namespace APG

/-- A relation `R : G₁.V → G₂.V → Prop` is a graph bisimulation if it satisfies the back-and-forth
zigzag conditions along directed edges. -/
structure IsBisim (G₁ G₂ : APG.{u}) (R : G₁.V → G₂.V → Prop) : Prop where
  forth : ∀ {u₁ v₁ : G₁.V} {u₂ : G₂.V},
    R u₁ u₂ → G₁.edge u₁ v₁ → ∃ v₂ : G₂.V, G₂.edge u₂ v₂ ∧ R v₁ v₂
  back : ∀ {u₁ : G₁.V} {u₂ v₂ : G₂.V},
    R u₁ u₂ → G₂.edge u₂ v₂ → ∃ v₁ : G₁.V, G₁.edge u₁ v₁ ∧ R v₁ v₂

/-- Two pointed graphs are bisimilar if some bisimulation relates their roots. -/
def Bisimilar (G₁ G₂ : APG.{u}) : Prop :=
  ∃ R : G₁.V → G₂.V → Prop, IsBisim G₁ G₂ R ∧ R G₁.root G₂.root

theorem Bisimilar.refl (G : APG.{u}) : Bisimilar G G :=
  ⟨Eq, ⟨by rintro u v _ rfl h; exact ⟨v, h, rfl⟩,
        by rintro u _ w rfl h; exact ⟨w, h, rfl⟩⟩, rfl⟩

theorem Bisimilar.symm {G₁ G₂ : APG.{u}} : Bisimilar G₁ G₂ → Bisimilar G₂ G₁ := by
  rintro ⟨R, ⟨hf, hb⟩, hr⟩
  exact ⟨fun u₂ u₁ => R u₁ u₂, ⟨fun hRu he => hb hRu he, fun hRu he => hf hRu he⟩, hr⟩

theorem Bisimilar.trans {G₁ G₂ G₃ : APG.{u}} :
    Bisimilar G₁ G₂ → Bisimilar G₂ G₃ → Bisimilar G₁ G₃ := by
  rintro ⟨R₁, h₁, hr₁⟩ ⟨R₂, h₂, hr₂⟩
  refine ⟨fun u₁ u₃ => ∃ u₂, R₁ u₁ u₂ ∧ R₂ u₂ u₃, ⟨?_, ?_⟩, ⟨G₂.root, hr₁, hr₂⟩⟩
  · rintro u₁ v₁ u₃ ⟨u₂, hR₁, hR₂⟩ he₁
    obtain ⟨v₂, he₂, hR₁'⟩ := h₁.forth hR₁ he₁
    obtain ⟨v₃, he₃, hR₂'⟩ := h₂.forth hR₂ he₂
    exact ⟨v₃, he₃, ⟨v₂, hR₁', hR₂'⟩⟩
  · rintro u₁ u₃ v₃ ⟨u₂, hR₁, hR₂⟩ he₃
    obtain ⟨v₂, he₂, hR₂'⟩ := h₂.back hR₂ he₃
    obtain ⟨v₁, he₁, hR₁'⟩ := h₁.back hR₁ he₂
    exact ⟨v₁, he₁, ⟨v₂, hR₁', hR₂'⟩⟩

/-- Pointed graph isomorphism (`Iso_∈` on transitive closures in Proposition `prop:boffa-torsors`),
using `.toFun` explicitly to avoid `DFunLike`'s `funext` (`Quot.sound`) footprint. -/
structure Iso (G₁ G₂ : APG.{u}) : Type u where
  toEquiv : G₁.V ≃ G₂.V
  map_root : toEquiv.toFun G₁.root = G₂.root
  map_edge : ∀ u v : G₁.V, G₁.edge u v ↔ G₂.edge (toEquiv.toFun u) (toEquiv.toFun v)

end APG

/-- Inductive edge relation on the tree unfolding `PUnit ⊕ Σ a, (child a).V` of a `PSet`, defined
purely inductively so that structural recursion requires zero axioms. -/
inductive PSetTreeEdge {α : Type u} (child : α → APG.{u}) :
    Sum PUnit.{u + 1} (Σ a : α, (child a).V) →
    Sum PUnit.{u + 1} (Σ a : α, (child a).V) → Prop
  | root_to_child (a : α) :
      PSetTreeEdge child (Sum.inl PUnit.unit) (Sum.inr ⟨a, (child a).root⟩)
  | child_step (a : α) {u v : (child a).V} :
      (child a).edge u v → PSetTreeEdge child (Sum.inr ⟨a, u⟩) (Sum.inr ⟨a, v⟩)

/-- Structural embedding `κ_Reg : PSet.{u} → APG.{u}` unfolding each well-founded pre-set into its
accessible pointed membership tree via `PSet.rec` *(axiom-free)*. -/
def psetToAPG : PSet.{u} → APG.{u}
  | PSet.mk α A =>
    let child := fun a => psetToAPG (A a)
    { V := Sum PUnit.{u + 1} (Σ a : α, (child a).V)
      edge := PSetTreeEdge child
      root := Sum.inl PUnit.unit }

/-- The one-vertex self-loop pointed coalgebra `quineAPG` (`q = {q}`) representing Aczel's unique
Quine atom in `ν P_S`. -/
def quineAPG : APG.{u} where
  V := PUnit.{u + 1}
  edge _ _ := True
  root := PUnit.unit

/-- Theorem `thm:axis-vii-foundation`(iii) *(axiom-free)*: the Quine self-loop coalgebra `quineAPG`
(`q = {q}`) lies strictly outside the well-founded image of `PSet.{u}` under bisimulation. -/
theorem quine_atom_outside_wf (x : PSet.{u}) :
    ¬ APG.Bisimilar (psetToAPG x) quineAPG.{u} := by
  induction x with
  | mk α A ih =>
    rintro ⟨R, hBisim, hRoot⟩
    obtain ⟨v₁, hvEdge, hvRel⟩ := hBisim.back hRoot trivial
    cases hvEdge with
    | root_to_child a =>
      apply ih a
      refine ⟨fun u w => R (Sum.inr ⟨a, u⟩) w, ⟨?_, ?_⟩, hvRel⟩
      · intro u₁ u₂ w hRu he
        exact hBisim.forth hRu (PSetTreeEdge.child_step a he)
      · intro u₁ w₁ w₂ hRu he
        obtain ⟨z, hzEdge, hzRel⟩ := hBisim.back hRu he
        cases hzEdge with
        | child_step _ heChild => exact ⟨_, heChild, hzRel⟩

/-- Inductive node-level bisimulation witnessing
`PSet.Equiv x y → APG.Bisimilar (psetToAPG x) (psetToAPG y)`. -/
inductive PSetEquivBisimRel :
    ∀ {x y : PSet.{u}}, (psetToAPG x).V → (psetToAPG y).V → Prop
  | roots {α β : Type u} {A : α → PSet.{u}} {B : β → PSet.{u}}
      (h : PSet.Equiv (PSet.mk α A) (PSet.mk β B)) :
      PSetEquivBisimRel (x := PSet.mk α A) (y := PSet.mk β B)
        (Sum.inl PUnit.unit) (Sum.inl PUnit.unit)
  | step {α β : Type u} {A : α → PSet.{u}} {B : β → PSet.{u}}
      (a : α) (b : β) {u : (psetToAPG (A a)).V} {v : (psetToAPG (B b)).V} :
      PSetEquivBisimRel (x := A a) (y := B b) u v →
      PSetEquivBisimRel (x := PSet.mk α A) (y := PSet.mk β B)
        (Sum.inr ⟨a, u⟩) (Sum.inr ⟨b, v⟩)

theorem psetEquivBisimRel_isBisim (x y : PSet.{u}) :
    APG.IsBisim (psetToAPG x) (psetToAPG y) (PSetEquivBisimRel (x := x) (y := y)) := by
  refine ⟨?_, ?_⟩
  · intro u₁ v₁ u₂ hRel hEdge
    induction hRel with
    | @roots α β A B hEqv =>
      cases hEdge with
      | root_to_child a =>
        obtain ⟨b, hab⟩ := hEqv.1 a
        have hSub : PSetEquivBisimRel (x := A a) (y := B b)
            (psetToAPG (A a)).root (psetToAPG (B b)).root := by
          cases hAa : A a with
          | mk α' A' =>
            cases hBb : B b with
            | mk β' B' =>
              rw [hAa, hBb] at hab
              exact PSetEquivBisimRel.roots hab
        exact ⟨Sum.inr ⟨b, (psetToAPG (B b)).root⟩,
          PSetTreeEdge.root_to_child b, PSetEquivBisimRel.step a b hSub⟩
    | @step α β A B a b u v _ ih =>
      cases hEdge with
      | child_step _ he =>
        obtain ⟨v', he', hRel'⟩ := ih he
        exact ⟨Sum.inr ⟨b, v'⟩, PSetTreeEdge.child_step b he', PSetEquivBisimRel.step a b hRel'⟩
  · intro u₁ u₂ v₂ hRel hEdge
    induction hRel with
    | @roots α β A B hEqv =>
      cases hEdge with
      | root_to_child b =>
        obtain ⟨a, hab⟩ := hEqv.2 b
        have hSub : PSetEquivBisimRel (x := A a) (y := B b)
            (psetToAPG (A a)).root (psetToAPG (B b)).root := by
          cases hAa : A a with
          | mk α' A' =>
            cases hBb : B b with
            | mk β' B' =>
              rw [hAa, hBb] at hab
              exact PSetEquivBisimRel.roots hab
        exact ⟨Sum.inr ⟨a, (psetToAPG (A a)).root⟩,
          PSetTreeEdge.root_to_child a, PSetEquivBisimRel.step a b hSub⟩
    | @step α β A B a b u v _ ih =>
      cases hEdge with
      | child_step _ he =>
        obtain ⟨u', he', hRel'⟩ := ih he
        exact ⟨Sum.inr ⟨a, u'⟩, PSetTreeEdge.child_step a he', PSetEquivBisimRel.step a b hRel'⟩

/-- Theorem `thm:axis-vii-foundation`(iii) monomorphism property *(axiom-free)*: extensional
equivalence `PSet.Equiv x y` coincides with `APG.Bisimilar (psetToAPG x) (psetToAPG y)`, so
`ZFSet` (`μ P_S`) embeds faithfully into coalgebra bisimulation classes (`ν P_S`). -/
theorem pset_equiv_iff_bisimilar (x y : PSet.{u}) :
    PSet.Equiv x y ↔ APG.Bisimilar (psetToAPG x) (psetToAPG y) := by
  constructor
  · intro h
    cases x with
    | mk α A =>
      cases y with
      | mk β B =>
        exact ⟨PSetEquivBisimRel, psetEquivBisimRel_isBisim _ _, PSetEquivBisimRel.roots h⟩
  · induction x generalizing y with
    | mk α A ih =>
      cases y with
      | mk β B =>
        rintro ⟨R, hBisim, hRoot⟩
        refine ⟨fun a => ?_, fun b => ?_⟩
        · obtain ⟨v₂, hvEdge, hvRel⟩ :=
            hBisim.forth hRoot (PSetTreeEdge.root_to_child a)
          cases hvEdge with
          | root_to_child b =>
            refine ⟨b, ih a (B b) ⟨fun u v => R (Sum.inr ⟨a, u⟩) (Sum.inr ⟨b, v⟩), ⟨?_, ?_⟩, hvRel⟩⟩
            · intro u₁ u₂ w hRu he
              obtain ⟨z, hzEdge, hzRel⟩ :=
                hBisim.forth hRu (PSetTreeEdge.child_step a he)
              cases hzEdge with
              | child_step _ he' => exact ⟨_, he', hzRel⟩
            · intro u₁ w₁ w₂ hRu he
              obtain ⟨z, hzEdge, hzRel⟩ :=
                hBisim.back hRu (PSetTreeEdge.child_step b he)
              cases hzEdge with
              | child_step _ he' => exact ⟨_, he', hzRel⟩
        · obtain ⟨v₁, hvEdge, hvRel⟩ :=
            hBisim.back hRoot (PSetTreeEdge.root_to_child b)
          cases hvEdge with
          | root_to_child a =>
            refine ⟨a, ih a (B b) ⟨fun u v => R (Sum.inr ⟨a, u⟩) (Sum.inr ⟨b, v⟩), ⟨?_, ?_⟩, hvRel⟩⟩
            · intro u₁ u₂ w hRu he
              obtain ⟨z, hzEdge, hzRel⟩ :=
                hBisim.forth hRu (PSetTreeEdge.child_step a he)
              cases hzEdge with
              | child_step _ he' => exact ⟨_, he', hzRel⟩
            · intro u₁ w₁ w₂ hRu he
              obtain ⟨z, hzEdge, hzRel⟩ :=
                hBisim.back hRu (PSetTreeEdge.child_step b he)
              cases hzEdge with
              | child_step _ he' => exact ⟨_, he', hzRel⟩

/-! ## Section 4: Boffa Hypersets & Twin Quine Torsors (`prop:boffa-torsors`) -/

/-- Mutual `2`-cycle pointed graph `u = {v}, v = {u}` (`|V| = 2`), bisimilar to `quineAPG` in
Aczel's `ν P_S` yet non-isomorphic as a pointed `∈`-graph in Boffa's `V_BAFA`. -/
def quineTwoCycleAPG : APG.{0} where
  V := Bool
  edge b₁ b₂ := b₂ = !b₁
  root := false

/-- Proposition `prop:boffa-torsors`(i): `quineAPG` and `quineTwoCycleAPG` are bisimilar yet admit
no pointed graph isomorphism. -/
theorem quineAPG_bisimilar_and_nonIso_twoCycle :
    APG.Bisimilar quineAPG.{0} quineTwoCycleAPG ∧
      IsEmpty (APG.Iso quineAPG.{0} quineTwoCycleAPG) := by
  refine ⟨⟨fun _ _ => True, ⟨?_, ?_⟩, trivial⟩, ⟨fun e => ?_⟩⟩
  · intro _ _ u₂ _ _; exact ⟨!u₂, rfl, trivial⟩
  · intro _ _ _ _ _; exact ⟨PUnit.unit, trivial, trivial⟩
  · have hf : e.toEquiv.toFun (e.toEquiv.invFun false) = false := e.toEquiv.right_inv false
    have ht : e.toEquiv.toFun (e.toEquiv.invFun true) = true := e.toEquiv.right_inv true
    have hunit : e.toEquiv.invFun false = e.toEquiv.invFun true := rfl
    have hft : false = true := hf.symm.trans ((congrArg e.toEquiv.toFun hunit).trans ht)
    cases hft

/-- Ordered distinct twin Quine atom pairs `(a, b)` vs. `(b, a)` over a two-atom support
`Q_2 = {false, true}`. -/
def OrderedTwinPair : Type :=
  { p : Bool × Bool // p.1 ≠ p.2 }

/-- First ordered twin `(a, b)`. -/
def twinAB : OrderedTwinPair := ⟨(false, true), by decide⟩

/-- Swapped ordered twin `(b, a)`. -/
def twinBA : OrderedTwinPair := ⟨(true, false), by decide⟩

/-- Right/left `Bool` (`ℤ/2ℤ` xor) transposition action on `OrderedTwinPair`. -/
def twinSwapAct : Bool → OrderedTwinPair → OrderedTwinPair
  | false, p => p
  | true, ⟨(x, y), h⟩ => ⟨(y, x), fun hyx => h hyx.symm⟩

/-- Proposition `prop:boffa-torsors`(ii) *(axiom-free `Bool` core)*: the swap group `Bool` (`xor`)
acts freely and simply transitively on `OrderedTwinPair`, and admits no swap-fixed point (hence no
equivariant global section over the unordered twin pair `{a, b}`). -/
theorem boffa_twin_torsor :
    (∀ p : OrderedTwinPair, twinSwapAct false p = p) ∧
    (∀ g₁ g₂ : Bool, ∀ p : OrderedTwinPair,
      twinSwapAct (xor g₁ g₂) p = twinSwapAct g₁ (twinSwapAct g₂ p)) ∧
    (∀ g₁ g₂ : Bool, ∀ p : OrderedTwinPair,
      twinSwapAct g₁ p = twinSwapAct g₂ p → g₁ = g₂) ∧
    (∀ p q : OrderedTwinPair, ∃ g : Bool,
      twinSwapAct g p = q ∧ ∀ g' : Bool, twinSwapAct g' p = q → g' = g) ∧
    ¬ ∃ p : OrderedTwinPair, twinSwapAct true p = p := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro g₁ g₂ ⟨⟨x, y⟩, h⟩
    cases g₁ <;> cases g₂ <;> rfl
  · intro g₁ g₂ ⟨⟨x, y⟩, h⟩ heq
    cases g₁ <;> cases g₂
    · rfl
    · exfalso; exact h (congrArg (fun z : OrderedTwinPair => z.1.1) heq)
    · exfalso; exact h (congrArg (fun z : OrderedTwinPair => z.1.1) heq).symm
    · rfl
  · rintro ⟨⟨x₁, y₁⟩, h₁⟩ ⟨⟨x₂, y₂⟩, h₂⟩
    cases x₁ <;> cases y₁ <;> cases x₂ <;> cases y₂
    all_goals
      try (exfalso; apply h₁; rfl)
      try (exfalso; apply h₂; rfl)
    · refine ⟨false, rfl, fun g' hg' => ?_⟩
      cases g'
      · rfl
      · injection hg' with hval; injection hval
    · refine ⟨true, rfl, fun g' hg' => ?_⟩
      cases g'
      · injection hg' with hval; injection hval
      · rfl
    · refine ⟨true, rfl, fun g' hg' => ?_⟩
      cases g'
      · injection hg' with hval; injection hval
      · rfl
    · refine ⟨false, rfl, fun g' hg' => ?_⟩
      cases g'
      · rfl
      · injection hg' with hval; injection hval
  · rintro ⟨⟨⟨x, y⟩, h⟩, hfix⟩
    exact h (congrArg (fun z : OrderedTwinPair => z.1.2) hfix)

/-- Additive `ZMod 2` action on `OrderedTwinPair`. -/
instance instVAddZMod2OrderedTwin : VAdd (ZMod 2) OrderedTwinPair where
  vadd g p := twinSwapAct (decide (g.val = 1)) p

/-- Additive `ZMod 2` subtraction (`vsub`) on `OrderedTwinPair`. -/
instance instVSubZMod2OrderedTwin : VSub (ZMod 2) OrderedTwinPair where
  vsub p q := if p.1.1 = q.1.1 then 0 else 1

/-- Stock `Mathlib` `AddTorsor (ZMod 2) OrderedTwinPair` instance (Choice-free). -/
instance instAddTorsorZMod2OrderedTwin : AddTorsor (ZMod 2) OrderedTwinPair where
  nonempty := ⟨twinAB⟩
  zero_vadd p := rfl
  add_vadd g₁ g₂ p := by
    match g₁, g₂ with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨0, _⟩, ⟨1, _⟩ => rfl
    | ⟨1, _⟩, ⟨0, _⟩ => rfl
    | ⟨1, _⟩, ⟨1, _⟩ =>
        rcases p with ⟨⟨x, y⟩, h⟩
        rfl
    | ⟨n + 2, hn⟩, _ => exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hn))
    | _, ⟨n + 2, hn⟩ => exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hn))
  vsub_vadd' p q := by
    rcases p with ⟨⟨x₁, y₁⟩, h₁⟩
    rcases q with ⟨⟨x₂, y₂⟩, h₂⟩
    cases x₁ <;> cases y₁ <;> cases x₂ <;> cases y₂ <;>
      first | (exfalso; apply h₁; rfl) | (exfalso; apply h₂; rfl) | rfl
  vadd_vsub' g p := by
    rcases p with ⟨⟨x, y⟩, h⟩
    match g with
    | ⟨0, _⟩ =>
        cases x <;> cases y <;> first | (exfalso; apply h; rfl) | rfl
    | ⟨1, _⟩ =>
        cases x <;> cases y <;> first | (exfalso; apply h; rfl) | rfl
    | ⟨n + 2, hn⟩ =>
        exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hn))

/-- Unordered-pair orbit equivalence relation on `OrderedTwinPair` identifying `(a, b) ~ (b, a)`. -/
def twinOrbitSetoid : Setoid OrderedTwinPair where
  r p q := ∃ g : ZMod 2, g +ᵥ p = q
  iseqv :=
    ⟨fun p => ⟨0, zero_vadd (ZMod 2) p⟩,
     by rintro p q ⟨g, rfl⟩; exact ⟨-g, neg_vadd_vadd g p⟩,
     by rintro p q r ⟨g₁, rfl⟩ ⟨g₂, rfl⟩; exact ⟨g₂ + g₁, add_vadd g₂ g₁ p⟩⟩

/-- Quotient unordered-pair base `[Q_2]^2`. -/
def UnorderedTwinOrbit : Type := Quotient twinOrbitSetoid

/-- Proposition `prop:boffa-torsors`(ii) Layer-3 `AddTorsor (ZMod 2)` & quotient-orbit projection:
`OrderedTwinPair` is a genuine `Mathlib` `AddTorsor (ZMod 2)` whose two distinct ordered twins
collapse to a single unordered orbit via `Quotient.sound` (`[propext, Quot.sound]`, Choice-free)
with nonzero torsor cocycle `(twinBA -ᵥ twinAB) = 1`. -/
theorem boffa_twin_addTorsor :
    Nonempty (AddTorsor (ZMod 2) OrderedTwinPair) ∧
      (Quotient.mk twinOrbitSetoid twinAB = Quotient.mk twinOrbitSetoid twinBA) ∧
      (twinBA -ᵥ twinAB : ZMod 2) = 1 ∧
      ∀ s : UnorderedTwinOrbit → OrderedTwinPair,
        (1 : ZMod 2) +ᵥ s (Quotient.mk twinOrbitSetoid twinAB) ≠
          s (Quotient.mk twinOrbitSetoid twinAB) := by
  refine ⟨⟨inferInstance⟩, Quotient.sound ⟨1, rfl⟩, rfl, fun s hs => ?_⟩
  exact boffa_twin_torsor.2.2.2.2 ⟨s (Quotient.mk twinOrbitSetoid twinAB), hs⟩

/-! ## Section 5: Material Extensionality & `ZFSet` Quotient Gate (`prop:extensionality-truncation`)
-/

/-- Empty pre-set `∅ : PSet.{0}`. -/
def psetEmpty0 : PSet.{0} := PSet.mk PEmpty PEmpty.elim

/-- Singleton-of-empty pre-set `[∅]` (`X₁ = sup(1, const_∅)`). -/
def psetSingleEmpty : PSet.{0} := PSet.mk PUnit (fun _ => psetEmpty0)

/-- Multiplicity-two empty pre-set `[∅, ∅]` (`X₂ = sup(2, const_∅)`). -/
def psetDoubleEmpty : PSet.{0} := PSet.mk Bool (fun _ => psetEmpty0)

/-- Asymmetric two-branch family `false ↦ ∅, true ↦ {∅}` testing branch-swap sensitivity in
`PSet`. -/
def twoPointBranch : Bool → PSet.{0}
  | false => psetEmpty0
  | true => psetSingleEmpty

theorem psetEmpty0_ne_psetSingleEmpty : psetEmpty0 ≠ psetSingleEmpty := by
  intro h
  have hType : PEmpty = PUnit := congrArg PSet.Type h
  exact PEmpty.elim (Eq.mp hType.symm PUnit.unit)

theorem psetDoubleEmpty_ne_psetSingleEmpty : psetDoubleEmpty ≠ psetSingleEmpty := by
  intro h
  have hType : Bool = PUnit := congrArg PSet.Type h
  have ht : Eq.mp hType true = PUnit.unit := rfl
  have hf : Eq.mp hType false = PUnit.unit := rfl
  have hinj : Eq.mp hType true = Eq.mp hType false := ht.trans hf.symm
  have hback := congrArg (Eq.mp hType.symm) hinj
  simp at hback

theorem psetTwoPoint_ne_swapped :
    PSet.mk Bool twoPointBranch ≠ PSet.mk Bool (twoPointBranch ∘ Bool.not) := by
  intro h
  have hFunc : twoPointBranch = (twoPointBranch ∘ Bool.not) :=
    eq_of_heq (PSet.mk.inj h).2
  have hEval : twoPointBranch false = (twoPointBranch ∘ Bool.not) false :=
    congrFun hFunc false
  exact psetEmpty0_ne_psetSingleEmpty hEval

/-- Proposition `prop:extensionality-truncation` (`zfset_ext_quot_gate`): intensional `PSet`
distinguishes both multiplicity (`[∅, ∅] ≠ [∅]`) and `Bool` branch swap, whereas `ZFSet.mk`
(`Quotient.eq` / `Quotient.sound` over `PSet.Equiv`, using only `[propext, Quot.sound]`)
characterizes extensional equality and collapses both multiplicity and arbitrary `α ≃ α` branch
permutations across all universes. -/
theorem zfset_ext_quot_gate :
    (∀ x y : PSet.{u}, ZFSet.mk x = ZFSet.mk y ↔ PSet.Equiv x y) ∧
      psetDoubleEmpty ≠ psetSingleEmpty ∧
      PSet.mk Bool twoPointBranch ≠ PSet.mk Bool (twoPointBranch ∘ Bool.not) ∧
      ZFSet.mk psetDoubleEmpty = ZFSet.mk psetSingleEmpty ∧
      ∀ (α : Type u) (A : α → PSet.{u}) (σ : α ≃ α),
        ZFSet.mk (PSet.mk α (A ∘ σ)) = ZFSet.mk (PSet.mk α A) := by
  refine ⟨fun x y => Quotient.eq (r := PSet.setoid),
    psetDoubleEmpty_ne_psetSingleEmpty, psetTwoPoint_ne_swapped, ?_, ?_⟩
  · exact Quotient.sound
      ⟨fun _ => ⟨PUnit.unit, PSet.Equiv.refl _⟩, fun _ => ⟨false, PSet.Equiv.refl _⟩⟩
  · intro α A σ
    exact Quotient.sound
      ⟨fun a => ⟨σ a, PSet.Equiv.refl _⟩,
       fun a => ⟨σ.symm a, by dsimp; rw [σ.apply_symm_apply]⟩⟩

/-! ## Section 6: Mandatory 4-Layer Definition Check Gate (`namespace Checks`) -/

namespace Checks

/-! ### Layer 1: Carrier Inhabitation (`Nontrivial` witnesses) -/

instance instNontrivialOrderedTwinPair : Nontrivial OrderedTwinPair :=
  ⟨⟨twinAB, twinBA, fun h => by
    have := congrArg (fun z : OrderedTwinPair => z.1.1) h
    cases this⟩⟩

instance instNontrivialAPG0 : Nontrivial APG.{0} :=
  ⟨⟨psetToAPG psetEmpty0, quineAPG.{0}, fun h =>
    quine_atom_outside_wf psetEmpty0 (h ▸ APG.Bisimilar.refl _)⟩⟩

instance instNontrivialPSet0 : Nontrivial PSet.{0} :=
  ⟨⟨psetEmpty0, psetSingleEmpty, psetEmpty0_ne_psetSingleEmpty⟩⟩

instance instNontrivialZFSet0 : Nontrivial ZFSet.{0} :=
  ⟨⟨ZFSet.mk psetEmpty0, ZFSet.mk psetSingleEmpty, fun h => by
    have hEqv : PSet.Equiv psetEmpty0 psetSingleEmpty := Quotient.exact h
    obtain ⟨a, _⟩ := hEqv.2 PUnit.unit
    cases a⟩⟩

noncomputable instance instNontrivialSkeletonType0 : Nontrivial (Skeleton (Type 0)) :=
  ⟨⟨toSkeleton PEmpty, toSkeleton PUnit, fun h => by
    obtain ⟨e⟩ := (toSkeleton_eq_toSkeleton_iff (X := PEmpty) (Y := PUnit)).1 h
    exact PEmpty.elim (e.inv PUnit.unit)⟩⟩

/-! ### Layer 2: Bidirectional Separation (`P X ∧ ¬ P Y`) -/

/-- Predicate `InWFImage G` asserting that a pointed graph is bisimilar to some `PSet`. -/
def InWFImage (G : APG.{0}) : Prop :=
  ∃ x : PSet.{0}, APG.Bisimilar (psetToAPG x) G

theorem layer2_sep_inWFImage :
    InWFImage (psetToAPG psetSingleEmpty) ∧ ¬ InWFImage quineAPG.{0} :=
  ⟨⟨psetSingleEmpty, APG.Bisimilar.refl _⟩, fun ⟨x, hx⟩ => quine_atom_outside_wf x hx⟩

theorem layer2_sep_apg_bisimilar :
    APG.Bisimilar quineAPG.{0} quineTwoCycleAPG ∧
      ¬ APG.Bisimilar (psetToAPG psetEmpty0) quineAPG.{0} :=
  ⟨quineAPG_bisimilar_and_nonIso_twoCycle.1, quine_atom_outside_wf psetEmpty0⟩

theorem layer2_sep_pset_equiv :
    PSet.Equiv psetDoubleEmpty psetSingleEmpty ∧
      ¬ PSet.Equiv psetEmpty0 psetSingleEmpty :=
  ⟨⟨fun _ => ⟨PUnit.unit, PSet.Equiv.refl _⟩, fun _ => ⟨false, PSet.Equiv.refl _⟩⟩,
   fun h => let ⟨a, _⟩ := h.2 PUnit.unit; PEmpty.elim a⟩

theorem layer2_sep_swap_fixedPoint :
    (∃ p : Bool × Bool, (p.2, p.1) = p) ∧
      ¬ (∃ p : OrderedTwinPair, twinSwapAct true p = p) :=
  ⟨⟨(false, false), rfl⟩, boffa_twin_torsor.2.2.2.2⟩

/-- Minimal vs. full powerclass separation over `(ℕ, <)` in the vertical fiber `π_Set⁻¹(M)`:
on a single-element carrier `Unit`, `defModel` equals all subsets, whereas on `Bool`, the
automorphism-invariant empty-membership structure `(Bool, False)` still separates `defModel` from
parameter-free subsets if restricted, and here we separate `defModel`'s class predicate from a
restricted constant-only predicate vs. full `Set` algebra. -/
def fullPowerClassModel (M : SetStructure.{u}) : ClassSetModel.{u} where
  base := M
  IsClass _ := True
  def_mem _ := trivial
  compl_mem _ := trivial
  inter_mem _ _ := trivial

/-- Over `(ℕ, =)` without arbitrary second-order comprehension, `fullPowerClassModel` contains every
subset, whereas we can exhibit an explicit `SetStructure` with two distinct `ClassSetModel` fibers
sharing the exact same `base` when `ParamClassFormula` generates only finite/cofinite sets! -/
def natTrivialSetStructure : SetStructure.{0} where
  Carrier := Nat
  mem _ _ := False

theorem evalClassFormula_natTrivial_finite_or_cofinite :
    ∀ φ : ParamClassFormula natTrivialSetStructure.Carrier,
      (evalClassFormula natTrivialSetStructure φ).Finite ∨
        (evalClassFormula natTrivialSetStructure φ)ᶜ.Finite
  | .eqParam p => Or.inl (Set.finite_singleton p)
  | .memParam _ => Or.inl Set.finite_empty
  | .compl φ => by
      rcases evalClassFormula_natTrivial_finite_or_cofinite φ with h | h
      · exact Or.inr (by simpa [evalClassFormula] using h)
      · exact Or.inl (by simpa [evalClassFormula] using h)
  | .inter φ ψ => by
      rcases evalClassFormula_natTrivial_finite_or_cofinite φ with hφ | hφ
      · exact Or.inl (hφ.subset Set.inter_subset_left)
      · rcases evalClassFormula_natTrivial_finite_or_cofinite ψ with hψ | hψ
        · exact Or.inl (hψ.subset Set.inter_subset_right)
        · refine Or.inr ?_
          change (evalClassFormula natTrivialSetStructure φ ∩
            evalClassFormula natTrivialSetStructure ψ)ᶜ.Finite
          rw [Set.compl_inter]
          exact hφ.union hψ

theorem layer2_sep_vertical_class_fiber :
    let evens : Set Nat := {n | n % 2 = 0}
    (fullPowerClassModel natTrivialSetStructure).IsClass evens ∧
      ¬ (defModel natTrivialSetStructure).IsClass evens := by
  refine ⟨trivial, ?_⟩
  rintro ⟨φ, hφ⟩
  rcases evalClassFormula_natTrivial_finite_or_cofinite φ with hfin | hcofin
  · rw [← hφ] at hfin
    exact evenNatSet_infinite hfin
  · rw [← hφ] at hcofin
    exact oddNatSet_infinite hcofin

theorem layer2_sep_subclass_separation :
    SatisfiesSubclassSeparation finOmegaModel ∧
      ¬ SatisfiesSubclassSeparation naivePullbackModel :=
  ⟨satisfiesSubclassSeparation_finOmegaModel,
    naive_pullback_breaks_subclass_separation.2.2.2.2.2.2.2⟩

/-! ### Layer 3: `mathlib4` Typeclass Projections & Derived Sanity Lemmas -/

example : Category SetStructure.{0} := inferInstance
example : Category ClassSetModel.{0} := inferInstance
noncomputable example : defFunctor.{0} ⊣ piSetFunctor.{0} := defSetProjAdjunction
noncomputable example : Category (Skeleton (Type 0)) := inferInstance
noncomputable example : (fromSkeleton (Type 0)).IsEquivalence := inferInstance
example : Setoid PSet.{0} := inferInstance
example : AddGroup (ZMod 2) := inferInstance
example : AddTorsor (ZMod 2) OrderedTwinPair := inferInstance

theorem derived_def_piSet_coreflection_obj (M : SetStructure.{u}) :
    piSetFunctor.obj (defFunctor.obj M) = M := by
  simp

theorem derived_twin_torsor_order_two (p : OrderedTwinPair) :
    ((1 : ZMod 2) + (1 : ZMod 2)) +ᵥ p = p := by
  have h11 : ((1 : ZMod 2) + (1 : ZMod 2)) = 0 := rfl
  rw [h11, zero_vadd]

theorem derived_double_singleton_apg_bisimilar :
    APG.Bisimilar (psetToAPG psetDoubleEmpty) (psetToAPG psetSingleEmpty) :=
  (pset_equiv_iff_bisimilar psetDoubleEmpty psetSingleEmpty).1 layer2_sep_pset_equiv.1

/-! ### Layer 4: Kernel Axiom Gate (`#guard_msgs in #print axioms`) -/

section KernelAxiomGate

/-- info: 'HomotopyCRM.SetsResiduum.card_split_iff_global_choice' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.card_split_iff_global_choice

/-- info: 'HomotopyCRM.SetsResiduum.type_equiv_splitting_global_choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.type_equiv_splitting_global_choice

/-- info: 'HomotopyCRM.SetsResiduum.quine_atom_outside_wf' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.quine_atom_outside_wf

/-- info: 'HomotopyCRM.SetsResiduum.pset_equiv_iff_bisimilar' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.pset_equiv_iff_bisimilar

/-- info: 'HomotopyCRM.SetsResiduum.quineAPG_bisimilar_and_nonIso_twoCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.quineAPG_bisimilar_and_nonIso_twoCycle

/-- info: 'HomotopyCRM.SetsResiduum.boffa_twin_torsor' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.boffa_twin_torsor

/-- info: 'HomotopyCRM.SetsResiduum.boffa_twin_addTorsor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.boffa_twin_addTorsor

/-- info: 'HomotopyCRM.SetsResiduum.zfset_ext_quot_gate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.zfset_ext_quot_gate

/-- info: 'HomotopyCRM.SetsResiduum.defSetProjAdjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.defSetProjAdjunction

/-- info: 'HomotopyCRM.SetsResiduum.finToPowElemHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.finToPowElemHom

/-- info: 'HomotopyCRM.SetsResiduum.finToPowClassHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.finToPowClassHom

/--
info: 'HomotopyCRM.SetsResiduum.naive_pullback_breaks_subclass_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.naive_pullback_breaks_subclass_separation

/--
info: 'HomotopyCRM.SetsResiduum.Checks.layer2_sep_subclass_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.Checks.layer2_sep_subclass_separation

/-- info: 'HomotopyCRM.SetsResiduum.Checks.layer2_sep_inWFImage' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.Checks.layer2_sep_inWFImage

/-- info: 'HomotopyCRM.SetsResiduum.Checks.layer2_sep_apg_bisimilar' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.Checks.layer2_sep_apg_bisimilar

/-- info: 'HomotopyCRM.SetsResiduum.Checks.layer2_sep_pset_equiv' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.Checks.layer2_sep_pset_equiv

/-- info: 'HomotopyCRM.SetsResiduum.Checks.layer2_sep_swap_fixedPoint' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.Checks.layer2_sep_swap_fixedPoint

/--
info: 'HomotopyCRM.SetsResiduum.Checks.layer2_sep_vertical_class_fiber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.Checks.layer2_sep_vertical_class_fiber

/-- info: 'HomotopyCRM.SetsResiduum.Checks.derived_double_singleton_apg_bisimilar' does not depend on any axioms -/
#guard_msgs in
#print axioms HomotopyCRM.SetsResiduum.Checks.derived_double_singleton_apg_bisimilar

end KernelAxiomGate

end Checks

end HomotopyCRM.SetsResiduum
