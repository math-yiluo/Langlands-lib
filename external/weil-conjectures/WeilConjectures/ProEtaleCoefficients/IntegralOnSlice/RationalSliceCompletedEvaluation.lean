/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.ProEtaleCoefficients.IntegralOnSlice.RationalEvaluationData
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationTranspose

import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement

/-!
# Restriction of completed integral operations and rational evaluation

Source: main-20261015 blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality,
termwise comparison and coefficient unit; Stacks Tags 03DJ, 08JB, 08TC, 099F
(blueprint: lem-sf-rational-slice-completed-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- An index for direct restriction or relocalization; none denotes the ambient site.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def RestrictionArrow (U V : Option X.ProEt) : Type t :=
  match U, V with
  | none, _ => PUnit
  | some _, none => PEmpty
  | some A, some B => B ⟶ A

/-- The module functor is Mathlib's sectionwise restriction with its original ring action.
Source: Stacks 03DH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionModules {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    Mod l E X U ⥤ Mod l E X V :=
  match U, V, a with
  | none, none, _ => 𝟭 _
  | none, some B, _ => SheafOfModules.overFunctor (rings l E X none) B
  | some _, none, a => PEmpty.elim a
  | some _, some _, a => SheafOfModules.overMap (rings l E X none) a

set_option backward.isDefEq.respectTransparency false in
/-- Sectionwise restriction is additive and exact, including relocalization.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation).
Proof: restriction preserves kernels and products sectionwise. Coverings of an object
of an over-site are exactly coverings of its domain with the same structural arrow;
hence local lifts of cokernel sections restrict, proving preservation of cokernels.
Addition is sectionwise. The same argument applies to Over.map and the identity. -/
theorem restrictionModules_exact {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionModules l E X a).Additive ∧
      PreservesFiniteLimits (restrictionModules l E X a) ∧
      PreservesFiniteColimits (restrictionModules l E X a) := by
  cases U with
  | none =>
    cases V with
    | none =>
      change (𝟭 (Mod l E X none)).Additive ∧
        PreservesFiniteLimits (𝟭 (Mod l E X none)) ∧
        PreservesFiniteColimits (𝟭 (Mod l E X none))
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    | some B =>
      exact ⟨SheafOfModules.sitePerfectOverFunctor_additive (rings l E X none) B,
        SheafOfModules.overFunctor_exact_ofUniverses (rings l E X none) B⟩
  | some B =>
    cases V with
    | none => exact PEmpty.elim a
    | some C =>
      exact ⟨SheafOfModules.sitePerfectOverMap_additive (rings l E X none) a,
        SheafOfModules.overMap_exact_ofUniverses (rings l E X none) a⟩

/-- The additive structure supplied by exact sectionwise restriction.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
instance restrictionModulesAdditive {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionModules l E X a).Additive := (restrictionModules_exact l E X a).1

/-- The finite-limit structure supplied by exact sectionwise restriction.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
instance restrictionModulesLimits {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    PreservesFiniteLimits (restrictionModules l E X a) :=
  (restrictionModules_exact l E X a).2.1

/-- The finite-colimit structure supplied by exact sectionwise restriction.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
instance restrictionModulesColimits {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    PreservesFiniteColimits (restrictionModules l E X a) :=
  (restrictionModules_exact l E X a).2.2

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the actual complexes term by term.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionComplex {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    Cx l E X U ⥤ Cx l E X V :=
  (restrictionModules l E X a).mapHomologicalComplex (.up ℤ)

/-- The functor induced by this exact restriction on the existing derived categories.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionDerived {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    D l E X U ⥤ D l E X V := (restrictionModules l E X a).mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- The termwise additive functor remains additive after quasi-isomorphism localization.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation).
Proof: termwise restriction preserves sums of chain maps. The additive localization
universal property descends this identity, equivalently use the derived adjunction
with exact extension by zero. Thus the induced derived functor preserves addition. -/
theorem restrictionDerived_additive {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionDerived l E X a).Additive := by
  change (restrictionModules l E X a).mapDerivedCategory.Additive
  exact Functor.additive_of_preserves_binary_products _

/-- The additive structure from termwise restriction and additive localization.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
instance restrictionDerivedAdditive {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionDerived l E X a).Additive := restrictionDerived_additive l E X a

set_option backward.isDefEq.respectTransparency false in
/-- Comparison data for the actual restriction functor. The generator and two
cone-coordinate equations fix the reduction and Roos comparisons, not just their
isomorphism classes. Completed tensor is tied to these comparisons and ordinary tensor.
Source: Stacks 03DJ, 08JB, 08TC; Bhatt--Scholze 3.4.10
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
structure CompletedRestrictionComparisons {U V : Option X.ProEt}
    (a : RestrictionArrow X U V) where
  /-- Restriction of a flat-term K-flat representative is again such a representative. -/
  good : ∀ P : Cx l E X U, Good l E X U P →
    Good l E X V ((restrictionComplex l E X a).obj P)
  /-- Derived reduction computed on these representatives; scalars are restored by pi_n. -/
  reductionIso : ∀ n : ℕ, level l E X U n ⋙ restrictionComplex l E X a ≅
    restrictionComplex l E X a ⋙ level l E X V n
  /-- Products are compared using their restricted projections. -/
  productIso : ∀ P : Cx l E X U,
    (restrictionComplex l E X a).obj
      (∏ᶜ fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n)) ≅
        ∏ᶜ fun n : ℕ ↦ ((tower l E X V).obj
          ((restrictionComplex l E X a).obj P)).obj (op n)
  /-- The comparison of the specified shifted cones, natural in the input complex. -/
  roosIso : roos l E X U ⋙ restrictionComplex l E X a ≅
    restrictionComplex l E X a ⋙ roos l E X V
  /-- Completion comparison, natural on the actual derived category. -/
  completionIso : completion l E X U ⋙ restrictionDerived l E X a ≅
    restrictionDerived l E X a ⋙ completion l E X V
  /-- Ordinary tensor comparison, used to identify the completed tensor. -/
  ordinaryTensorIso : (duality l E X U).closed.tensor ⋙ restrictionDerived l E X a ≅
    ((restrictionDerived l E X a).prod (restrictionDerived l E X a)) ⋙
      (duality l E X V).closed.tensor
  /-- Completed tensor comparison. -/
  tensorIso : completedTensor l E X U ⋙ restrictionDerived l E X a ≅
    ((restrictionDerived l E X a).prod (restrictionDerived l E X a)) ⋙
      completedTensor l E X V
  /-- Internal Hom is the ordinary ambient ringed-site derived internal Hom. -/
  homIso : hom l E X U ⋙ restrictionDerived l E X a ≅
    ((restrictionDerived l E X a).op.prod (restrictionDerived l E X a)) ⋙ hom l E X V
  /-- The coefficient object carries its unchanged restricted coefficient action. -/
  coefficientIso : (restrictionDerived l E X a).obj (coefficient l E X U) ≅
    coefficient l E X V

/-- On direct restriction the ordinary tensor and Hom comparisons are precisely the
published pure-tensor and local-Hom-family comparisons, including their model squares.
Source: Stacks 07A4, 08JB (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.GlobalModel (B : X.ProEt)
    (d : CompletedRestrictionComparisons l E X
      (U := none) (V := some B) PUnit.unit) : Prop :=
  letI : HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      ((sheafCompose ((topology X none).over B)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((ring l E X none).over B))) := hasDerived l E X (some B)
  ∃ e : RingedSliceEvaluationComparisons
      (hom l E X none) (hom l E X (some B))
      (restrictionDerived l E X (U := none) (V := some B) PUnit.unit)
      (duality l E X none).closed (duality l E X (some B)).closed
      (RingedSliceFlatRestriction (topology X none) (ring l E X none) B),
    RingedSliceEvaluationNormalized (topology X none) (ring l E X none) B
      (duality l E X none).closed (duality l E X none).models
      (duality l E X (some B)).closed (duality l E X (some B)).models e ∧
    (∀ L M : D l E X none, d.ordinaryTensorIso.hom.app (L, M) = (e.rho L M).hom) ∧
    (∀ L M : D l E X none, d.homIso.hom.app (op L, M) = (e.eta L M).hom)

end WeilConjectures.IntegralOnSlice
