/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.SmoothPurity.Common.CommonStageInternalHomData
public import WeilConjectures.SmoothPurity.Common.CommonStagePullbackData
public import WeilConjectures.SmoothPurity.Common.CommonStagePullbackDescent
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

import WeilConjectures.SmoothPurity.CommonStageInternalHomDescent.CommonStageInternalHomDescent
import WeilConjectures.SmoothPurity.NormalizedPairDescent.PairDescentPrescribedComponents
import WeilConjectures.SmoothPurity.RawBilinearScalarComparison.RawBilinearScalarComparison
import all WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! # Derived pullback, tensor product, and internal Hom

Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1467;
Stacks Project, Tags 06YL, 06YV, 08J7 and 099N
(blueprint: prose-03-02).

The ambient operations for every commutative condensed coefficient ring are the
existing module-object derived pullback, K-flat relative tensor and closed internal Hom,
publicly re-exported here. `ambientDerivedOperations_spec` records their defining
properties and the exact termwise pullback comparison.

The finite, integral, rational and common-stage declarations below retain the legacy
constructible interfaces for their existing consumers. They do not define the ambient
operations of the current blueprint.

## Main definitions

- `finiteDerivedPullback`: exact intrinsic constant-coefficient inverse image.
- `finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`: ambient operations.
- `finiteIntrinsicTensorModels`: K-flat tensor and ordinary evaluation normalization.
- `finiteIntrinsicReductionHom`: reduced evaluation's canonical closed transpose.
- `constructibleIntegralPullback`, `constructibleIntegralTensor`: actual restrictions.
- `constructibleIntegralHom`: ambient Hom restricted to permitted constructible pairs.
- `rationalDerivedPullback`, `rationalDerivedTensor`, `rationalDerivedInternalHom`:
  the uniquely specified linear and bilinear extensions with unchanged integral objects.
- `commonStageDerivedPullback`, `commonStageDerivedTensor`, `commonStageDerivedInternalHom`:
  operations on the recorded pair category, with normalized representative formulas.

Every common-stage comparison rationalizes the prescribed integral comparison.
No idempotent completion, arbitrary isomorphism, or extra coefficient flatness is used.
-/

-- The module has public declarations; avoid the costly final private-only style scan.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
-- The generated common-stage types make the section-variable linter expensive.
-- Every retained section parameter is present in the operation's public type.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂

open Opposite TensorProduct

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

-- Keep the chosen derived localization model abstract during elaboration.
attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear

section PairDescent
variable {I : Type*} [Preorder I] [IsDirectedOrder I]
  {C : I → Type*} [∀ i, Category* (C i)]
  {D : I → Type*} [∀ i, Category* (D i)]
  (S : StageSystem C) (T : StageSystem D) (φ : ∀ i, C i ⥤ D i)

end PairDescent

/-! Private helpers of the former single module, kept here verbatim: the importers
`FiniteProductFieldCoefficientDescent` and `RationalRestrictionComparisonCoherence` use them
through `import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom`. -/

private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem chosenUnique_spec {A : Sort*} {p : A → Prop} (h : ∃! a, p a)
    (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private abbrev rationalTensor_spec (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
  chosenUnique_spec (rationalDerivedTensor_existsUnique l E W)
    (rationalDerivedTensor l E W) rfl

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue

attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  integralDerivedInternalHom sfRationalScalarExtension
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor

section CommonStage
attribute [local irreducible] rationalDerivedInternalHom
  ScalarLocalization.composition StageSystem.PairCategory.mkHom
attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

attribute [local irreducible] rationalHomScalarComparison
  sfConstructibleIntegralScalarExtension sfIntegralScalarComp sfIntegralScalarUnit

attribute [local irreducible] operationStageTransitionIso

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

attribute [local irreducible] commonStagePullbackComparison

section PullbackProofs

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local irreducible] ScalarLocalization.category

/-- Pullback on the actual pair-category quotient has the prescribed representative action.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02).
Proof: use the normalized rationalPullbackScalarComparison for every coefficient
inclusion. The strict generator formulas commute with a tower of coefficient
maps; multiplication and associativity of tensors give the scalar associators.
Both Roos coordinates preserve these equalities. Thus the comparisons satisfy
the coherent pair-functor descent equation. Conjugating a representative by the
source comparison and inverse target comparison is independent of enlargement
and eventual equality. Composition cancels the middle comparisons; identity
representatives give identities. Every arrow has a representative, so the object
and representative formulas uniquely determine the functor. -/
theorem commonStageDerivedPullback_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X,
      (∀ P, F.obj P = commonStagePullbackObject l Ω f P) ∧
      (∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
        (L : Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
        (a : P.toStage hP ⟶ Q.toStage hQ),
        HEq (F.map (X := P) (Y := Q) (ofHom P Q L hP hQ a))
          (ofHom (commonStagePullbackObject l Ω f P)
            (commonStagePullbackObject l Ω f Q) L hP hQ
            ((commonStagePullbackComparison l Ω f P L hP).hom ≫
              (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map a ≫
              (commonStagePullbackComparison l Ω f Q L hQ).inv))) := by
  exact (commonStagePullback_comparison_data l Ω f).elim
    (fun b hb ↦ commonStagePullback_descent_from_data l Ω f b hb.1 hb.2)

end PullbackProofs

/-- Canonical common-stage pullback, with no new coefficient objects or retracts.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def commonStageDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :=
  (commonStageDerivedPullback_existsUnique l Ω f).exists.choose

/-- The literal tensor object is formed at the finite coefficient compositum.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def commonStageTensorObject (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  ⟨Padic.finiteCoefficientCompositum l Ω P.stage Q.stage,
    (rationalDerivedTensor l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage)) W).obj
      (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1,
        Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2)⟩

section ComparisonElaboration
attribute [local irreducible] ObjectProperty.FullSubcategory.category

/-- The tensor comparison at a common stage includes the scalar associators of both inputs.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def commonStageTensorComparison (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : Index l Ω) (h : (commonStageTensorObject l Ω W P Q).stage ≤ L) :
    (commonStageTensorObject l Ω W P Q).toStage h ≅
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).obj
        (P.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h),
          Q.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)) :=
  (operationStageTransitionIso l Ω W _ L h).app
      (commonStageTensorObject l Ω W P Q).obj ≪≫
    (rationalTensorScalarComparison l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage))
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W).app
      (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1,
        Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2) ≪≫
    (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).mapIso
      (Iso.prod
        (((operationStageTransitionIso l Ω W _ L h).app
          (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
            P.stage Q.stage).1)).symm ≪≫
          ((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1 h).app P.obj)
        (((operationStageTransitionIso l Ω W _ L h).app
          (Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
            P.stage Q.stage).2)).symm ≪≫
          ((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2 h).app Q.obj))

end ComparisonElaboration

attribute [local irreducible] commonStageTensorComparison

section TensorDescentElaboration
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.pairCategory CategoryTheory.uniformProd
attribute [local semireducible] operationStageTransitionIso
attribute [local irreducible] ObjectProperty.FullSubcategory.category ScalarLocalization.category

/-- Common-stage tensor has the bilinear representative formula of the blueprint.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02).
Proof: extend both endpoints to their finite coefficient composita and use the
literal object formula. At a common larger stage, use commonStageTensorComparison
to identify their scalar extensions with the tensor of the extended inputs. The
normalized scalar tensor comparisons are natural, compatible with coefficient
towers and units: test their strict finite generator formulas and both Roos
coordinates. Thus the displayed conjugation respects eventual equality. At a
common stage, composition and identities follow from the rational tensor functor;
intermediate comparisons cancel. Directedness puts every pair of morphisms at
such a common stage, so the formula also gives uniqueness. -/
theorem commonStageDerivedTensor_existsUnique (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω W ×
        generalAlgebraicallyClosedConstructibleCategory l Ω W ⥤
          generalAlgebraicallyClosedConstructibleCategory l Ω W,
      (∀ P Q, F.obj (P, Q) = commonStageTensorObject l Ω W P Q) ∧
      (∀ (P Q P' Q' : generalAlgebraicallyClosedConstructibleCategory l Ω W)
        (L : Index l Ω)
        (h : (commonStageTensorObject l Ω W P Q).stage ≤ L)
        (h' : (commonStageTensorObject l Ω W P' Q').stage ≤ L)
        (a : P.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h) ⟶
          P'.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).1.trans h'))
        (b : Q.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h) ⟶
          Q'.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).2.trans h')),
        HEq (F.map (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom
          (ofHom P P' L
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h)
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).1.trans h') a)
          (ofHom Q Q' L
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).2.trans h') b)))
          (ofHom (commonStageTensorObject l Ω W P Q)
            (commonStageTensorObject l Ω W P' Q') L h h'
            ((commonStageTensorComparison l Ω W P Q L h).hom ≫
              (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).map (Prod.mkHom a b) ≫
              (commonStageTensorComparison l Ω W P' Q' L h').inv))) := by
  let S := stageSystem l Ω W
  let U : BilinearCoefficientDescent.Family S S S :=
    ⟨fun E ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) W,
      fun {_ _} h ↦ rationalTensorStageComparison l Ω W h,
      rationalTensorStageComparison_coherent l Ω W⟩
  let join := Padic.finiteCoefficientCompositum l Ω
  let left := fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1
  let right := fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2
  have hc (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W)
      (L : Index l Ω) (h : join P.stage Q.stage ≤ L) :
      BilinearCoefficientDescent.endpoint U join left right (P, Q) h =
        commonStageTensorComparison l Ω W P Q L h := by
    unfold BilinearCoefficientDescent.endpoint
    change ((rationalTensorStageComparison l Ω W h).app
      (P.toStage (left P.stage Q.stage), Q.toStage (right P.stage Q.stage)) ≪≫
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).mapIso
        (Iso.prod ((S.assoc (left P.stage Q.stage) h).app P.obj)
          ((S.assoc (right P.stage Q.stage) h).app Q.obj))) = _
    delta rationalTensorStageComparison commonStageTensorComparison operationStageTransitionIso
    have hh := tensorStageComparison_endpoint
      (C := Stage l Ω W (join P.stage Q.stage)) (D := Stage l Ω W L)
      (rationalDerivedTensor l (Coefficient.{u} l Ω (join P.stage Q.stage)) W)
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) W)
      (operationStageTransitionIso l Ω W _ L h)
      (rationalTensorScalarComparison l (Coefficient.{u} l Ω (join P.stage Q.stage))
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W)
      (P.toStage (left P.stage Q.stage)) (Q.toStage (right P.stage Q.stage))
      ((S.assoc (left P.stage Q.stage) h).app P.obj)
      ((S.assoc (right P.stage Q.stage) h).app Q.obj)
    exact hh
  exact tensorDescent_with_components S U join left right
    (fun P Q L h ↦ commonStageTensorComparison l Ω W P Q L h) hc

end TensorDescentElaboration

/-- The canonical common-stage tensor functor on the existing pair category.
Source: blueprint common-stage paragraph
(blueprint: prose-03-02). -/
def commonStageDerivedTensor (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :=
  (commonStageDerivedTensor_existsUnique l Ω W).exists.choose

section HomDescent

attribute [local irreducible] commonStageHomComparison
set_option allowUnsafeReducibility true in
attribute [local reducible] commonStageHomObject commonStageHomPairAtStage
  GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.pairCategory
attribute [local irreducible] ScalarLocalization.category
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local implicit_reducible] catToReflQuiver

open CommonStageInternalHom CommonStageInternalHomDescent

/-- Common-stage internal Hom has precisely the contravariant representative formula.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: prose-03-02).
Proof: form the permitted rational Hom at each literal compositum. The permitted
pair remains permitted at every common stage by commonStageHomPairAtStage_permitted.
Use commonStageHomComparison to compare the scalar extension of each output with
the Hom of the extended inputs. Its ordinary comparison transposes extended
evaluation; the inverse comparison in its first argument gives exactly u.op in
the formula. Naturality and the normalized coefficient tower equations show that
conjugation respects further transport and eventual equality. At a common stage,
the rational Hom functor gives identity and composition; the middle comparisons
cancel. Directedness puts any two representatives at such a stage. Every arrow
has a representative, so these formulas determine the functor uniquely. -/
theorem commonStageDerivedInternalHom_existsUnique (W : Scheme.{u}) :
    ∃! F : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω W,
      (∀ P, F.obj P = commonStageHomObject.{u, v} l Ω W P) ∧
      (∀ (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
        (L : Index l Ω)
        (h : (StageSystem.PairCategory.stage.{v, u+2, u+2}
          (commonStageHomObject.{u, v} l Ω W P)) ≤ L)
        (h' : (StageSystem.PairCategory.stage.{v, u+2, u+2}
          (commonStageHomObject.{u, v} l Ω W Q)) ≤ L)
        (a : (commonStageHomPairAtStage.{u, v} l Ω W Q L h').obj.1.unop ⟶
          (commonStageHomPairAtStage.{u, v} l Ω W P L h).obj.1.unop)
        (b : (commonStageHomPairAtStage.{u, v} l Ω W P L h).obj.2 ⟶
          (commonStageHomPairAtStage.{u, v} l Ω W Q L h').obj.2),
        HEq (F.map (X := P) (Y := Q)
          (ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom
            (StageSystem.PairCategory.mkHom.{v, u+2, u+2}
              (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω W)
              (S := stageSystem l Ω W) (X := Q.obj.1.unop) (Y := P.obj.1.unop) L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.2)).1.trans h')
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.2)).1.trans h) a).op
            (StageSystem.PairCategory.mkHom.{v, u+2, u+2}
              (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω W)
              (S := stageSystem l Ω W) (X := P.obj.2) (Y := Q.obj.2) L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.2)).2.trans h)
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.2)).2.trans h') b))))
          (StageSystem.PairCategory.mkHom.{v, u+2, u+2}
              (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω W)
              (S := stageSystem l Ω W)
              (X := commonStageHomObject.{u, v} l Ω W P)
              (Y := commonStageHomObject.{u, v} l Ω W Q) L h h'
            ((commonStageHomComparison.{u, v} l Ω W P L h).hom ≫
              (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map
                (X := commonStageHomPairAtStage.{u, v} l Ω W P L h)
                (Y := commonStageHomPairAtStage.{u, v} l Ω W Q L h')
                (ObjectProperty.homMk
                  (X := commonStageHomPairAtStage.{u, v} l Ω W P L h)
                  (Y := commonStageHomPairAtStage.{u, v} l Ω W Q L h')
                  (Prod.mkHom a.op b)) ≫
              (commonStageHomComparison.{u, v} l Ω W Q L h').inv))) := by
  let F : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω W :=
    { obj := commonStageHomObject l Ω W
      map := homArrow l Ω W
      map_id := fun P ↦ by
        let L := (commonStageHomObject l Ω W P).stage
        calc
          homArrow l Ω W (𝟙 P) =
              homArrow l Ω W (input l Ω W P P L le_rfl le_rfl (𝟙 _) (𝟙 _)) :=
            congrArg (homArrow l Ω W) (homInput_id l Ω W P L le_rfl).symm
          _ = output l Ω W P P L le_rfl le_rfl (𝟙 _) (𝟙 _) :=
            homArrow_spec l Ω W P P L le_rfl le_rfl (𝟙 _) (𝟙 _)
          _ = 𝟙 _ := homOutput_id l Ω W P L le_rfl
      map_comp := fun {P Q R} f g ↦ by
        obtain ⟨L, -, hP, hQ, a, b, hf⟩ :=
          homRepresentative_exists l Ω W P Q f (commonStageHomObject l Ω W P).stage
        obtain ⟨M, hLM, hQ', hR, a', b', hg⟩ :=
          homRepresentative_exists l Ω W Q R g L
        have hf' := hf.trans (homInput_transport l Ω W P Q L M hP hQ hLM a b).symm
        rw [hf', hg, homInput_comp, homArrow_spec, homArrow_spec, homArrow_spec]
        exact (homOutput_comp l Ω W P Q R M (hP.trans hLM) hQ' hR
          ((stageSystem l Ω W).tr hLM a) ((stageSystem l Ω W).tr hLM b) a' b').symm }
  refine ⟨F, ⟨fun P ↦ rfl, ?_⟩, ?_⟩
  · intro P Q L h h' a b
    exact heq_of_eq (homArrow_spec l Ω W P Q L h h' a b)
  · intro G hG
    apply Functor.hext hG.1
    intro P Q f
    obtain ⟨L, -, hP, hQ, a, b, rfl⟩ :=
      homRepresentative_exists l Ω W P Q f (commonStageHomObject l Ω W P).stage
    exact (hG.2 P Q L hP hQ a b).trans
      (heq_of_eq (homArrow_spec l Ω W P Q L hP hQ a b).symm)

/-- The canonical common-stage internal Hom on precisely the permitted full subcategory.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: prose-03-02). -/
def commonStageDerivedInternalHom (W : Scheme.{u}) :=
  (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose

end HomDescent

end CommonStage
end WeilConjectures

open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option synthInstance.maxSize 2048

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

end AlgebraicGeometry.ProEtale.CondensedRing
