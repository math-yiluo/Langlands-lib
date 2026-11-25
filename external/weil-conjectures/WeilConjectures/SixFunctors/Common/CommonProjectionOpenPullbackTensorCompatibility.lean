/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonProjectionTensorComparison
import WeilConjectures.SixFunctors.Common.CommonStagePullbackTensorForward
import WeilConjectures.SixFunctors.Common.CommonProjectionTensorComparisonNormalization

/-! # Representative compatibility for the common-stage open pullback/tensor square

Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-common-projection-open-pullback-tensor-forward-compatibility).

This is the concrete compatibility equation needed to apply the generic forward
transport lemma. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option Elab.async false
set_option linter.auxLemma false

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

private theorem uncurry_normalization
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (T : A ⥤ B ⥤ C) (U : A × B ⥤ C)
    (h : T = Functor.currying.inverse.obj U) : Functor.uncurry.obj T = U := by
  rw [h]
  simp only [Functor.currying, Functor.uncurry_obj_curry_obj]

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedPullback commonStageDerivedTensor
  sfRationalScalarExtension sfConstructibleIntegralScalarExtension
  canonicalRationalPullbackTensor canonicalCommonStagePullbackTensor
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso
  GeneralAlgebraicallyClosedCoefficients.unitor

-- Keep the coefficient-category structures abstract during diagram elaboration.
attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  instCategoryDerivedCategory DerivedCategory.instPreadditive HomologicalComplex.instCategory
  SheafOfModules.instCategory SheafOfModules.instAbelian
  completedIntegralCommRingSheafUnrestricted
  rationalPullbackScalarComparison rationalTensorScalarComparison
  Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue
  sfIntegralScalarComp sfIntegralScalarUnit
  ScalarLocalization.category Scheme.residueField
  StageSystem.PairCategory.categoryStruct Preadditive.fullSubcategory
  sfIntegralConstructible ScalarLocalization.linear ScalarLocalization.preadditive
  Linear.homModule Preadditive.homGroup Linear.fullSubcategory sfIntegralConstructibleLinear

-- Keep inclusion maps abstract when matching the final compatibility equation.
-- Their representatives were already evaluated in the inverse-square theorem.
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.inclusion
attribute [local irreducible] StageSystem.ι StageSystem.PairCategory.mkHom
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

/-- The finite-stage representative equation for the common-stage open square.

Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-open-pullback-tensor-forward-compatibility).

Proof: normalize the rational and common tensorators and pullback comparisons,
evaluate the canonical common-stage pullback/tensor representative at the included
pair, and cancel the transition maps and scalar unit. -/
theorem commonProjectionOpenPullbackTensor_forward_compatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C)
    (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D)
    (M N : sfRationalConstructibleCategory C.l
      (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E) Q.Z.obj.left) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Q.X.obj.left) E).map
        (((H.coefficientStages E).rationalExchange Q).openTensorPullback.hom.app M |>.app N) ≫
      (commonProjectionTensorComparison H E Q.X).hom.app
        ((H.coefficientStages E).rational.pull Q.i |>.obj M,
          (H.coefficientStages E).rational.pull Q.i |>.obj N) ≫
      (Functor.uncurry.obj (H.commonStageTensor Q.X)).map
        (Prod.mkHom
          (((H.commonStageComparison E).directAdjunction Q.i).left.hom.app M)
          (((H.commonStageComparison E).directAdjunction Q.i).left.hom.app N)) =
    (((H.commonStageComparison E).directAdjunction Q.i).left.hom.app
      ((Functor.uncurry.obj ((H.coefficientStages E).rationalTensor Q.Z)).obj (M, N))) ≫
      (H.commonStage.pull Q.i).map
        ((commonProjectionTensorComparison H E Q.Z).hom.app (M, N)) ≫
      (((H.commonStageExchange Q).openTensorPullback.hom.app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Q.Z.obj.left) E).obj M)).app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Q.Z.obj.left) E).obj N)) := by
  let : ∀ x : Q.X.obj.left, Invertible (C.l : Q.X.obj.left.residueField x) :=
    fun x ↦ (sixFunctorSpace_coefficient_invertible C Q.X x).some
  let : ∀ x : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField x) :=
    fun x ↦ (sixFunctorSpace_coefficient_invertible C Q.Z x).some
  have hRY := uncurry_normalization _ _
    ((H.coefficientStages E).rationalTensorNormalization Q.Z)
  have hRX := uncurry_normalization _ _
    ((H.coefficientStages E).rationalTensorNormalization Q.X)
  have hUY := uncurry_normalization _ _ (H.commonStageTensorNormalization Q.Z)
  have hUX := uncurry_normalization _ _ (H.commonStageTensorNormalization Q.X)
  have hty := commonProjectionTensorComparison_heq H E Q.Z
  have htx := commonProjectionTensorComparison_heq H E Q.X
  have he := (H.commonStageModelNormalization E).2.1 Q.i
  have hmu := (H.coefficientStages E).rationalOpenTensorPullbackNormalization Q M N
  have hmu' := H.commonStageOpenTensorPullbackNormalization Q
    ((inclusion (Y := Q.Z.obj.left) E).obj M) ((inclusion (Y := Q.Z.obj.left) E).obj N)
  exact commonStagePullbackTensor_forward_of_normalizations C.l C.Qbar Q.i.hom.left E
    ((H.coefficientStages E).rational.pull Q.i) (H.commonStage.pull Q.i)
    (Functor.uncurry.obj ((H.coefficientStages E).rationalTensor Q.Z))
    (Functor.uncurry.obj ((H.coefficientStages E).rationalTensor Q.X))
    (Functor.uncurry.obj (H.commonStageTensor Q.Z))
    (Functor.uncurry.obj (H.commonStageTensor Q.X))
    ((H.coefficientStages E).rationalPullback Q.i) (H.commonStagePullback Q.i)
    hRY hRX hUY hUX
    (commonProjectionTensorComparison H E Q.Z) (commonProjectionTensorComparison H E Q.X)
    hty htx
    ((H.commonStageComparison E).directAdjunction Q.i).left
    he M N
    (((H.coefficientStages E).rationalExchange Q).openTensorPullback.hom.app M |>.app N)
    (((H.commonStageExchange Q).openTensorPullback.hom.app
      ((inclusion (Y := Q.Z.obj.left) E).obj M)).app
        ((inclusion (Y := Q.Z.obj.left) E).obj N))
    hmu hmu'

end WeilConjectures
