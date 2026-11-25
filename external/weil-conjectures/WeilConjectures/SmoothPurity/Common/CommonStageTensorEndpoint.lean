/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all Mathlib.Logic.Small.Defs

/-! # Tensor endpoint identification

Proved helper for restriction tensor representative stage transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory Stage transition
  WeilConjectures.commonStagePullbackObject WeilConjectures.commonStageTensorObject

set_option allowUnsafeReducibility true in
attribute [local reducible] stageSystem

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  ScalarLocalization.category ScalarLocalization.composition
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue sfRationalScalarComp
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.normalizedAssociator
  AlgebraicallyClosedCoefficients.coefficientInclusion
  ObjectProperty.FullSubcategory.category sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  sfRationalScalarExtension commonStageDerivedPullback commonStageDerivedTensor
  rationalPullbackScalarComparison rationalTensorScalarComparison
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The normalized tensor comparison followed by input associators is the pair endpoint.

Source: lemma-section-normal-bundle--1, common-stage subargument, steps 3–5.
Proof: Expand the normalized tensor comparison, keeping its transition isomorphisms.
Functoriality combines the two input corrections with the inverses of the transition
isomorphisms. This is exactly the defining common-stage tensor endpoint. The calculation
is the existing tensorStageComparison_endpoint applied to the two stage associators.
(blueprint: lem-weil-common-stage-tensor-endpoint). -/
theorem commonStageTensor_endpoint
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (P Q : Pair l Ω W) (L : Index l Ω)
    (h : (commonStageTensorObject l Ω W P Q).stage ≤ L) :
    (rationalTensorStageComparison l Ω W h).app
        (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1,
          Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2) ≪≫
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).mapIso
        (Iso.prod
          (((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1 h).app P.obj)
          (((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2 h).app Q.obj)) =
      commonStageTensorComparison l Ω W P Q L h := by
  delta rationalTensorStageComparison commonStageTensorComparison operationStageTransitionIso
  have hh := tensorStageComparison_endpoint
    (C := Stage l Ω W (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage))
    (D := Stage l Ω W L)
    (rationalDerivedTensor l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage)) W)
    (rationalDerivedTensor l (Coefficient.{u} l Ω L) W)
    (operationStageTransitionIso l Ω W _ L h)
    (rationalTensorScalarComparison l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage))
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W)
    (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1)
    (Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2)
    (((stageSystem l Ω W).assoc
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1 h).app P.obj)
    (((stageSystem l Ω W).assoc
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2 h).app Q.obj)
  simpa only [operationStageTransitionIso, commonStageTensorObject] using hh

end WeilConjectures
