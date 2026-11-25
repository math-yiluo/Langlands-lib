/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Rational.RationalPullbackStageCoherence
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs

/-! # Pullback endpoint identification

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

/-- The normalized pullback comparison is the prescribed pair endpoint comparison.

Source: lemma-section-normal-bundle--1, common-stage subargument, steps 3–5.
Proof: Expand both comparisons into the recorded transition isomorphism, the rational
pullback scalar comparison and the inverse source transition. Their component formulas
are identical; equality of the hom components gives equality of the isomorphisms.
(blueprint: lem-weil-common-stage-pullback-endpoint). -/
theorem commonStagePullback_endpoint
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : Pair l Ω X) (L : Index l Ω) (h : P.stage ≤ L) :
    (rationalPullbackStageComparison l Ω f h).app P.obj =
      commonStagePullbackComparison l Ω f P L h := by
  cases P
  apply Iso.ext
  unfold rationalPullbackStageComparison commonStagePullbackComparison
    operationStageTransitionIso
  simp only [Iso.app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.mapIso_hom, Iso.symm_hom,
    commonStagePullbackObject]

end WeilConjectures
