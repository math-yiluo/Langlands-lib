/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitTransportAssembly

/-! # Transport of the normalized strict tensor comparison to total limits

Source: Stacks 07A4 and 0941; realization step 8 of
lem-pur-scalar-extension-tower-coherence.

This module isolates the localization and total-limit transport step.  The
strict tensor comparison itself is supplied as `DerivedSigmaModel`; the
remaining equation is the passage from its normalized cochain coordinates to
the named completed comparison and realization maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible]
  integralCompletedTensor integralDerivedPullback
  integralComparisonDerivedSequenceScalar integralComparisonDerivedSequencePullback
  pullbackReduction scalarReduction tensorReduction

/--
Transport a normalized strict scalar/tensor comparison through the two supplied
realization models and the completed scalar tensor comparison.  This is the
localization and total-limit part of the tensor word calculation: all finite
quotient and signed-total identities are contained in `hα` and are not
reproved here.

Source: Stacks 07A4 and 0941; the localization and derived-limit part of
realization step 8 of `lem-pur-scalar-extension-tower-coherence`.

Proof: choose simultaneous flat-term K-flat representatives of the two
constructible inputs.  Apply the normalization equations of `SY` and `TL` to
their quotient presentations, then use the `DerivedSigmaModel` equation `hα`
to identify the strict scalar/tensor map.  Naturality of the Roos bridge and
of the completion isomorphisms transports this equality from representatives
to the completed objects.  The localization universal property removes the
representative choices, and functoriality of the total limit gives the displayed
equality.  The same argument includes zero complexes, identity coefficient
maps, and ramified quotient transitions.
(blueprint: stage3-pur-scalar-tensor-limit-transport)
-/
theorem scalarTowerTensorLimitSquare_of_derivedSigmaModel (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (_hl : IsUnit (l : Γ(W, ⊤)))
    (M N : sfIntegralConstructibleCategory l E W)
    (hT : IsSfDerivedComplete l E W
      ((integralCompletedTensor.{u, u} l E W).obj (M.obj, N.obj)))
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (hα : DerivedSigmaModel l E L ι W SE SL α) :
    (scalarTensorCompleted l E L ι W M.obj N.obj M.property.1 N.property.1 hT).hom ≫
        TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι W).obj M.obj,
            (integralScalarExtension.{u} l E L ι W).obj N.obj) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY M.obj)
            (scalarReduction l E L ι W SE SL ρL SY N.obj))) =
      SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E W).obj (M.obj, N.obj)) ≫
      (coefficientSequenceLimit.{u, u} l L W).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
            (tensorReduction l E W SE ρE TE M.obj N.obj) ≫
          α.hom.app (SE.reduction.obj M.obj, SE.reduction.obj N.obj)) := by
  apply scalarTowerTensorLimitSquare_of_strictWitnesses l E L ι W SE SL ρE ρL SY TE TL
    _hl M N hT α
  intro P Q hP hQ
  exact strictTensorWitness_of_derivedSigmaModel l E L ι W SE SL α hα P Q hP hQ

end WeilConjectures.ScalarExtensionTower
