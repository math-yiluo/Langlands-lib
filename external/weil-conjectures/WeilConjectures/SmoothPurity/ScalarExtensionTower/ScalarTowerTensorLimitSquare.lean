/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitSquareTransport

/-! # Canonical scalar comparison in total-limit coordinates

Source: Stacks 07A4 and 0941; realization step 8 of
lem-pur-scalar-extension-tower-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
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
  pullbackReduction scalarReduction tensorReduction derivedSigma

/-- The tensor scalar comparison in its specified total-limit coordinates.
This is the tensor word calculation before coherent-reduction adjunction; it
neither constructs realization models nor asserts the pullback word calculation.
Source: Stacks 07A4, 0941; original realization step 8
(blueprint: stage3-pur-scalar-tensor-limit-square).

Proof: resolve M and N simultaneously by flat-term K-flat complexes and take
their actual quotient systems. Scalar change and signed total tensor preserve the
resolving class. The normalization fields of TE, TL and SY identify the two word
coordinates with Roos maps of these same strict systems. Tensor balancing sends
b tensor (x tensor y) to (b tensor x) tensor (1 tensor y); its inverse multiplies
the coefficient factors. Both maps preserve each bidegree, the signed differential
and every quotient transition. The representative equation characterizing
DerivedSigmaModel identifies the localization of this strict map with derivedSigma.
The prescribed scalarTensorOrdinary normalization uses precisely its total-tensor
Roos map; scalarCompletionIso inserts the same quotient augmentation and zero
shifted coordinate. Thus scalarTensorCompleted has exactly this limit coordinate.
Naturality of Roos and localization in both good-representative variables yield
the displayed equation on M,N. The choice of hT is proof irrelevant. Zero inputs,
identity coefficients and ramification obey the same balancing calculation; no
flatness of the quotient coefficient homomorphism or limit interchange is used. -/
theorem scalarTowerTensorLimitSquare (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (_hl : IsUnit (l : Γ(W, ⊤)))
    (M N : sfIntegralConstructibleCategory l E W)
    (hT : IsSfDerivedComplete l E W
      ((integralCompletedTensor.{u, u} l E W).obj (M.obj, N.obj))) :
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
          (derivedSigma l E L ι W SE SL).hom.app
            (SE.reduction.obj M.obj, SE.reduction.obj N.obj)) := by
  have hα := (derivedSigma_existsUnique l E L ι W SE SL).exists.choose_spec
  let α := derivedSigma l E L ι W SE SL
  have hα' : DerivedSigmaModel l E L ι W SE SL α := by
    simpa only [α, derivedSigma] using hα
  exact scalarTowerTensorLimitSquare_of_derivedSigmaModel l E L ι W SE SL ρE ρL SY TE TL
    _hl M N hT α hα'

end WeilConjectures.ScalarExtensionTower
