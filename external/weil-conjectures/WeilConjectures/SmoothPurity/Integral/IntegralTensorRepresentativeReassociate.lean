/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Reassociation of the tensor representative comparison

Source: Stacks 07A4 and 0941; categories.tex, Tag 04VK.
(blueprint: def-pur-integral-tensor-representative-reassociate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOperationsTensorTowerFunctor
  integralOperationsTensorComplexFunctor scalarTensorChain integralCompletedTensor
  integralOperationsRoosFunctor DerivedCategory.Q integralOperationsGoodComplex
attribute [local semireducible] integralOperationsTensorComplexFunctor
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor

variable (W : AlgebraicGeometry.Scheme.{u})
local notation "I" => ObjectProperty.ι (integralOperationsGoodComplex l E W)
local notation "q" => integralOperationsGoodLocalization l E W
local notation "t" => Functor.prod I I ⋙ integralOperationsTensorComplexFunctor l E W

/-- Reassociate the recorded tensor representative comparison without changing its map.
Source: Stacks 06YT and 08TC
(blueprint: def-pur-integral-tensor-representative-reassociate).
The construction is exactly integralCompletedTensorComparison; only its target
functor is written as the tensor complex functor followed by Q. -/
def integralTensorRepresentativeReassociate :
    (Functor.prod q q) ⋙ integralCompletedTensor l E W ≅ t ⋙ DerivedCategory.Q :=
  integralCompletedTensorComparison l E W

/-- The reassociation preserves every component of the recorded comparison.
Source: Stacks 06YT and 08TC
(blueprint: def-pur-integral-tensor-representative-reassociate).
Proof: the reassociation was defined to be this same comparison. -/
theorem integralTensorRepresentativeReassociate_app (P) :
    (integralTensorRepresentativeReassociate l E W).hom.app P =
      (integralCompletedTensorComparison l E W).hom.app P := rfl

end WeilConjectures
