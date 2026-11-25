/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorGoodComparison

/-! # The uniquely normalized good scalar tensor isomorphism

Source: Stacks 07A4 and 0941; categories.tex, Tag 04VK.
(blueprint: def-pur-integral-scalar-tensor-good-iso).
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
/-- The uniquely normalized good comparison, with its fixed chain-map components.
Source: Stacks 07A4, 0941 and 08TC.
(blueprint: def-pur-integral-scalar-tensor-good-iso).
The proved uniqueness theorem determines this object by all its hom components;
no arbitrary existence witness is used. Its construction is the NatIso.ofComponents
construction in that theorem, and only its invertibility proofs depend on the
chain quasi-isomorphism theorem. -/
def integralScalarTensorGoodIso :=
  (integralScalarTensorGoodComparison l E L ι W).exists.choose

/-- The good tensor comparison has exactly the specified localized chain components.
Source: Stacks 07A4, 0941 and 08TC.
(blueprint: def-pur-integral-scalar-tensor-good-iso).
Proof: apply choose_spec of the proved uniqueness theorem used in the definition. -/
theorem integralScalarTensorGoodIso_hom_app (P) :
    (integralScalarTensorGoodIso l E L ι W).hom.app P =
      DerivedCategory.Q.map (scalarTensorChain l E L ι W P.1.obj P.2.obj) :=
  (integralScalarTensorGoodComparison l E L ι W).exists.choose_spec P

end WeilConjectures
