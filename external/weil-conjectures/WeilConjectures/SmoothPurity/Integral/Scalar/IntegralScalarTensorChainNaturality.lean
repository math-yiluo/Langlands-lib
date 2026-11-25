/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison

/-! # Naturality of the scalar tensor Roos map

Source: Stacks 03EL, 07A4, 0941 and 08TC; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-pur-integral-scalar-tensor-chain-naturality).
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
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor

/-- Naturality follows by specializing the additive Roos natural transformation.
Source: Stacks 08TC (blueprint: lem-pur-integral-scalar-tensor-chain-naturality).
Proof: apply scalarRoosTransformation to scalarTensorTower and read its
naturality equation, unfolding only the Roos tensor functor and chain map. -/
theorem scalarTensorChain_naturality (W : AlgebraicGeometry.Scheme.{u})
    {P Q : CochainComplex (integralTowerModules l E W) ℤ ×
      CochainComplex (integralTowerModules l E W) ℤ} (a : P ⟶ Q) :
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).map
        ((integralOperationsTensorComplexFunctor l E W).map a) ≫
        scalarTensorChain l E L ι W Q.1 Q.2 =
      scalarTensorChain l E L ι W P.1 P.2 ≫
        (integralOperationsTensorComplexFunctor l L W).map
          ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).prod
            ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ))).map a) := by
  let S := (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)
  let δ := scalarRoosTransformation (integralOperationsTensorTowerFunctor l E W)
    (integralOperationsTensorTowerFunctor l L W) (S.prod S)
    (integralOrdinaryScalar l E L ι W) (scalarTensorTower l E L ι W)
  simpa only [δ, S, scalarRoosTransformation, scalarTensorChain,
    integralOperationsTensorComplexFunctor, Functor.comp_map] using δ.naturality a

end WeilConjectures
