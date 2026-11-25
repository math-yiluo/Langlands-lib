/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelTower

/-! # Composition of normalized strict scalar tensor towers
(blueprint: lem-pur-integral-scalar-tensor-tower-composition). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor scalarPullbackChain scalarTensorChain
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

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F)

section TowerComposition
attribute [local irreducible] integralOperationsTensorLevel integralOrdinaryScalarComp
attribute [local implicit_reducible] integralOperationsTensorTowerFunctor

/-- Normalized strict tensor tower comparisons respect coefficient composition.
Source: Stacks 08TC and the blueprint coefficient comparison step 9.
(blueprint: lem-pur-integral-scalar-tensor-tower-composition).
Proof: extensionality of natural transformations reduces the equation to each
integer level. The chosen tower normalization identifies each tower component
with its finite tensor comparison. The finite-level scalar composition theorem
then supplies the required equality, including the two associator components. -/
theorem integralScalarTensorTowerComposition (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    Functor.whiskerRight ((scalarTensorTower l E L ι W).app (P, Q))
        ((integralOrdinaryScalar l L F j W).mapHomologicalComplex (.up ℤ)) ≫
      ((scalarTensorTower l L F j W).app
          ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
            (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
        (integralOperationsTensorTowerFunctor l F W).map (CategoryTheory.Prod.mkHom
          ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
            (.up ℤ)).hom.app P)
          ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
            (.up ℤ)).hom.app Q))) =
    Functor.whiskerLeft ((integralOperationsTensorTowerFunctor l E W).obj (P, Q))
        (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom ≫
      (scalarTensorTower l E F (j.comp ι) W).app (P, Q) := by
  apply NatTrans.ext
  funext n
  let SC := (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)
  have hi : ((scalarTensorTower l E L ι W).app (P, Q)).app n =
      (scalarTensorLevel l E L ι W n.unop).app (P, Q) := by
    exact (scalarTensorTower_existsUnique l E L ι W).exists.choose_spec P Q n.unop
  have hj : ((scalarTensorTower l L F j W).app (SC.obj P, SC.obj Q)).app n =
      (scalarTensorLevel l L F j W n.unop).app (SC.obj P, SC.obj Q) := by
    exact (scalarTensorTower_existsUnique l L F j W).exists.choose_spec
        (SC.obj P) (SC.obj Q) n.unop
  have hc : ((scalarTensorTower l E F (j.comp ι) W).app (P, Q)).app n =
      (scalarTensorLevel l E F (j.comp ι) W n.unop).app (P, Q) := by
    exact (scalarTensorTower_existsUnique l E F (j.comp ι) W).exists.choose_spec P Q n.unop
  dsimp only [Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app]
  rw [hi, hj, hc]
  exact integralScalarTensorLevelTower l E L ι F j W n.unop P Q

end TowerComposition

end WeilConjectures
