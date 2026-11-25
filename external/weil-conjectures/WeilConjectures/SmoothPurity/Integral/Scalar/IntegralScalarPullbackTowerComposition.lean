/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelComposition

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Composition of normalized strict scalar pullback towers

Finite-level composition and the specified components of the strict tower maps
prove the tower identity, before applying the additive Roos construction.
(blueprint: lem-pur-integral-scalar-pullback-tower-composition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
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
attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
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

attribute [local irreducible] integralOrdinaryScalarComp scalarPullbackLevel scalarPullbackTower
  integralOperationsLevelPullback unrestrictedIntegralReductionFunctor
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback Functor.leftAdjoint
attribute [local implicit_reducible] integralOperationsPullbackLevel integralOperationsRestrict
  integralCoefficientSheaf integralCoefficientCommRingSheaf

private theorem pullbackTower_component {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    ((scalarPullbackTower l E L ι f).app P).app (op n) =
      (scalarPullbackLevel l E L ι f n).app P := by
  simpa only [scalarPullbackTower] using
    (scalarPullbackTower_existsUnique l E L ι f).exists.choose_spec P n

/-- The normalized strict scalar pullback towers respect coefficient composition.
Source: Stacks 07A4 and 08TC; the strict-tower part of the scalar comparison in
blueprint fix-prop-coherence. At each tower index use the component normalization
of scalarPullbackTower, apply finite-level composition, and then use natural
transformation extensionality. No new reduction map or limit comparison is chosen.
(blueprint: lem-pur-integral-scalar-pullback-tower-composition) -/
theorem integralScalarPullbackTowerComposition {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    Functor.whiskerRight ((scalarPullbackTower l E L ι f).app P)
        ((integralOrdinaryScalar l L F j X).mapHomologicalComplex (.up ℤ)) ≫
      (scalarPullbackTower l L F j f).app
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (integralOperationsPullbackTowerFunctor l F f).map
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j)
          (.up ℤ)).hom.app P) =
    Functor.whiskerLeft ((integralOperationsPullbackTowerFunctor l E f).obj P)
      ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι X F j)
        (.up ℤ)).hom) ≫ (scalarPullbackTower l E F (j.comp ι) f).app P := by
  apply NatTrans.ext
  funext n
  change (((integralOrdinaryScalar l L F j X).mapHomologicalComplex (.up ℤ)).map
      (((scalarPullbackTower l E L ι f).app P).app (op n.unop))) ≫
        ((scalarPullbackTower l L F j f).app _).app (op n.unop) ≫
          ((integralOperationsPullbackTowerFunctor l F f).map _).app (op n.unop) =
    (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι X F j)
      (.up ℤ)).hom.app _ ≫ ((scalarPullbackTower l E F (j.comp ι) f).app P).app (op n.unop)
  rw [pullbackTower_component, pullbackTower_component, pullbackTower_component]
  exact integralScalarPullbackLevelComposition l E L ι F j f P n.unop

end WeilConjectures
