/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels

import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackRoosQuasiIso

/-! # Properties of the specified integral scalar pullback chain map

Source: Stacks 07A4, 0941 and 08TC.
(blueprint: lem-pur-integral-scalar-pullback-chain-quasi-iso).

Naturality follows from the two Roos coordinates. The quasi-isomorphism proof
specializes the normalized cofinal-filtration comparison to the specified maps.
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
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

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

section ScalarPullbackChainProperties

attribute [local implicit_reducible] integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor

private theorem scalarPullbackChain_naturality
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    {P Q : CochainComplex (integralTowerModules l E Y) ℤ} (a : P ⟶ Q) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        ((integralOperationsPullbackComplexFunctor l E f).map a) ≫
        scalarPullbackChain l E L ι f Q =
      scalarPullbackChain l E L ι f P ≫
        (integralOperationsPullbackComplexFunctor l L f).map
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).map a) := by
  let δ := scalarRoosTransformation (integralOperationsPullbackTowerFunctor l E f)
    (integralOperationsPullbackTowerFunctor l L f)
    ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ))
    (integralOrdinaryScalar l E L ι X) (scalarPullbackTower l E L ι f)
  simpa only [δ, scalarRoosTransformation, scalarPullbackChain,
    integralOperationsPullbackComplexFunctor, Functor.comp_map] using δ.naturality a

/-- The specified pullback chain comparison is a quasi-isomorphism on every good complex.
Source: Stacks 07A4, 0941 and 08TC, via the normalized Roos comparison.
(blueprint: lem-pur-integral-scalar-pullback-chain-quasi-iso).
Proof: unfold the specified chain map as its additive Roos comparison followed
by its strict tower comparison. Apply integralScalarPullbackRoosQuasiIso.
The chosen strict tower normalization identifies its component at each n with
the chosen finite-level map, whose generator normalization gives the first
hypothesis. The two defining coordinates of scalarRoosMap give the second.
No further completeness or boundedness assumption is used. -/
theorem scalarPullbackChainQuasiIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    QuasiIso (scalarPullbackChain l E L ι f P.obj) := by
  unfold scalarPullbackChain integralOperationsPullbackComplexFunctor
  apply integralScalarPullbackRoosQuasiIso l E L ι f P.obj P.property
    ((scalarPullbackTower l E L ι f).app P.obj)
  · intro n i V x
    have ht : ((scalarPullbackTower l E L ι f).app P.obj).app (op n) =
        (scalarPullbackLevel l E L ι f n).app P.obj :=
      (scalarPullbackTower_existsUnique l E L ι f).exists.choose_spec P.obj n
    rw [ht]
    exact (scalarPullbackLevel_existsUnique l E L ι f n).exists.choose_spec P.obj i V x
  · exact (scalarRoosMap_existsUnique (integralOrdinaryScalar l E L ι X)
      ((integralOperationsPullbackTowerFunctor l E f).obj P.obj)).exists.choose_spec

end ScalarPullbackChainProperties

end WeilConjectures
