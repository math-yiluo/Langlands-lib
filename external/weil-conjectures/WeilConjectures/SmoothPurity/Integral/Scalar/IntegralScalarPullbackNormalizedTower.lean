/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackTowerRepresentatives
import WeilConjectures.CategoryTheory.SmoothPurity.FunctorSquareTowerDescent

/-! # Descent of normalized scalar pullback tower comparisons

The exact scalar factors and the normalized chain maps form coherent squares before
localization. Source: coefficient-comparison coherence, Stacks 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-pullback-normalized-tower).
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

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
attribute [local irreducible] constantSheaf limit
  integralDerivedPullback integralCompletedTensor integralScalarExtension

section ScalarTowerDescent

attribute [local irreducible] integralOrdinaryScalarComp integralOrdinaryDerivedScalarComp
attribute [local implicit_reducible] goodScalar integralOperationsPullbackOnGood
  integralOperationsTensorOnGood integralOperationsGoodLocalization
attribute [local irreducible] goodScalarComparison pullbackRep

private theorem pullbackNormalizedSquare
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f)
    (hα : scalarPullbackOrdinaryNormalization l E L ι f α)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (integralOrdinaryDerivedScalar l E L ι X).map ((pullbackRep l E f).hom.app P) ≫
        (pullbackSquare l E L ι f) P =
      (α).hom.app
          ((integralOperationsGoodLocalization l E Y).obj P) ≫
        (integralDerivedPullback l L f).map ((goodScalarComparison l E L ι Y).hom.app P) ≫
        (pullbackRep l L f).hom.app ((goodScalar l E L ι Y).obj P) := by
  simp only [pullbackRep_hom_app, goodScalarComparison_hom_app, pullbackSquare]
  exact hα P

/-- Normalized scalar pullback comparisons respect coefficient towers.
Source: coefficient-comparison coherence, Stacks 04VK, 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-pullback-normalized-tower).
Proof: the specified normalization equations identify the comparison squares on
good representatives. The scalar associator factorization and the chain tower
identity give the two representative associator equations. Apply faithful
localization descent to these three squares. For tensor pairs use the product
localization, whose restriction is fully faithful in both variables. -/
theorem integralScalarPullbackNormalizedTower
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f)
    (β : integralDerivedPullback l L f ⋙ integralOrdinaryDerivedScalar l L F j X ≅
      integralOrdinaryDerivedScalar l L F j Y ⋙ integralDerivedPullback l F f)
    (γ : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E F (j.comp ι) X ≅
      integralOrdinaryDerivedScalar l E F (j.comp ι) Y ⋙ integralDerivedPullback l F f)
    (hα : scalarPullbackOrdinaryNormalization l E L ι f α)
    (hβ : scalarPullbackOrdinaryNormalization l L F j f β)
    (hγ : scalarPullbackOrdinaryNormalization l E F (j.comp ι) f γ) :
    ∀ K : DerivedCategory (integralTowerModules l E Y),
      (integralOrdinaryDerivedScalar l L F j X).map
          ((α).hom.app K) ≫
        (β).hom.app
          ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
        (integralDerivedPullback l F f).map
          ((integralOrdinaryDerivedScalarComp l E L ι Y F j).hom.app K) =
      (integralOrdinaryDerivedScalarComp l E L ι X F j).hom.app
          ((integralDerivedPullback l E f).obj K) ≫
        (γ).hom.app K := by
  let q := integralOperationsGoodLocalization l E Y
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E Y
  exact functorSquareTowerDescent q
    (integralOperationsGoodLocalization l L Y) (integralOperationsGoodLocalization l F Y)
    (goodScalar l E L ι Y) (goodScalar l L F j Y) (goodScalar l E F (j.comp ι) Y)
    (goodScalarComp l E L ι F j Y)
    (integralOrdinaryDerivedScalar l E L ι Y) (integralOrdinaryDerivedScalar l L F j Y)
    (integralOrdinaryDerivedScalar l E F (j.comp ι) Y)
    (integralOrdinaryDerivedScalarComp l E L ι Y F j)
    (integralOrdinaryDerivedScalar l E L ι X) (integralOrdinaryDerivedScalar l L F j X)
    (integralOrdinaryDerivedScalar l E F (j.comp ι) X)
    (integralOrdinaryDerivedScalarComp l E L ι X F j)
    (integralDerivedPullback l E f) (integralDerivedPullback l L f)
    (integralDerivedPullback l F f) _ _ _
    (pullbackRep l E f) (pullbackRep l L f) (pullbackRep l F f)
    (goodScalarComparison l E L ι Y) (goodScalarComparison l L F j Y)
    (goodScalarComparison l E F (j.comp ι) Y)
    (pullbackSquare l E L ι f) (pullbackSquare l L F j f)
    (pullbackSquare l E F (j.comp ι) f)
    (α) (β)
    (γ)
    (Localization.fullyFaithfulWhiskeringLeft q V _).faithful
    (pullbackNormalizedSquare l E L ι f α hα)
    (pullbackNormalizedSquare l L F j f β hβ)
    (pullbackNormalizedSquare l E F (j.comp ι) f γ hγ)
    (goodScalarComp_factors l E L ι F j Y)
    (pullbackSquare_tower l E L ι F j f)

end ScalarTowerDescent
end WeilConjectures
