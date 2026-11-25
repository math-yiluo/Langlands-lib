/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackChainTower

/-! # Coherent scalar squares on pullback representatives

The exact scalar factors and the normalized chain maps form coherent squares before
localization. Source: coefficient-comparison coherence, Stacks 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-pullback-tower-representatives).
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

attribute [local irreducible] integralOrdinaryScalarComp

attribute [local implicit_reducible] integralOperationsPullbackOnGood
  integralOperationsTensorOnGood integralOperationsGoodLocalization

private def goodScalar (W : AlgebraicGeometry.Scheme.{u}) :=
  (integralOperationsGoodComplex l L W).lift
    ((integralOperationsGoodComplex l E W).ι ⋙
      (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ))
    (fun P ↦ scalarGood l E L ι W P)

attribute [local implicit_reducible] goodScalar

private def goodScalarComparison (W : AlgebraicGeometry.Scheme.{u}) :
    integralOperationsGoodLocalization l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      goodScalar l E L ι W ⋙ integralOperationsGoodLocalization l L W :=
  Functor.isoWhiskerLeft (integralOperationsGoodComplex l E W).ι
    (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors

attribute [local implicit_reducible] goodScalarComparison

private theorem goodScalarComparison_hom_app (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (goodScalarComparison l E L ι W).hom.app P =
      (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj := by
  rfl

private theorem scalarComp_factors
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app (DerivedCategory.Q.obj P) ≫
        (integralOrdinaryScalar l E F (j.comp ι) W).mapDerivedCategoryFactors.hom.app P =
      (integralOrdinaryDerivedScalar l L F j W).map
          ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P) ≫
        (integralOrdinaryScalar l L F j W).mapDerivedCategoryFactors.hom.app
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (integralOrdinaryScalarComp l E L ι W F j) (.up ℤ)).hom.app P) := by
  exact Functor.exactDerivedRestrictionComposition_hom_factors
    (integralOrdinaryScalar l E L ι W) (integralOrdinaryScalar l L F j W)
    (integralOrdinaryScalar l E F (j.comp ι) W)
    (integralOrdinaryScalarComp l E L ι W F j) P

attribute [local irreducible] integralOrdinaryDerivedScalarComp

private def goodScalarComp
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u}) :
    goodScalar l E L ι W ⋙ goodScalar l L F j W ≅ goodScalar l E F (j.comp ι) W :=
  NatIso.ofComponents (fun P ↦ (integralOperationsGoodComplex l F W).isoMk
    ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
      (.up ℤ)).app P.obj)) (by
      intro P Q a
      apply (integralOperationsGoodComplex l F W).ι.map_injective
      exact (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
        (.up ℤ)).hom.naturality a.hom)

private theorem goodScalarComp_factors
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (integralOrdinaryDerivedScalar l L F j W).map
        ((goodScalarComparison l E L ι W).hom.app P) ≫
      (goodScalarComparison l L F j W).hom.app ((goodScalar l E L ι W).obj P) ≫
      (integralOperationsGoodLocalization l F W).map
        ((goodScalarComp l E L ι F j W).hom.app P) =
    (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
        ((integralOperationsGoodLocalization l E W).obj P) ≫
      (goodScalarComparison l E F (j.comp ι) W).hom.app P := by
  exact (scalarComp_factors l E L ι F j W P.obj).symm

private def pullbackRep {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    integralOperationsGoodLocalization l E Y ⋙ integralDerivedPullback l E f ≅
      (integralOperationsGoodComplex l E Y).ι ⋙
        integralOperationsPullbackComplexFunctor l E f ⋙ DerivedCategory.Q :=
  integralDerivedPullbackComparison l E f

attribute [local implicit_reducible] pullbackRep

private theorem pullbackRep_hom_app {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (pullbackRep l E f).hom.app P =
      (integralDerivedPullbackComparison l E f).hom.app P := by
  rfl

private def pullbackSquare {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (integralOrdinaryDerivedScalar l E L ι X).obj
        (DerivedCategory.Q.obj ((integralOperationsPullbackComplexFunctor l E f).obj P.obj)) ⟶
      DerivedCategory.Q.obj ((integralOperationsPullbackComplexFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) :=
  (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
      ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
    DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj)

/-- The pullback representative square commutes with a coefficient tower.
Source: coefficient-comparison coherence, Stacks 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-pullback-tower-representatives).
Proof: naturality of the second scalar localization factor moves the first chain map
past that factor. Functoriality of Q combines the remaining chain maps, the chain
pullback tower equation rewrites their composite, and exact-derived scalar
composition identifies the two localization factors with the scalar associator. -/
theorem integralScalarPullbackTowerOnRepresentatives
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (integralOrdinaryDerivedScalar l L F j X).map
      ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
          ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
        DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj)) ≫
      (integralOrdinaryScalar l L F j X).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor l L f).obj
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
      DerivedCategory.Q.map (scalarPullbackChain l L F j f
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
      DerivedCategory.Q.map ((integralOperationsPullbackComplexFunctor l F f).map
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j)
          (.up ℤ)).hom.app P.obj)) =
    (integralOrdinaryDerivedScalarComp l E L ι X F j).hom.app
        (DerivedCategory.Q.obj ((integralOperationsPullbackComplexFunctor l E f).obj P.obj)) ≫
      (integralOrdinaryScalar l E F (j.comp ι) X).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
      DerivedCategory.Q.map (scalarPullbackChain l E F (j.comp ι) f P.obj) := by
  have hn := (integralOrdinaryScalar l L F j X).mapDerivedCategoryFactors.hom.naturality
    (scalarPullbackChain l E L ι f P.obj)
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
    integralScalarPullbackChainTower]
  erw [DerivedCategory.Q.map_comp]
  erw [← reassoc_of% (scalarComp_factors l E L ι F j X
    ((integralOperationsPullbackComplexFunctor l E f).obj P.obj))]

private theorem pullbackSquare_tower
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (integralOrdinaryDerivedScalar l L F j X).map
        ((pullbackSquare l E L ι f) P) ≫
      (pullbackSquare l L F j f) ((goodScalar l E L ι Y).obj P) ≫
      ((integralOperationsGoodComplex l F Y).ι ⋙
        integralOperationsPullbackComplexFunctor l F f ⋙ DerivedCategory.Q).map
        ((goodScalarComp l E L ι F j Y).hom.app P) =
    (integralOrdinaryDerivedScalarComp l E L ι X F j).hom.app
        (DerivedCategory.Q.obj ((integralOperationsPullbackComplexFunctor l E f).obj P.obj)) ≫
      (pullbackSquare l E F (j.comp ι) f) P := by
  simp only [pullbackSquare, Category.assoc]
  change (integralOrdinaryDerivedScalar l L F j X).map
      ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
          ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
        DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj)) ≫
      (integralOrdinaryScalar l L F j X).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor l L f).obj
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
      DerivedCategory.Q.map (scalarPullbackChain l L F j f
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
      DerivedCategory.Q.map ((integralOperationsPullbackComplexFunctor l F f).map
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j)
          (.up ℤ)).hom.app P.obj)) =
    (integralOrdinaryDerivedScalarComp l E L ι X F j).hom.app
        (DerivedCategory.Q.obj ((integralOperationsPullbackComplexFunctor l E f).obj P.obj)) ≫
      (integralOrdinaryScalar l E F (j.comp ι) X).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
      DerivedCategory.Q.map (scalarPullbackChain l E F (j.comp ι) f P.obj)
  exact integralScalarPullbackTowerOnRepresentatives l E L ι F j f P

end ScalarTowerDescent
end WeilConjectures
