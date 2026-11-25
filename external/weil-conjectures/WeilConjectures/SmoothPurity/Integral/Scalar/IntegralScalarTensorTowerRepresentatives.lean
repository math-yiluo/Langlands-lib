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
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorChainTower

/-! # Coherent scalar squares on tensor representatives

The exact scalar factors and the normalized chain maps form coherent squares before
localization. Source: coefficient-comparison coherence, Stacks 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-tensor-tower-representatives).
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
attribute [local implicit_reducible] goodScalar goodScalarComparison
  integralOperationsPullbackOnGood integralOperationsTensorOnGood
  integralOperationsGoodLocalization

private def tensorRep (W : AlgebraicGeometry.Scheme.{u}) :
    (integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W) ⋙ integralCompletedTensor l E W ≅
      ((integralOperationsGoodComplex l E W).ι.prod
        (integralOperationsGoodComplex l E W).ι) ⋙
          integralOperationsTensorComplexFunctor l E W ⋙ DerivedCategory.Q :=
  integralCompletedTensorComparison l E W

attribute [local implicit_reducible] tensorRep

private theorem tensorRep_hom_app (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory ×
      (integralOperationsGoodComplex l E W).FullSubcategory) :
    (tensorRep l E W).hom.app P =
      (integralCompletedTensorComparison l E W).hom.app P := by
  rfl

private def tensorSquare (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory ×
      (integralOperationsGoodComplex l E W).FullSubcategory) :
    (integralOrdinaryDerivedScalar l E L ι W).obj (DerivedCategory.Q.obj
        ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj))) ⟶
      DerivedCategory.Q.obj ((integralOperationsTensorComplexFunctor l L W).obj
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P.1.obj,
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P.2.obj)) :=
  (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
      ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj)) ≫
    DerivedCategory.Q.map (scalarTensorChain l E L ι W P.1.obj P.2.obj)

private theorem tensorSquare_app (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory ×
      (integralOperationsGoodComplex l E W).FullSubcategory) :
    (tensorSquare l E L ι W) P =
      (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
        ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj)) ≫
      DerivedCategory.Q.map (scalarTensorChain l E L ι W P.1.obj P.2.obj) := by rfl

/-- The completed-tensor representative square commutes with coefficient towers.
Source: coefficient-comparison coherence, Stacks 07A4, 08J9 and 08TC.
(blueprint: lem-pur-integral-scalar-tensor-tower-representatives).
Proof: move the first scalar tensor chain map across the second exact scalar
localization factor by naturality. The localized tensor chain tower equation
rewrites the three chain maps to the direct comparison preceded by the scalar
associator. The composition formula for scalar localization factors gives the
claimed representative equation. -/
theorem integralScalarTensorTowerOnRepresentatives
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory ×
      (integralOperationsGoodComplex l E W).FullSubcategory) :
    (integralOrdinaryDerivedScalar l L F j W).map
      ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj)) ≫
        DerivedCategory.Q.map (scalarTensorChain l E L ι W P.1.obj P.2.obj)) ≫
      (integralOrdinaryScalar l L F j W).mapDerivedCategoryFactors.hom.app
        ((integralOperationsTensorComplexFunctor l L W).obj
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P.1.obj,
            ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P.2.obj)) ≫
      DerivedCategory.Q.map (scalarTensorChain l L F j W
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P.1.obj)
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P.2.obj)) ≫
      DerivedCategory.Q.map ((integralOperationsTensorComplexFunctor l F W).map
        (CategoryTheory.Prod.mkHom
          ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
            (.up ℤ)).hom.app P.1.obj)
          ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
            (.up ℤ)).hom.app P.2.obj))) =
    (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
        (DerivedCategory.Q.obj
          ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj))) ≫
      (integralOrdinaryScalar l E F (j.comp ι) W).mapDerivedCategoryFactors.hom.app
        ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj)) ≫
      DerivedCategory.Q.map (scalarTensorChain l E F (j.comp ι) W P.1.obj P.2.obj) := by
  have hn := (integralOrdinaryScalar l L F j W).mapDerivedCategoryFactors.hom.naturality
    (scalarTensorChain l E L ι W P.1.obj P.2.obj)
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
    integralScalarTensorChainTower]
  erw [DerivedCategory.Q.map_comp]
  erw [← reassoc_of% (scalarComp_factors l E L ι F j W
    ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj)))]

private theorem tensorSquare_tower
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory ×
      (integralOperationsGoodComplex l E W).FullSubcategory) :
    (integralOrdinaryDerivedScalar l L F j W).map ((tensorSquare l E L ι W) P) ≫
      (tensorSquare l L F j W)
        (((goodScalar l E L ι W).prod (goodScalar l E L ι W)).obj P) ≫
      (((integralOperationsGoodComplex l F W).ι.prod
        (integralOperationsGoodComplex l F W).ι) ⋙
        integralOperationsTensorComplexFunctor l F W ⋙ DerivedCategory.Q).map
        ((NatIso.prod (goodScalarComp l E L ι F j W)
          (goodScalarComp l E L ι F j W)).hom.app P) =
    (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
        (DerivedCategory.Q.obj
          ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj))) ≫
      (tensorSquare l E F (j.comp ι) W) P := by
  let S := (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)
  simp only [tensorSquare_app, Category.assoc]
  change (integralOrdinaryDerivedScalar l L F j W).map
      ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj)) ≫
        DerivedCategory.Q.map (scalarTensorChain l E L ι W P.1.obj P.2.obj)) ≫
      (integralOrdinaryScalar l L F j W).mapDerivedCategoryFactors.hom.app
        ((integralOperationsTensorComplexFunctor l L W).obj
          (S.obj P.1.obj, S.obj P.2.obj)) ≫
      DerivedCategory.Q.map (scalarTensorChain l L F j W
        (S.obj P.1.obj) (S.obj P.2.obj)) ≫
      DerivedCategory.Q.map ((integralOperationsTensorComplexFunctor l F W).map
        (CategoryTheory.Prod.mkHom
          ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
            (.up ℤ)).hom.app P.1.obj)
          ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
            (.up ℤ)).hom.app P.2.obj))) =
    (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
        (DerivedCategory.Q.obj
          ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj))) ≫
      (integralOrdinaryScalar l E F (j.comp ι) W).mapDerivedCategoryFactors.hom.app
        ((integralOperationsTensorComplexFunctor l E W).obj (P.1.obj, P.2.obj)) ≫
      DerivedCategory.Q.map (scalarTensorChain l E F (j.comp ι) W P.1.obj P.2.obj)
  exact integralScalarTensorTowerOnRepresentatives l E L ι F j W P

end ScalarTowerDescent
end WeilConjectures
