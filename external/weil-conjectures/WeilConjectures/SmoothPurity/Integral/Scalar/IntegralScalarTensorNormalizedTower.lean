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
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorTowerRepresentatives
import WeilConjectures.CategoryTheory.SmoothPurity.FunctorSquareTowerDescent

/-! # Descent of normalized scalar tensor tower comparisons

The exact scalar factors and the normalized chain maps form coherent squares before
localization. Source: coefficient-comparison coherence, Stacks 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-tensor-normalized-tower).
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
attribute [local irreducible] goodScalarComparison pullbackRep tensorRep

private theorem tensorNormalizedSquare (W : AlgebraicGeometry.Scheme.{u})
    (α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W)
    (hα : ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l L W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (integralCompletedTensorComparison l L W).hom.app
            (⟨_, scalarGood l E L ι W P⟩, ⟨_, scalarGood l E L ι W Q⟩))
    (P : (integralOperationsGoodComplex l E W).FullSubcategory ×
      (integralOperationsGoodComplex l E W).FullSubcategory) :
    (integralOrdinaryDerivedScalar l E L ι W).map ((tensorRep l E W).hom.app P) ≫
        (tensorSquare l E L ι W) P =
      (α).hom.app
          ((integralOperationsGoodLocalization l E W).obj P.1,
            (integralOperationsGoodLocalization l E W).obj P.2) ≫
        (integralCompletedTensor l L W).map (CategoryTheory.Prod.mkHom
          ((goodScalarComparison l E L ι W).hom.app P.1)
          ((goodScalarComparison l E L ι W).hom.app P.2)) ≫
        (tensorRep l L W).hom.app
          (((goodScalar l E L ι W).prod (goodScalar l E L ι W)).obj P) := by
  simp only [tensorRep_hom_app, goodScalarComparison_hom_app, tensorSquare_app]
  exact hα P.1 P.2

/-- Normalized scalar tensor comparisons respect coefficient towers.
Source: coefficient-comparison coherence, Stacks 04VK, 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-tensor-normalized-tower).
Proof: the specified normalization equations identify the comparison squares on
good representatives. The scalar associator factorization and the chain tower
identity give the two representative associator equations. Apply faithful
localization descent to these three squares. For tensor pairs use the product
localization, whose restriction is fully faithful in both variables. -/
theorem integralScalarTensorNormalizedTower
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W)
    (β : integralCompletedTensor l L W ⋙ integralOrdinaryDerivedScalar l L F j W ≅
      (integralOrdinaryDerivedScalar l L F j W).prod
        (integralOrdinaryDerivedScalar l L F j W) ⋙ integralCompletedTensor l F W)
    (γ : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E F (j.comp ι) W ≅
      (integralOrdinaryDerivedScalar l E F (j.comp ι) W).prod
        (integralOrdinaryDerivedScalar l E F (j.comp ι) W) ⋙ integralCompletedTensor l F W)
    (hα : ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l L W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (integralCompletedTensorComparison l L W).hom.app
            (⟨_, scalarGood l E L ι W P⟩, ⟨_, scalarGood l E L ι W Q⟩))
    (hβ : ∀ P Q : (integralOperationsGoodComplex l L W).FullSubcategory,
        (integralOrdinaryDerivedScalar l L F j W).map
            ((integralCompletedTensorComparison l L W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l L F j W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l L W).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l L F j W P.obj Q.obj) =
        β.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l F W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l L F j W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l L F j W).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (integralCompletedTensorComparison l F W).hom.app
            (⟨_, scalarGood l L F j W P⟩, ⟨_, scalarGood l L F j W Q⟩))
    (hγ : ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E F (j.comp ι) W).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l E F (j.comp ι) W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E F (j.comp ι) W P.obj Q.obj) =
        γ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l F W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E F (j.comp ι) W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E F (j.comp ι) W).mapDerivedCategoryFactors.hom.app
                Q.obj)) ≫
          (integralCompletedTensorComparison l F W).hom.app
            (⟨_, scalarGood l E F (j.comp ι) W P⟩, ⟨_, scalarGood l E F (j.comp ι) W Q⟩)) :
    ∀ M N : DerivedCategory (integralTowerModules l E W),
      (integralOrdinaryDerivedScalar l L F j W).map
          ((α).hom.app (M, N)) ≫
        (β).hom.app
          ((integralOrdinaryDerivedScalar l E L ι W).obj M,
            (integralOrdinaryDerivedScalar l E L ι W).obj N) ≫
        (integralCompletedTensor l F W).map (CategoryTheory.Prod.mkHom
          ((integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app M)
          ((integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app N)) =
      (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
          ((integralCompletedTensor l E W).obj (M, N)) ≫
        (γ).hom.app (M, N) := by
  let q := integralOperationsGoodLocalization l E W
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E W
  have hh := functorSquareTowerDescent (q.prod q)
    ((integralOperationsGoodLocalization l L W).prod (integralOperationsGoodLocalization l L W))
    ((integralOperationsGoodLocalization l F W).prod (integralOperationsGoodLocalization l F W))
    ((goodScalar l E L ι W).prod (goodScalar l E L ι W))
    ((goodScalar l L F j W).prod (goodScalar l L F j W))
    ((goodScalar l E F (j.comp ι) W).prod (goodScalar l E F (j.comp ι) W))
    (NatIso.prod (goodScalarComp l E L ι F j W) (goodScalarComp l E L ι F j W))
    ((integralOrdinaryDerivedScalar l E L ι W).prod (integralOrdinaryDerivedScalar l E L ι W))
    ((integralOrdinaryDerivedScalar l L F j W).prod (integralOrdinaryDerivedScalar l L F j W))
    ((integralOrdinaryDerivedScalar l E F (j.comp ι) W).prod
      (integralOrdinaryDerivedScalar l E F (j.comp ι) W))
    (NatIso.prod (integralOrdinaryDerivedScalarComp l E L ι W F j)
      (integralOrdinaryDerivedScalarComp l E L ι W F j))
    (integralOrdinaryDerivedScalar l E L ι W) (integralOrdinaryDerivedScalar l L F j W)
    (integralOrdinaryDerivedScalar l E F (j.comp ι) W)
    (integralOrdinaryDerivedScalarComp l E L ι W F j)
    (integralCompletedTensor l E W) (integralCompletedTensor l L W)
    (integralCompletedTensor l F W) _ _ _
    (tensorRep l E W) (tensorRep l L W) (tensorRep l F W)
    (NatIso.prod (goodScalarComparison l E L ι W) (goodScalarComparison l E L ι W))
    (NatIso.prod (goodScalarComparison l L F j W) (goodScalarComparison l L F j W))
    (NatIso.prod (goodScalarComparison l E F (j.comp ι) W)
      (goodScalarComparison l E F (j.comp ι) W))
    (tensorSquare l E L ι W) (tensorSquare l L F j W) (tensorSquare l E F (j.comp ι) W)
    (α) (β)
    (γ)
    (Localization.fullyFaithfulWhiskeringLeft (q.prod q) (V.prod V) _).faithful
    (tensorNormalizedSquare l E L ι W α hα)
    (tensorNormalizedSquare l L F j W β hβ)
    (tensorNormalizedSquare l E F (j.comp ι) W γ hγ)
    (fun P ↦ by
      apply CategoryTheory.Prod.hom_ext
      · exact goodScalarComp_factors l E L ι F j W P.1
      · exact goodScalarComp_factors l E L ι F j W P.2)
    (tensorSquare_tower l E L ι F j W)
  intro M N
  exact hh (M, N)

end ScalarTowerDescent
end WeilConjectures
