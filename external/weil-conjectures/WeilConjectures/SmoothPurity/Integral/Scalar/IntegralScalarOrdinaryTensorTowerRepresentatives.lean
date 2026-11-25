/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
public import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralOrdinaryTensorChain

import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackTowerRepresentatives

/-! # Coherent ordinary tensor scalar squares on representatives

The exact scalar factors and the normalized chain maps form coherent squares before
localization. Source: coefficient-comparison coherence, Stacks 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-ordinary-tensor-tower-representatives).
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

attribute [local irreducible] integralOrdinaryScalarComp integralOrdinaryDerivedScalarComp

/-- The localized ordinary tensor chain square respects coefficient towers.
Source: coefficient-comparison coherence, Stacks 03EL, 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-ordinary-tensor-tower-representatives).
Proof: naturality of the second exact scalar localization factor interchanges it
with the first tensor chain comparison. Combine the three Q-images, apply the
given ordinary chain tower equation, then separate the Q-image of the result.
The scalar factorization composition formula identifies the remaining factors
with the output derived scalar associator followed by the direct scalar factor. -/
theorem integralScalarOrdinaryTensorTowerOnRepresentatives
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (μ : coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W))
    (ν : coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l L W) ⋙
          (integralOrdinaryScalar l L F j W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l L F j W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l L F j W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l F W))
    (ξ : coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E F (j.comp ι) W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E F (j.comp ι) W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E F (j.comp ι) W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l F W))
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (hμ : ((integralOrdinaryScalar l L F j W).mapHomologicalComplex (.up ℤ)).map
        (μ.hom.app (P, Q)) ≫
      ν.hom.app
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l F W)).map (CategoryTheory.Prod.mkHom
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app P)
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app Q)) =
    (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
      (.up ℤ)).hom.app
        ((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≫
      ξ.hom.app
        (P, Q)) :
    (integralOrdinaryDerivedScalar l L F j W).map
      ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≫
        DerivedCategory.Q.map (μ.hom.app
          (P, Q))) ≫
      (integralOrdinaryScalar l L F j W).mapDerivedCategoryFactors.hom.app
        ((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l L W)).obj
            (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      DerivedCategory.Q.map (ν.hom.app
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      DerivedCategory.Q.map ((coefficientTotalTensor.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l F W)).map
        (CategoryTheory.Prod.mkHom
          ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
            (.up ℤ)).hom.app P)
          ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
            (.up ℤ)).hom.app Q))) =
    (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
        (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, u + 1, u}
          (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q))) ≫
      (integralOrdinaryScalar l E F (j.comp ι) W).mapDerivedCategoryFactors.hom.app
        ((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≫
      DerivedCategory.Q.map (ξ.hom.app
        (P, Q)) := by
  have hn := (integralOrdinaryScalar l L F j W).mapDerivedCategoryFactors.hom.naturality
    (μ.hom.app (P, Q))
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  erw [hμ]
  erw [DerivedCategory.Q.map_comp]
  erw [← reassoc_of% (scalarComp_factors l E L ι F j W
    ((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)))]

end WeilConjectures
