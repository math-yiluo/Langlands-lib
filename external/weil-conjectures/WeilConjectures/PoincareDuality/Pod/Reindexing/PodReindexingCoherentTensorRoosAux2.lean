/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoosAux
import WeilConjectures.SmoothPurity.Supporting.Tensor.ReferenceTensorModelFactors

/-! # Derived reduction of the strict Roos normalization

The coherent tensor comparison is identified, on good representatives, with the strict
Roos map of a tower comparison, given a chain-level model `σ` of the coherent system tensor
comparison and the induced strict tower equation.

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC, 0941
(blueprint: stage3-pod-reindexing-coherent-tensor-roos).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A bifunctor applied to a pair of threefold composites, the middle one a product map.
Source: functoriality of a bifunctor. -/
theorem bifunctor_map_mkHom_comp₃ {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (T : C × C ⥤ D) (R : B ⥤ C) {P₀ P₃ Q₀ Q₃ : C} {P₁ P₂ Q₁ Q₂ : B}
    (a : P₀ ⟶ R.obj P₁) (a' : Q₀ ⟶ R.obj Q₁) (b : P₁ ⟶ P₂) (b' : Q₁ ⟶ Q₂)
    (c : R.obj P₂ ⟶ P₃) (c' : R.obj Q₂ ⟶ Q₃) :
    T.map (Prod.mkHom (a ≫ R.map b ≫ c) (a' ≫ R.map b' ≫ c')) =
      T.map (Prod.mkHom a a') ≫ T.map ((R.prod R).map (Prod.mkHom b b')) ≫
        T.map (Prod.mkHom c c') := by
  rw [← T.map_comp, ← T.map_comp]
  rfl

-- Without this, the unifier unfolds `integralOperationsRoos` into mapping cocones when comparing
-- `integralOperationsRoosFunctor.obj` with `integralOperationsTensorComplexFunctor.obj`.
attribute [local irreducible] integralOperationsRoos in
-- Unifying the pasting lemma with the reference realizations unfolds large functor objects.
/-- The derived part of the strict Roos normalization: if the coherent system tensor
comparison is localized from an actual chain map `σ`, and the tower map induced by `σ`
is the strict tower map `τ`, then the coherent tensor comparison is the strict Roos map
of `τ`.
Source: Stacks 07A4, 08TC, 0941 (blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem podReindexing_tensor_roos_of_strict
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (τ : (podReindexTower l E g).obj
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj)) ≅
      (integralOperationsTensorTowerFunctor l E X).obj
        (((podGoodReindex l E g A).obj P).obj, ((podGoodReindex l E g A).obj Q).obj))
    (σ : ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj,
            ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
              Q.obj)) ⟶
      (coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)).obj
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj
            ((podGoodReindex l E g A).obj P).obj,
            ((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj
              ((podGoodReindex l E g A).obj Q).obj))
    (hσ :
      letI : (isoReductionIntegralInverse l E g).Additive :=
        isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
      letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
        isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
      letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
        isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
      (integralComparisonDerivedSequencePullback l E g).map
          ((pullbackTensorSystemModel l E Y _ _
            (pullbackTensorReductionGood l E Y P) (pullbackTensorReductionGood l E Y Q)).hom ≫
          (podReindexCalculus l E Y).systemClosed.tensor.map
            (Prod.mkHom ((pullbackTensorReductionModel l E Y).inv.app P)
              ((pullbackTensorReductionModel l E Y).inv.app Q))) ≫
        (podReindexingSystemTensor l E g).hom.app
          ((podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj),
            (podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj Q.obj)) ≫
        (podReindexCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            (A.reduction.hom.app (DerivedCategory.Q.obj P.obj) ≫
              (podReindexCalculus l E X).reduction.map
                ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
              (pullbackTensorReductionModel l E X).hom.app ((podGoodReindex l E g A).obj P))
            (A.reduction.hom.app (DerivedCategory.Q.obj Q.obj) ≫
              (podReindexCalculus l E X).reduction.map
                ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj) ≫
              (pullbackTensorReductionModel l E X).hom.app ((podGoodReindex l E g A).obj Q))) ≫
        (pullbackTensorSystemModel l E X _ _
          (pullbackTensorReductionGood l E X ((podGoodReindex l E g A).obj P))
          (pullbackTensorReductionGood l E X ((podGoodReindex l E g A).obj Q))).inv =
      (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map σ)
    (hτ : (podReindexTower l E g).map (pullbackTensorTensorTower l E Y P.obj Q.obj).inv ≫
        (A.restricted _).hom ≫
        HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map σ) ≫
        (pullbackTensorTensorTower l E X ((podGoodReindex l E g A).obj P).obj
          ((podGoodReindex l E g A).obj Q).obj).hom = τ.hom) :
    letI : (isoReductionIntegralInverse l E g).Additive :=
      isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
    (podOrdinaryReindex l E g).map ((podReindexingTensorModel l E Y).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
      A.limit.hom.app ((podReindexCalculus l E Y).systemClosed.tensor.obj
        ((podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj),
          (podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj Q.obj))) ≫
      (coefficientSequenceLimit l E X).map ((podReindexingSystemTensor l E g).hom.app
        ((podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj),
          (podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj Q.obj))) ≫
      (coefficientSequenceLimit l E X).map ((podReindexCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (A.reduction.hom.app (DerivedCategory.Q.obj P.obj))
          (A.reduction.hom.app (DerivedCategory.Q.obj Q.obj)))) ≫
      (podReindexingTensorModel l E X).inv.app
        ((podOrdinaryReindex l E g).obj (DerivedCategory.Q.obj P.obj),
          (podOrdinaryReindex l E g).obj (DerivedCategory.Q.obj Q.obj)) ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj)
          ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
      (integralCompletedTensorComparison l E X).hom.app
        ((podGoodReindex l E g A).obj P, (podGoodReindex l E g A).obj Q) =
      (podOrdinaryReindex l E g).map
        ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map
        ((A.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).hom ≫
          integralOperationsRoosFunctor.map τ.hom) := by
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  have hY := podReindexingTensorModel_hom_app_good l E Y P Q
  have hrefY := pullbackTensorReferenceTensorModel_hom l E Y P Q
  have hrefX := pullbackTensorReferenceTensorModel_hom l E X
    ((podGoodReindex l E g A).obj P) ((podGoodReindex l E g A).obj Q)
  have hXi := podReindexingTensorModel_inv_app_good l E X
    ((podGoodReindex l E g A).obj P) ((podGoodReindex l E g A).obj Q)
  have hXn := (podReindexingTensorModel l E X).inv.naturality
    (Prod.mkHom ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj)
      ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj))
  have hfac := (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors_hom_naturality
    (integralOperationsRoosFunctor.map (pullbackTensorTensorTower l E Y P.obj Q.obj).hom)
  have hroos := congrArg (fun f ↦ DerivedCategory.Q.map f)
    (hA.2.2.2.2.2.2.2.2.2.2.2.2.1 _ _ (pullbackTensorTensorTower l E Y P.obj Q.obj).hom)
  simp only [Functor.map_comp] at hroos
  have hlim := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj,
            ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
              Q.obj))
  rw [podLimitRoos_eq_pullbackTensorLimitRoos, podLimitRoos_eq_pullbackTensorLimitRoos] at hlim
  have hlimnat := pullbackTensorLimitRoos_naturality l E X σ
  have hlim' : (podOrdinaryReindex l E g).map (pullbackTensorLimitRoos l E Y
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj,
            ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
              Q.obj))).hom ≫
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app
        (integralOperationsRoosFunctor.obj (pullbackTensorRestrictedTower l E Y
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj,
            ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
              Q.obj)))) ≫
      DerivedCategory.Q.map (A.roos (pullbackTensorRestrictedTower l E Y
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj,
            ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
              Q.obj)))).hom ≫
      (integralOperationsRoosFunctor ⋙ DerivedCategory.Q).map (A.restricted
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj,
            ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
              Q.obj))).hom =
    A.limit.hom.app (DerivedCategory.Q.obj
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj,
            ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
              Q.obj))) ≫
      (coefficientSequenceLimit l E X).map
        ((integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app _) ≫
      (pullbackTensorLimitRoos l E X _).hom := hlim
  dsimp only at hrefY hrefX
  refine coherentTensorRoos_paste (podOrdinaryReindex l E g) (coefficientSequenceLimit l E Y)
    (coefficientSequenceLimit l E X) (integralComparisonDerivedSequencePullback l E g) A.limit.hom
    (integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
    (refY := pullbackTensorReferenceTensorModel l E Y P Q)
    (refX := pullbackTensorReferenceTensorModel l E X
      ((podGoodReindex l E g A).obj P) ((podGoodReindex l E g A).obj Q))
    (hY := hY) (hXn := hXn) (hXi := hXi) (hrefX := hrefX) (hrefY := hrefY)
    (hfac := hfac) (hroos := hroos) (hτ := hτ) (hlim := hlim') (hlimnat := hlimnat)
    (hσ := hσ) (hk₁ := ?_) (hk₂ := ?_) (hR := ?_) (hw := ?_) (hsplit := ?_)
  · exact ((podReindexCalculus l E Y).systemClosed.tensor.mapIso
      (Iso.prod ((pullbackTensorReductionModel l E Y).app P)
        ((pullbackTensorReductionModel l E Y).app Q))).hom_inv_id
  · exact Iso.inv_hom_id _
  · exact ((podReindexTower l E g).mapIso (pullbackTensorTensorTower l E Y P.obj Q.obj)).hom_inv_id
  · exact bifunctor_map_mkHom_comp₃ (podReindexCalculus l E X).systemClosed.tensor
      (podReindexCalculus l E X).reduction _ _ _ _ _ _
  · exact Functor.map_comp _ _ _

end WeilConjectures
