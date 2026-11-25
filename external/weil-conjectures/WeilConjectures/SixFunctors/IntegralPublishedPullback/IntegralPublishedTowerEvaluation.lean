/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackStrictFiniteComponent
import all WeilConjectures.SixFunctors.IntegralPublishedPullback.IntegralPublishedFiniteEvaluation
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Finite projections of the published completed pullback tower

Source: Stacks 08TC, 0941, 099N; the fixed quotient and Roos normalizations.
(blueprint: lem-sf-integral-published-tower-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.integralDerivedPullback WeilConjectures.pullbackTensorCalculus
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.coefficientFiniteDerivedRestriction
  WeilConjectures.integralComparisonDerivedSequencePullback
  WeilConjectures.coefficientConstantTowerLimit
  WeilConjectures.coefficientConstantTowerEvaluation
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.integralOperationsRoos WeilConjectures.integralOperationsRoosFunctor
  WeilConjectures.integralOperationsGoodComplex
  WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.integralOperationsPullbackOnGood
  WeilConjectures.integralOperationsPullbackComplexFunctor
  WeilConjectures.integralPullbackFiniteComplex
  WeilConjectures.integralOperationsPullbackTowerFunctor
  WeilConjectures.integralOperationsPullbackLevel WeilConjectures.integralOperationsRestrict
  WeilConjectures.scalarReductionDerivedRestriction
  HomologicalComplex.complexOfFunctorsToFunctorToComplex HomologicalComplex.asFunctor
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.pullbackTensorConstantLimit WeilConjectures.pullbackTensorTowerQ
  WeilConjectures.pullbackTensorRestrictedTower
  WeilConjectures.pullbackTensorSequenceDerived
  WeilConjectures.pullbackTensorReferencePullback
  CochainComplex.IsKFlatResolutionIndependentCoefficients
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPublishedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Naturality of the actual Roos projection. Source: Stacks 08TC.
Expand the Roos map in its first cone coordinate, then apply product-map naturality.
(blueprint: lem-sf-integral-published-tower-evaluation). -/
private theorem roos_projection_natural {W : Scheme.{u}}
    {A B : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ}
    (a : A ⟶ B) (n : ℕ) :
    DerivedCategory.Q.map (integralOperationsRoosFunctor.map a) ≫
        integralOperationRoosProjection l E W B n =
      integralOperationRoosProjection l E W A n ≫ DerivedCategory.Q.map (a.app (op n)) := by
  unfold integralOperationRoosProjection
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  erw [← Category.assoc, (IntegralAmbient.roosMap_coordinates a).1, Category.assoc,
    Pi.map_π]
  exact (Category.assoc _ _ _).symm

private theorem published_roos_projection (W : Scheme.{u})
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    (pullbackTensorRoosModel l E W).hom.app C ≫
      integralOperationRoosProjection l E W C.asFunctor n =
      (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj C) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app C := by
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [I.IsKInjective] :
      (pullbackTensorRoosModel l E W).hom.app I ≫
        integralOperationRoosProjection l E W I.asFunctor n =
        (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj I) ≫
          (coefficientConstantTowerEvaluationFactors l E W n).hom.app I := by
    have hn := (pullbackTensorRoosModel_existsUnique l E W).exists.choose_spec I
    change (pullbackTensorRoosModel l E W).hom.app I = _ at hn
    rw [hn]
    unfold integralOperationRoosProjection
    rw [Category.assoc, ← DerivedCategory.Q.map_comp]
    have h : pullbackTensorRoosUnit l E W I ≫
        CochainComplex.mappingCocone.fst
          (scalarRoosBoundary I.asFunctor) ≫
        Pi.π (fun m ↦ I.asFunctor.obj (op m)) n =
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I := by
      dsimp only [pullbackTensorRoosUnit, scalarRoosBoundary, HomologicalComplex.asFunctor,
        HomologicalComplex.complexOfFunctorsToFunctorToComplex]
      rw [CochainComplex.mappingCocone.lift_fst_assoc]
      dsimp only [pullbackTensorRoosAugmentation]
      exact Pi.lift_comp_π
        (fun m ↦ (NatTrans.mapHomologicalComplex (lim.π (op m)) (.up ℤ)).app I) n
    rw [h]
    exact ((coefficientConstantTowerProjection_exists l E W n).choose_spec.1 I).symm
  obtain ⟨I, hI, f, _, hf⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : QuasiIso f := hf
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)
  apply (cancel_mono (DerivedCategory.Q.map
    ((V.mapHomologicalComplex (.up ℤ)).map f))).1
  have hv := V.mapDerivedCategoryFactors.hom.naturality f
  have hp := (coefficientConstantTowerProjection l E W n).naturality
    (DerivedCategory.Q.map f)
  have hθ := (pullbackTensorRoosModel l E W).hom.naturality f
  dsimp only [Functor.comp_map] at hv hθ
  erw [Category.assoc, ← roos_projection_natural l E
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n]
  rw [← Category.assoc, ← hθ, Category.assoc]
  erw [hi I]
  rw [Category.assoc, ← hv]
  exact (reassoc_of% hp) _

/-- The published limit/Roos bridge preserves finite projections. Source: Stacks 08TC.
Compute on K-injective towers using the prescribed Roos unit, extend by naturality,
then use the exact scalar-restriction factorization.
(blueprint: lem-sf-integral-published-tower-evaluation). -/
private theorem published_bridge_projection (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (pullbackTensorLimitRoos l E W C).hom ≫
        integralOperationRoosProjection l E W
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex
            (.up ℤ)).obj C).asFunctor n =
      (coefficientSequenceProjection l E W n).app (DerivedCategory.Q.obj C) ≫
        (integralComparisonRestrictedEvaluationFactors l E W C n).hom := by
  dsimp only [pullbackTensorLimitRoos, Iso.trans_hom, Functor.mapIso_hom]
  erw [Category.assoc, published_roos_projection l E W
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C) n]
  unfold coefficientSequenceProjection integralComparisonRestrictedEvaluationFactors
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% ((coefficientConstantTowerProjection l E W n).naturality
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app C))]

/-- The strict pullback tower component is the normalized finite evaluation.
Source: Stacks 0941 and 099N. Transport the exact restriction square to complexes,
apply the normalization of pullbackTensorDerivedEvaluation, and cancel the
inverse-image evaluation and representative quotient isomorphisms.
(blueprint: lem-sf-integral-published-tower-evaluation). -/
theorem published_tower_finite_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    let C := ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P
    let D := ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C
    (integralComparisonRestrictedEvaluationFactors l E X D n).hom ≫
      DerivedCategory.Q.map (pullbackTensorPullbackTowerLevel l E f P n).hom ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
        (integralPullbackFiniteComplex l E f P n) =
    (coefficientFiniteDerivedRestriction l E X n).map
      ((coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.inv.app C) ≫
        (pullbackTensorDerivedEvaluation l E f n).hom.app (DerivedCategory.Q.obj C) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
            DerivedCategory.Q.map ((pullbackTensorReductionEvaluationComplex l E Y n).inv.app P)) ≫
        (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
          ).mapDerivedCategoryFactors.hom.app
          ((unrestrictedIntegralFiniteComplex l E Y n).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
            (.up ℤ)).inv.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P))) := by
  dsimp only
  let C := ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P
  let D := ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C
  let R := scalarReductionRestriction l E X n
  let T := (integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)
  let j := (pullbackTensorInverseEvaluationComplex l E f n).inv.app C ≫
    T.map ((pullbackTensorReductionEvaluationComplex l E Y n).inv.app P)
  have hq : (integralComparisonRestrictedEvaluationFactors l E X D n).hom ≫
      DerivedCategory.Q.map (pullbackTensorPullbackTowerLevel l E f P n).hom ≫
      R.mapDerivedCategoryFactors.inv.app (integralPullbackFiniteComplex l E f P n) =
    R.mapDerivedCategory.map
      ((coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app D ≫
        DerivedCategory.Q.map j) := by
    have hn := R.mapDerivedCategoryFactors.hom.naturality j
    dsimp only [Functor.comp_map] at hn
    dsimp only [pullbackTensorPullbackTowerLevel, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app_inv, Iso.app_hom]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% (restricted_level_factors l E X D n)]
    dsimp only [R] at hn ⊢
    simp only [← Functor.map_comp, ← Functor.map_comp_assoc]
    change _ ≫ (R.mapDerivedCategoryFactors.hom.app _ ≫
      (DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map j) ≫
        R.mapDerivedCategoryFactors.inv.app _)) = _
    erw [reassoc_of% hn.symm]
    dsimp only [R, coefficientFiniteDerivedRestriction, scalarReductionDerivedRestriction]
    simp only [Iso.hom_inv_id_app]
    erw [Category.comp_id]
    rw [← Functor.map_comp]
  rw [hq]
  apply congrArg R.mapDerivedCategory.map
  have hf := finite_evaluation_component l E f C n
    ((unrestrictedIntegralFiniteComplex l E Y n).obj P)
    ((pullbackTensorReductionEvaluationComplex l E Y n).app P).symm
  have he := congrArg (fun a ↦ (coefficientSequenceDerivedEvaluation l E X n).map
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.inv.app C) ≫ a) hf
  simp only [C, Iso.app_inv, Iso.symm_hom,
    ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id_app] at he
  have hid := (coefficientSequenceDerivedEvaluation l E X n).map_id
    (DerivedCategory.Q.obj D)
  erw [hid, Category.id_comp] at he
  exact he

end WeilConjectures.IntegralPublishedPullback
