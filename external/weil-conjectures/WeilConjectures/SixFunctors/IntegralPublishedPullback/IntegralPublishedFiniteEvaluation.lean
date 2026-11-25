/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackStrictFiniteComponent
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Exact finite evaluation factors for the published pullback

Source: Stacks 08TC, 0941, 099N; the fixed quotient and Roos normalizations.
(blueprint: lem-sf-integral-published-finite-evaluation).
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

private theorem derived_square_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso F G) ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso H I).symm).inv.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        (((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) ≪≫
          NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).symm).hom.app K) =
    I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) := by
  have hc : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (H ⋙ I)) (.up ℤ)).inv.app K = 𝟙 _ := by
    apply (cancel_epi ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (H ⋙ I)) (.up ℤ)).hom.app K)).1
    rw [Iso.hom_inv_id_app, Functor.mapHomologicalComplexCompIso_refl_hom_app,
      Category.comp_id]
  apply (cancel_epi (((Functor.mapDerivedCategoryCompIso F G) ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso H I).symm).hom.app (DerivedCategory.Q.obj K))).1
  simp only [Iso.hom_inv_id_app_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
    (DerivedCategory.Q.obj K))).1
  simp only [Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  simp only [Functor.mapHomologicalComplexCompIso_refl_hom_app, hc,
    Category.id_comp, Category.comp_id]
  rfl

/-- Localization factors of exact restriction commute with finite evaluation.
Source: Stacks 0941. Cancel the derived composition isomorphisms, apply the
naturality of the localized square, and use the composition-factor equations.
(blueprint: lem-sf-integral-published-finite-evaluation). -/
private theorem restricted_level_factors (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (integralComparisonRestrictedEvaluationFactors l E W C n).hom ≫
      DerivedCategory.Q.map (pullbackTensorRestrictedLevel l E W C n).hom =
    (coefficientFiniteDerivedRestriction l E W n).map
        ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C) ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) := by
  have h := derived_square_factors
    (coefficientSequenceRestriction l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (coefficientSequenceEvaluation l E W n)
    (scalarReductionRestriction l E W n)
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) C
  simpa only [integralComparisonRestrictedEvaluationFactors, coefficientRestrictedEvaluationIso,
    coefficientSequenceDerivedRestriction, coefficientConstantTowerEvaluation,
    coefficientConstantTowerEvaluationFactors, coefficientFiniteDerivedRestriction,
    coefficientSequenceDerivedEvaluation, scalarReductionDerivedRestriction,
    integralTowerModules, pullbackTensorRestrictedLevel, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] using h

/-- Normalized finite evaluation transported along a finite representative isomorphism.
Source: Stacks 0941 and 099N. Apply the prescribed derived evaluation normalization,
use naturality of the exact pullback factors and the intrinsic comparison, and
cancel that comparison with its inverse.
(blueprint: lem-sf-integral-published-finite-evaluation). -/
theorem finite_evaluation_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ)
    (A : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (κ : (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) ≅ A) :
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app C) ≫
      (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
        (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app C) ≫
      DerivedCategory.Q.map
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map κ.hom) =
    (pullbackTensorDerivedEvaluation l E f n).hom.app (DerivedCategory.Q.obj C) ≫
      (finiteDerivedPullback l E n f).map
        ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map κ.hom) ≫
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
        ).mapDerivedCategoryFactors.hom.app A ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
          (.up ℤ)).inv.app A) := by
  let F := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  let α := NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)
  have h := (pullbackTensorDerivedEvaluation_existsUnique l E f n).exists.choose_spec
  change pullbackTensorDerivedEvaluationNormalization l E f n
    (pullbackTensorDerivedEvaluation l E f n) at h
  unfold pullbackTensorDerivedEvaluationNormalization at h
  have hk := h C
  have hn := F.mapDerivedCategoryFactors.hom.naturality κ.hom
  have ha := α.inv.naturality κ.hom
  dsimp only [Functor.comp_map] at hn ha
  symm
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  have hk' := congrArg (fun t ↦ t ≫
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map κ.hom) ≫
    DerivedCategory.Q.map (α.inv.app A)) hk
  simp only [Category.assoc] at hk'
  erw [hk']
  have ha' := congrArg DerivedCategory.Q.map ha
  simp only [Functor.map_comp] at ha'
  erw [ha']
  simp only [α, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]

end WeilConjectures.IntegralPublishedPullback
