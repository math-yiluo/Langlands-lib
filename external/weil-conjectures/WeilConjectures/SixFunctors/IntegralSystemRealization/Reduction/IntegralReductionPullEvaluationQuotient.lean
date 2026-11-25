/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

/-! # Finite scalar pullback in the canonical quotient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalization_extension
    {C : Type*} [Category C] {A B D E F G H I J K : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : A ⟶ F) (e : F ⟶ G) (f : G ⟶ H) (g : H ⟶ E)
    (u : D ⟶ I) (v : I ⟶ J) (w : E ⟶ J) (k : H ⟶ K) (t : K ⟶ J)
    (h : a ≫ b ≫ c = d ≫ e ≫ f ≫ g)
    (hu : u ≫ v = c ≫ w) (hk : k ≫ t = g ≫ w) :
    a ≫ b ≫ u ≫ v = d ≫ e ≫ f ≫ k ≫ t := by
  rw [hu, reassoc_of% h, ← hk]

private theorem evaluation_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
    (pullbackTensorDerivedEvaluation l E f n).hom.app (DerivedCategory.Q.obj C) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C) ≫
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) =
      (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app C) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
          (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app C) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
            (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C)) := by
  exact (pullbackTensorDerivedEvaluation_existsUnique l E f n).exists.choose_spec C

/-- Transport of derived evaluation to the ordinary quotient model.
Source: Stacks Tag 07A6 (blueprint: lem-sf-integral-reduction-pull-evaluation-quotient). -/
theorem integralReductionPullEvaluationQuotient {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
    let C := ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P
    let κ := (pullbackTensorReductionEvaluationComplex l E Y n).inv.app P
    let I := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
    (pullbackTensorDerivedEvaluation l E f n).hom.app (DerivedCategory.Q.obj C) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
            DerivedCategory.Q.map κ) ≫
        I.mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P) =
      (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app C) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
          (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          ((pullbackTensorInverseEvaluationComplex l E f n).inv.app C ≫
            ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map κ) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
            (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let C := ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P
  let κ := (pullbackTensorReductionEvaluationComplex l E Y n).inv.app P
  let I := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  dsimp only
  have hi := I.mapDerivedCategoryFactors.hom.naturality κ
  dsimp only [Functor.comp_map] at hi
  have hn := (NatIso.mapHomologicalComplex
    (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.naturality κ
  have hk := congrArg (fun h ↦ DerivedCategory.Q.map h) hn
  simp only [DerivedCategory.Q.map_comp] at hk
  have hz := normalization_extension
    ((pullbackTensorDerivedEvaluation l E f n).hom.app (DerivedCategory.Q.obj C))
    ((finiteDerivedPullback l E n f).map
      ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C))
    (I.mapDerivedCategoryFactors.hom.app
      (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C))
    ((coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app C))
    ((coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C))
    (DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app C))
    (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C)))
    ((finiteDerivedPullback l E n f).map (DerivedCategory.Q.map κ))
    (I.mapDerivedCategoryFactors.hom.app
      (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P))
    (DerivedCategory.Q.map ((I.mapHomologicalComplex (.up ℤ)).map κ))
    (DerivedCategory.Q.map
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map κ))
    (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
        (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P)))
    (evaluation_normalization l E f n C) hi hk
  simpa only [Functor.map_comp, Category.assoc] using hz

end WeilConjectures.IntegralSystemRealization
