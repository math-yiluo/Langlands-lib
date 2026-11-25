/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus

/-! # Factorization through the composite ordinary evaluation mate

Source: Stacks Tags 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  sfIntrinsicPullback coefficientSequenceEvaluation
  pullbackTensorSequenceInverse pullbackTensorSystemComparison
  pullbackTensorInverseEvaluationComplex finitePullbackTensorConstruction
  coefficientTotalTensor DerivedCategory.Q DerivedCategory instCategoryDerivedCategory
  CochainComplex.IsKFlatIndependentCoefficients
  CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorCalculus pullbackTensorSequenceDerived
  finiteIntrinsicDerivedTensor finiteIntrinsicClosed

attribute [local instance] sfIntrinsicPullback_additive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Combine the two ordinary maps in the supplied exact-evaluation factorization.
Source: Stacks Tags 0941 and 03D2
(blueprint: lem-pur-completed-pullback-tensor-evaluation-factors).
Proof: specialize the supplied factorization equation at A. Functoriality of the
quotient identifies the two consecutive images with the image of their composite;
associativity gives the displayed factorization.
-/
theorem completedPullbackTensor_evaluation_factors {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f)
    (he : ∀ A : CochainComplex (coefficientSequenceModules l E Y) ℤ,
      e.hom.app (DerivedCategory.Q.obj A) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app A) ≫
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app A) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)))
    (A : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    e.hom.app (DerivedCategory.Q.obj A) ≫
      (finiteDerivedPullback l E n f).map
        ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app A) ≫
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
        f).mapDerivedCategoryFactors.hom.app _ =
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A) ≫
      (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map
        ((pullbackTensorInverseEvaluationComplex l E f n).inv.app A ≫
          (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
            (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)) := by
  have h := he A
  simpa only [Functor.map_comp, Category.assoc] using h

end WeilConjectures
