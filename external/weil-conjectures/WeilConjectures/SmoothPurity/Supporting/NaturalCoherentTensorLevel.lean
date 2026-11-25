/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.SmoothPurity.Finite.FiniteTensorReductionComparison
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality

/-! # The natural comparison of coherent tensor levels -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint HasDerivedCategory.standard
  coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingSheafUnrestricted
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Reorder scalar restriction and evaluation on complexes.
Source: Stacks 07A4, 0941 (blueprint: def-pur-natural-coherent-tensor-level). -/
def pullbackTensorRestrictionEvaluation (W : Scheme.{u}) (n : ℕ) :=
  Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceRestriction l E W ⋙
      (evaluation ℕᵒᵖ (integralTowerModules l E W)).obj (op n))) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (coefficientSequenceEvaluation l E W n ⋙
        scalarReductionRestriction l E W n)) (.up ℤ)).symm

/-- Package the normalized tensor evaluation maps as a natural isomorphism.
Source: Stacks 07A4, 0941 (blueprint: def-pur-natural-coherent-tensor-level). -/
def pullbackTensorEvaluationComparison (W : Scheme.{u}) (n : ℕ) :
    coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W) ⋙
      (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ) ≅
    (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).prod
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ))) ⋙
      coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) :=
  NatIso.ofComponents (fun C ↦ coefficientEvaluationTensorIso l E W n C.1 C.2)
    (fun g ↦ pullbackTensorEvaluationTensor_naturality l E W n g.1 g.2)

attribute [local irreducible] coefficientTotalTensor in
/-- A natural comparison with the actual finite tensor-level functor.
Source: Stacks 07A4, 0941
(blueprint: def-pur-natural-coherent-tensor-level).
The construction composes reordering, the generator-normalized evaluation tensor
comparison and the tensor of inverse reduction evaluations, followed by scalar
restriction. Their naturality supplies the naturality field. -/
def pullbackTensorTensorLevelComparison (W : Scheme.{u}) (n : ℕ) :
    (((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).prod
      ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ))) ⋙
      coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) ⋙
      (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙
      (evaluation ℕᵒᵖ (CochainComplex (integralTowerModules l E W) ℤ)).obj (op n) ≅
    integralOperationsTensorTowerFunctor l E W ⋙
      (evaluation ℕᵒᵖ (CochainComplex (integralTowerModules l E W) ℤ)).obj (op n) := by
  let R := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let S := (scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)
  let B := coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
  exact Functor.isoWhiskerLeft (R.prod R)
    (Functor.isoWhiskerLeft B (pullbackTensorRestrictionEvaluation l E W n) ≪≫
      Functor.isoWhiskerRight (pullbackTensorEvaluationComparison l E W n) S) ≪≫
    pullbackTensorFiniteReductionComparison l E W n

end WeilConjectures
