/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # The finite tensor of inverse reduction evaluations -/
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

/-- Tensor the two inverse reduction evaluations and restrict scalars.
Source: Stacks 07A4, 0941 (blueprint: def-pur-finite-tensor-reduction-comparison). -/
def pullbackTensorFiniteReductionComparison (W : Scheme.{u}) (n : ℕ) :
    ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).prod
      ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ))) ⋙
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).prod
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)))) ⋙
      coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) ⋙
      (scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ) ≅
      integralOperationsTensorLevel l E W n :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight
      (NatIso.prod (pullbackTensorReductionEvaluationComplex l E W n).symm
        (pullbackTensorReductionEvaluationComplex l E W n).symm)
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)))
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ))

end WeilConjectures
