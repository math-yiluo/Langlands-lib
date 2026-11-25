/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Tensor.TensorReductionFiniteComponents

/-! # Equation for the transported finite tensor component

Source: Stacks 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory pullbackTensorCalculus
attribute [local irreducible] pullbackTensorReductionEvaluationComplex
  coefficientScalarTensorIso coefficientEvaluationTensorIso
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- An explicit equation for the transported finite component.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-finite-component-equation). -/
theorem tensorReductionSystemFiniteComponent_eq (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    tensorReductionSystemFiniteComponent l E W P Q n =
      (tensorReductionEvaluationComplexIso l E W n).inv.app (G.obj T) ≫
        tensorReductionFiniteComponent l E W P Q n ≫
        (tensorReductionEvaluationComplexIso l E W n).hom.app B := by
  rfl

end WeilConjectures
