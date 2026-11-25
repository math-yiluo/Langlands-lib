/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.ExpressionRecursion.IntegralExpressionTransposeIsIso
import WeilConjectures.SixFunctors.IntegralSystemRealization.ExpressionRecursion.IntegralExpressionCanonicalEquations

/-! # Direct compactification agreement of the canonical comparison -/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.ExpressionRecursion
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem inverseOrZero_eq_inv {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) [IsIso f] : GeneratorReduction.inverseOrZero f = inv f := by
  simp only [GeneratorReduction.inverseOrZero, dite_eq_left (inferInstance : IsIso f)]

end WeilConjectures.IntegralSystemRealization.ExpressionRecursion
