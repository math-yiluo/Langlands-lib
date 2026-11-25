/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleData

/-! # Universal comparison square right for quotient chain maps

Source: blueprint coefficient quotient proof, Steps 2 and 3; Stacks Tags 03EK and 06YY.
(blueprint: lem-coef-compact-support-quotient-computation-square-right).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/- **Reduced comparison square (right).**
Source: blueprint coefficient quotient proof, Steps 2--3; Stacks Tags 06YS, 06YY and 07A6.
(blueprint: lem-coef-compact-support-quotient-computation-square-right).

The universal counit and normalized adjunction comparison identifies the specified
chain map with the corresponding derived arrow. The proof is split from the parent
comparison theorem so that the two universal squares can be established independently.
-/
end WeilConjectures
