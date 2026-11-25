/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleData
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientComputationSquareLeft
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientComputationSquareRight

/-! # Universal comparison squares for quotient chain maps

Source: blueprint coefficient quotient proof, Steps 2 and 3; Stacks Tags 03EK and 06YY.
(blueprint: lem-coef-compact-support-quotient-computation-squares).
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

end WeilConjectures
