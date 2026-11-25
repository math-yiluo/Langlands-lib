/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # All limits for constant scalar restriction

The all-shaped ordinary limit clause is isolated from the K-injective clause
of the scalar-limit restriction foundation.
(blueprint: lem-pur-compact-support-scalar-limit-restriction-limits).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures.PurStrictScalar
