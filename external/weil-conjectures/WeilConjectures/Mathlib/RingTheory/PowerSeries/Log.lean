/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Tactic.LinearCombination

/-!
# Complements on the formal logarithm

## Main results

- `PowerSeries.one_add_X_mul_derivative_log`: `(1 + X) * (log (1 + X))' = 1`.
- `PowerSeries.mul_derivative_logOf`: the formal logarithm is a logarithmic primitive, i.e.
  `f * (logOf f)' = f'` whenever `f` has constant coefficient `1`.
-/

@[expose] public section

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The derivative of `log (1 + X)` is the inverse of `1 + X`. -/
theorem one_add_X_mul_derivative_log : (1 + X) * d⁄dX (log A) = 1 := by
  simpa only [mul_comm] using (derivative_log_mul_one_add_X (A := A))

/-- The formal logarithm `logOf f` of a series `f` with constant coefficient `1` is a
logarithmic primitive of `f`: `f * (logOf f)' = f'`. -/
theorem mul_derivative_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f * d⁄dX (logOf f) = d⁄dX f := by
  have hsub : HasSubst (f - 1) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_sub, hf, map_one, sub_self])
  have h := congrArg (subst (f - 1)) (one_add_X_mul_derivative_log (A := A))
  have hone : subst (f - 1) (1 : A⟦X⟧) = 1 := by rw [← coe_substAlgHom hsub, map_one]
  rw [subst_mul hsub, subst_add hsub, subst_X hsub, hone, add_sub_cancel] at h
  rw [logOf_eq, derivative_subst hsub, map_sub, Derivation.map_one_eq_zero, sub_zero,
    ← mul_assoc, h, one_mul]

end PowerSeries
