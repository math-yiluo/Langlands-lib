/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.DetTrace

/-!
# Automorphisms whose powers have trace zero

Over a field of characteristic zero, an automorphism `F` of a finite dimensional vector space
`V` with `tr (F ^ n) = 0` for all `n ≥ 1` forces `V = 0`: by the determinant-trace identity
`t (det (1 - t F))' = - (∑_{n ≥ 1} tr (F ^ n) t ^ n) det (1 - t F)` the reciprocal
characteristic polynomial `det (1 - t F)` has zero derivative, hence is constant, while its
degree is `dim V` since `F` is invertible.

## Main statements

- `LinearMap.finrank_eq_zero_of_trace_pow_eq_zero`
-/

@[expose] public section

open PowerSeries

namespace LinearMap

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Over a field of characteristic zero, an endomorphism `F` with invertible determinant whose
powers `F ^ n`, `n ≥ 1`, all have trace zero lives on the zero space: `det (1 - t F)` has zero
logarithmic derivative, hence is constant, but has degree `dim V`. -/
theorem finrank_eq_zero_of_trace_pow_eq_zero (F : Module.End K V) (hF : IsUnit (LinearMap.det F))
    (h : ∀ n : ℕ, n ≠ 0 → LinearMap.trace K V (F ^ n) = 0) :
    Module.finrank K V = 0 := by
  have h1 := X_mul_derivative_charpolyRev F
  have hT : (PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (F ^ n)) = 0 := by
    ext n
    rw [PowerSeries.coeff_mk, map_zero]
    split_ifs with hn
    · rfl
    · exact h n hn
  rw [hT, neg_zero, zero_mul, mul_eq_zero] at h1
  have h2 : Polynomial.derivative F.charpolyRev = 0 := by
    refine Polynomial.coe_injective (R := K) ?_
    rw [← PowerSeries.derivative_coe (R := K), Polynomial.coe_zero]
    exact h1.resolve_left PowerSeries.X_ne_zero
  rw [← natDegree_charpolyRev hF]
  exact Polynomial.derivative_eq_zero.mp h2

end LinearMap
