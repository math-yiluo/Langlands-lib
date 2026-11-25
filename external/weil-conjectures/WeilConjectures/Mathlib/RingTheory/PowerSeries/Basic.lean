/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coefficients of a product of power series

## Main statements

- `PowerSeries.coeff_mul_eq_sum_range`: the coefficient of `X ^ n` in `φ * ψ` is
  `∑_{i = 0}^{n} cᵢ(φ) c_{n - i}(ψ)`.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommSemiring R]

/-- **Formal power series** (blueprint `def-weil-formal-power-series`): an element of `R⟦X⟧` is
the sequence `(cₙ)_{n ≥ 0}` of its coefficients (`PowerSeries.coeff`), addition is
coefficientwise, and the coefficient of `X ^ n` in a product is `∑_{i = 0}^{n} cᵢ dₙ₋ᵢ`. -/
theorem coeff_mul_eq_sum_range (n : ℕ) (φ ψ : R⟦X⟧) :
    coeff n (φ * ψ) = ∑ i ∈ Finset.range (n + 1), coeff i φ * coeff (n - i) ψ := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

end PowerSeries
