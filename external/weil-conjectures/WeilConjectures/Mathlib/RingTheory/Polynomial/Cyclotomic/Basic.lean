/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Partial products of `Xⁿ - 1` evaluated at a root of unity

Let `k` be a field containing a primitive `n`-th root of unity, so that
`Xⁿ - 1 = ∏_{r ∈ μₙ(k)} (X - r)`, and let `x` be an element of a `k`-algebra `R` (given by a ring
homomorphism `ρ : k →+* R`) with `xⁿ = 1`. For each `r ∈ μₙ(k)` put
`y_r = ∏_{s ∈ μₙ(k), s ≠ r} (x - s)`. Then `y_r (x - r) = 0`, and Lagrange interpolation shows
that the `y_r` generate the unit ideal. Geometrically: `x` equals the constant `r` on the open
set where `y_r` is invertible, and these open sets cover `Spec R`.

## Main statements

- `Polynomial.prod_erase_mul_sub_eq_zero`: `y_r (x - r) = 0`.
- `Polynomial.sum_mul_prod_erase_sub_eq_one`: `∑_r c_r y_r = 1` for explicit constants `c_r`.
-/

@[expose] public section

namespace Polynomial

variable {k R : Type*} [Field k] [DecidableEq k] [CommRing R] (ρ : k →+* R) {n : ℕ}

/-- If `k` contains a primitive `n`-th root of unity and `xⁿ = 1`, then for every `n`-th root of
unity `r ∈ k`, `(∏_{s ≠ r} (x - s)) · (x - r) = xⁿ - 1 = 0`, the product running over the
`n`-th roots of unity `s ∈ k`. -/
lemma prod_erase_mul_sub_eq_zero {ζ : k} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) {x : R}
    (hx : x ^ n = 1) (r : k) (hr : r ∈ nthRootsFinset n (1 : k)) :
    (∏ s ∈ (nthRootsFinset n (1 : k)).erase r, (x - ρ s)) * (x - ρ r) = 0 := by
  rw [Finset.prod_erase_mul _ _ hr]
  have := congrArg (eval₂ ρ x) (X_pow_sub_one_eq_prod hn hζ)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_one, hx, sub_self, eval₂_finsetProd, eval₂_X,
    eval₂_C] at this
  exact this.symm

/-- **Lagrange interpolation at the `n`-th roots of unity.** For every `x` in a `k`-algebra,
`∑_r (∏_{s ≠ r} (r - s)⁻¹) · ∏_{s ≠ r} (x - s) = 1`, the sum and products running over the
`n`-th roots of unity in `k`: the Lagrange basis polynomials of a nonempty set of nodes sum
to `1`. -/
lemma sum_mul_prod_erase_sub_eq_one (hn : 0 < n) (x : R) :
    ∑ r ∈ nthRootsFinset n (1 : k), ρ (∏ s ∈ (nthRootsFinset n (1 : k)).erase r, (r - s)⁻¹) *
      ∏ s ∈ (nthRootsFinset n (1 : k)).erase r, (x - ρ s) = 1 := by
  have hne : (nthRootsFinset n (1 : k)).Nonempty :=
    ⟨1, (mem_nthRootsFinset hn _).2 (one_pow _)⟩
  have := congrArg (eval₂ ρ x) (Lagrange.sum_basis (v := id) (Set.injOn_id _) hne)
  simp only [Lagrange.basis, Lagrange.basisDivisor, eval₂_finsetSum, eval₂_finsetProd,
    eval₂_mul, eval₂_C, eval₂_sub, eval₂_X, eval₂_one, id] at this
  rw [← this]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_prod, ← Finset.prod_mul_distrib]

end Polynomial
