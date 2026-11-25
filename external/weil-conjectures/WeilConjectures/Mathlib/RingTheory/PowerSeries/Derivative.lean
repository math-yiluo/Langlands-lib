/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.LinearCombination

/-!
# Complements on the formal derivative of a power series

## Main results

- `PowerSeries.map_derivative` — the formal derivative commutes with the coefficientwise map
  along a ring homomorphism.
- `PowerSeries.X_mul_derivative_prod` — the logarithmic derivative of a finite product.
- `PowerSeries.neg_X_mul_derivative_prod_one_sub_C_mul_X` — the logarithmic derivative of
  `∏ (1 - c X)` is the generating series of the power sums `∑ cⁿ`.
- `PowerSeries.coeff_inv_prod_one_sub_C_mul_X_nonneg` — if all power sums of a multiset of
  complex numbers are nonnegative reals, so are all coefficients of `∏ (1 - c X)⁻¹`.
- `PowerSeries.X_mul_derivative_inv` — the logarithmic derivative of an inverse is the negative
  of the logarithmic derivative.
-/

@[expose] public section

namespace PowerSeries

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The formal derivative commutes with the coefficientwise map along a ring homomorphism. -/
theorem map_derivative (φ : R →+* S) (f : R⟦X⟧) :
    map φ (derivative (R := R) f) = derivative (R := S) (map φ f) := by
  ext n
  simp [coeff_derivative]

/-- The logarithmic derivative of a finite product is the sum of the logarithmic derivatives of
the factors: if `X fᵢ' = aᵢ fᵢ` for all `i ∈ s`, then `X (∏ fᵢ)' = (∑ aᵢ) ∏ fᵢ`. -/
theorem X_mul_derivative_prod {R : Type*} [CommRing R] {ι : Type*} {f a : ι → R⟦X⟧}
    (s : Finset ι) (h : ∀ i ∈ s, X * derivative (R := R) (f i) = a i * f i) :
    X * derivative (R := R) (∏ i ∈ s, f i) = (∑ i ∈ s, a i) * ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    have hb' := h b (Finset.mem_insert_self b s)
    have ihs := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert hb, Finset.sum_insert hb, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
    linear_combination f b * ihs + (∏ i ∈ s, f i) * hb'

/-- The logarithmic derivative of `P = ∏ (1 - c X)` is the generating series of the power sums:
`-X P' = P ∑_{n ≥ 1} pₙ Xⁿ` with `pₙ = ∑ cⁿ`. -/
theorem neg_X_mul_derivative_prod_one_sub_C_mul_X {R : Type*} [CommRing R] (s : Multiset R) :
    -(X * d⁄dX (s.map fun c ↦ 1 - C c * X).prod) =
      (s.map fun c ↦ 1 - C c * X).prod *
        mk fun n ↦ if n = 0 then 0 else (s.map (· ^ n)).sum := by
  induction s using Multiset.induction_on with
  | empty =>
    ext n
    simp
  | cons c s ih =>
    have hc : (1 - C c * X) * mk (fun n ↦ if n = 0 then (0 : R) else c ^ n) = C c * X := by
      ext n
      rcases n with _ | _ | n <;> simp [sub_mul, mul_assoc, coeff_succ_X_mul, pow_succ]
      ring
    have hS : (mk fun n ↦ if n = 0 then (0 : R) else ((c ::ₘ s).map (· ^ n)).sum) =
        mk (fun n ↦ if n = 0 then (0 : R) else c ^ n) +
          mk fun n ↦ if n = 0 then 0 else (s.map (· ^ n)).sum := by
      ext n
      simp only [coeff_mk, map_add]
      split_ifs <;> simp
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, hS]
    simp only [smul_eq_mul, map_sub, derivative_one, derivative_C, Derivation.leibniz,
      derivative_X]
    linear_combination (1 - C c * X) * ih - (s.map fun c ↦ 1 - C c * X).prod * hc

open scoped ComplexOrder in
/-- If every power sum `pₙ = ∑ cⁿ`, `n ≥ 1`, of a multiset of complex numbers is a nonnegative
real number, then every coefficient of `∏ (1 - c X)⁻¹` is a nonnegative real number.

This is the formal identity `∏ (1 - c X)⁻¹ = exp (∑_{n ≥ 1} pₙ Xⁿ / n)` in differentiated
form: the logarithmic derivative gives the recursion `n bₙ = ∑_{i + j = n, j ≥ 1} bᵢ pⱼ` for the
coefficients `bₙ` of the inverse, which preserves nonnegativity. -/
theorem coeff_inv_prod_one_sub_C_mul_X_nonneg (s : Multiset ℂ)
    (hs : ∀ n, 0 < n → 0 ≤ (s.map (· ^ n)).sum) (k : ℕ) :
    0 ≤ coeff k ((s.map fun c ↦ 1 - C c * X).prod)⁻¹ := by
  set P := (s.map fun c ↦ 1 - C c * X).prod
  set S : ℂ⟦X⟧ := mk fun n ↦ if n = 0 then 0 else (s.map (· ^ n)).sum
  have hP : constantCoeff P = 1 := by
    simp only [P, map_multiset_prod, Multiset.map_map]
    exact Multiset.prod_eq_one fun x hx ↦ by
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hx
      simp
  set G := P⁻¹
  have hPG : P * G = 1 := PowerSeries.mul_inv_cancel _ (by simp [hP])
  have hG : X * d⁄dX G = G * S := by
    rw [derivative_inv']
    calc X * (-G ^ 2 * d⁄dX P) = G ^ 2 * -(X * d⁄dX P) := by ring
      _ = G ^ 2 * (P * S) := by rw [neg_X_mul_derivative_prod_one_sub_C_mul_X]
      _ = G * S * (P * G) := by ring
      _ = G * S := by rw [hPG, mul_one]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | k
  · simp [G, constantCoeff_inv, hP]
  · have h := congrArg (coeff (k + 1)) hG
    rw [coeff_succ_X_mul, coeff_derivative, coeff_mul] at h
    have hsum : 0 ≤ ∑ p ∈ Finset.antidiagonal (k + 1), coeff p.1 G * coeff p.2 S := by
      refine Finset.sum_nonneg fun p hp ↦ ?_
      rcases eq_or_ne p.2 0 with h0 | h0
      · simp [S, h0]
      · have hi : p.1 < k + 1 := by
          have := Finset.mem_antidiagonal.1 hp
          omega
        simp only [S, coeff_mk, ite_eq_right h0]
        exact mul_nonneg (ih p.1 hi) (hs p.2 (Nat.pos_of_ne_zero h0))
    have hk : coeff (k + 1) G = (((k + 1 : ℕ) : ℝ)⁻¹ : ℝ) *
        ∑ p ∈ Finset.antidiagonal (k + 1), coeff p.1 G * coeff p.2 S := by
      rw [← h]
      push_cast
      field_simp
    rw [hk]
    exact mul_nonneg (Complex.zero_le_real.2 (by positivity)) hsum

/-- The logarithmic derivative of the inverse of an invertible power series over a field is the
negative of its logarithmic derivative: if `X f' = a f`, then `X (f⁻¹)' = -a f⁻¹`. -/
theorem X_mul_derivative_inv {K : Type*} [Field K] {f a : K⟦X⟧}
    (h : X * d⁄dX f = a * f) (hf : constantCoeff f ≠ 0) :
    X * d⁄dX f⁻¹ = -a * f⁻¹ := by
  have hmul : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hf
  rw [derivative_inv']
  linear_combination (-(f⁻¹ ^ 2)) * h + (-a * f⁻¹) * hmul

end PowerSeries
