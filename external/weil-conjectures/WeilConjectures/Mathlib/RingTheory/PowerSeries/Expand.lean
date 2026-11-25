/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Complements on the expansion `T ↦ T ^ p` of power series

## Main results

- `PowerSeries.expand_inv`: over a field, expansion commutes with taking inverses.
- `PowerSeries.X_pow_dvd_expand_sub_C_constantCoeff`: the expansion `f (T ^ p)` is congruent to
  its constant coefficient modulo `T ^ p`.
- `PowerSeries.X_mul_derivative_expand`: the Euler operator `X d/dX` commutes with the expansion
  `X ↦ X ^ p` up to the factor `p`: `X (f (X ^ p))' = p (X f')(X ^ p)`.
- `PowerSeries.eq_sum_X_pow_mul_expand`, `PowerSeries.finite_expand`: every power series is
  `∑_{r < m} t^r g_r(t^m)`, so `t ↦ t^m` is a finite ring map.
-/

@[expose] public section

namespace PowerSeries

/-- Over a field, the expansion `T ↦ T ^ p` commutes with taking inverses. -/
theorem expand_inv {K : Type*} [Field K] (p : ℕ) (hp : p ≠ 0) (f : K⟦X⟧) :
    expand p hp f⁻¹ = (expand p hp f)⁻¹ := by
  by_cases hf : constantCoeff f = 0
  · rw [PowerSeries.inv_eq_zero.2 hf, map_zero,
      PowerSeries.inv_eq_zero.2 (by rwa [constantCoeff_expand])]
  · rw [eq_inv_iff_mul_eq_one (by rwa [constantCoeff_expand]), ← map_mul,
      PowerSeries.inv_mul_cancel _ hf, map_one]

/-- The expansion `f (T ^ p)` of a power series is congruent to its constant coefficient modulo
`T ^ p`. -/
theorem X_pow_dvd_expand_sub_C_constantCoeff {R : Type*} [CommRing R] (p : ℕ) (hp : p ≠ 0)
    (f : R⟦X⟧) : X ^ p ∣ expand p hp f - C (constantCoeff f) := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, coeff_expand, coeff_C]
  rcases eq_or_ne m 0 with rfl | h0
  · simp
  · rw [ite_eq_right fun h ↦ (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h).not_gt hm, ite_eq_right h0,
      sub_zero]

variable {R : Type*} [CommRing R]

/-- The `n`-th coefficient of `X f'` is `n` times that of `f`. -/
theorem coeff_X_mul_derivative (f : R⟦X⟧) (n : ℕ) :
    coeff n (X * derivative (R := R) f) = n * coeff n f := by
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    push_cast
    rfl

/-- The Euler operator `X d/dX` and the expansion `X ↦ X ^ p`:
`X (f (X ^ p))' = p (X f')(X ^ p)`. -/
theorem X_mul_derivative_expand (p : ℕ) (hp : p ≠ 0) (f : R⟦X⟧) :
    X * derivative (R := R) (expand p hp f) =
      C (p : R) * expand p hp (X * derivative (R := R) f) := by
  ext n
  rw [coeff_X_mul_derivative, coeff_C_mul, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), coeff_X_mul_derivative]
    push_cast
    ring
  · simp


section Expand

variable (m : ℕ) (hm : m ≠ 0)

/-- Every power series is `∑_{r < m} t^r g_r(t^m)`, with `g_r = ∑ₙ a_{mn+r} tⁿ`. -/
lemma eq_sum_X_pow_mul_expand (f : PowerSeries R) :
    f = ∑ r ∈ Finset.range m,
      X ^ r * expand m hm (mk fun n ↦ coeff (m * n + r) f) := by
  ext N
  rw [map_sum, Finset.sum_eq_single (N % m)]
  · rw [coeff_X_pow_mul', ite_eq_left (Nat.mod_le N m), coeff_expand]
    have hd : m ∣ N - N % m := Nat.dvd_sub_mod N
    rw [ite_eq_left hd, coeff_mk]
    congr 1
    rw [Nat.mul_div_cancel' hd, Nat.sub_add_cancel (Nat.mod_le N m)]
  · intro r hr hrN
    rw [coeff_X_pow_mul']
    split_ifs with hrle
    · rw [coeff_expand, ite_eq_right]
      intro hd
      apply hrN
      have h2 : N % m = r % m := ((Nat.modEq_iff_dvd' hrle).2 hd).symm
      rw [h2, Nat.mod_eq_of_lt (Finset.mem_range.1 hr)]
    · rfl
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.mod_lt N (Nat.pos_of_ne_zero hm))) h

/-- `expand m` is injective. -/
lemma expand_injective : Function.Injective (expand m hm (R := R)) := by
  intro f g h
  ext n
  have := congrArg (coeff (m * n)) h
  rwa [coeff_expand_mul, coeff_expand_mul] at this

/-- `t ↦ t^m` is a finite ring map: `R⟦t⟧` is spanned by `1, t, …, t^{m-1}` over its image. -/
lemma finite_expand : (expand m hm (R := R)).toRingHom.Finite := by
  classical
  let := (expand m hm (R := R)).toRingHom.toAlgebra
  let : Module (PowerSeries R) (PowerSeries R) := Algebra.toModule
  refine ⟨⟨(Finset.range m).image fun r ↦ (X : PowerSeries R) ^ r, ?_⟩⟩
  rw [eq_top_iff]
  intro f _
  rw [eq_sum_X_pow_mul_expand m hm f]
  refine Submodule.sum_mem _ fun r hr ↦ ?_
  rw [mul_comm]
  exact Submodule.smul_mem _ (mk fun n ↦ coeff (m * n + r) f)
    (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hr)))

end Expand

end PowerSeries
