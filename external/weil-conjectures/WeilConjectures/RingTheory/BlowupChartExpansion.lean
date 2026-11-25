/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Homogeneous expansions of elements of powers of a two-generated ideal

If `I = (u, v)`, every element `r ∈ I ^ n` is a homogeneous form of degree `n` in `u` and `v`:
`r = ∑_{j ≤ n} p_j u ^ (n - j) v ^ j`. We record the coefficients as a polynomial `p` of degree at
most `n`, the *dehomogenization* of the form, which is the equation of the strict transform of
`V(r)` on the chart `v = u T` of the blow-up of `(u, v)`.

## Main results

- `Ideal.exists_eq_sum_of_mem_span_pair_pow`: the homogeneous expansion.
- `IsLocalRing.isUnit_coeff_of_not_mem_span_sup_pow`: if `r ∉ (u) + 𝔪 ^ (n + 1)`, the coefficient
  of `v ^ n` is a unit.
- `IsLocalRing.map_residue_ne_zero_of_not_mem_pow`: if `r ∉ 𝔪 ^ (n + 1)`, the residue of the
  dehomogenization is a nonzero polynomial.
-/

@[expose] public section

universe u

open Polynomial

variable {R : Type u} [CommRing R]

namespace Ideal

/-- An element of `(u, v) ^ n` is a homogeneous form of degree `n` in `u` and `v`, with
coefficients given by a polynomial of degree at most `n`. -/
theorem exists_eq_sum_of_mem_span_pair_pow {u v r : R} {n : ℕ}
    (hr : r ∈ Ideal.span {u, v} ^ n) :
    ∃ p : R[X], p.natDegree ≤ n ∧
      r = ∑ j ∈ Finset.range (n + 1), p.coeff j * u ^ (n - j) * v ^ j := by
  induction n generalizing r with
  | zero => exact ⟨C r, by simp⟩
  | succ n ih =>
    rw [pow_succ', Ideal.span_insert, sup_mul, Submodule.mem_sup] at hr
    obtain ⟨_, h₁, _, h₂, rfl⟩ := hr
    obtain ⟨s₁, hs₁, rfl⟩ := Ideal.mem_span_singleton_mul.mp h₁
    obtain ⟨s₂, hs₂, rfl⟩ := Ideal.mem_span_singleton_mul.mp h₂
    rw [← Ideal.span_insert] at hs₁ hs₂
    obtain ⟨p₁, hp₁, rfl⟩ := ih hs₁
    obtain ⟨p₂, hp₂, rfl⟩ := ih hs₂
    refine ⟨p₁ + X * p₂, ?_, ?_⟩
    · refine (natDegree_add_le _ _).trans (max_le (hp₁.trans n.le_succ) ?_)
      exact (natDegree_mul_le (p := X)).trans (by
        have := natDegree_X_le (R := R); omega)
    · simp only [coeff_add, add_mul, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_range_succ (n := n + 1), coeff_eq_zero_of_natDegree_lt (by omega),
          zero_mul, zero_mul, add_zero, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [show n + 1 - j = n - j + 1 by omega, pow_succ]
        ring
      · rw [Finset.sum_range_succ' (n := n + 1), coeff_X_mul_zero, zero_mul, zero_mul, add_zero,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [coeff_X_mul, Nat.add_sub_add_right, pow_succ]
        ring

end Ideal

/-- If `φ(y) = φ(x) T`, then `φ` maps the homogeneous form `∑_{j ≤ n} p_j x ^ (n - j) y ^ j` to
`φ(x) ^ n p(T)`. -/
theorem RingHom.map_sum_eq_pow_mul_eval₂ {S : Type*} [CommRing S] (φ : R →+* S) {x y : R} {T : S}
    (hT : φ y = φ x * T) (p : R[X]) {n : ℕ} (hp : p.natDegree ≤ n) :
    φ (∑ j ∈ Finset.range (n + 1), p.coeff j * x ^ (n - j) * y ^ j) = φ x ^ n * p.eval₂ φ T := by
  rw [eval₂_eq_sum_range' φ (Nat.lt_succ_of_le hp)]
  simp only [map_sum, map_mul, map_pow, Finset.mul_sum, hT]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [mul_pow, show n = n - j + j by omega, pow_add, Nat.add_sub_cancel]
  ring

namespace IsLocalRing

variable [IsLocalRing R]

/-- If `r = ∑_{j ≤ n} p_j u ^ (n - j) v ^ j` with `v ∈ 𝔪` and `r ∉ (u) + 𝔪 ^ (n + 1)`, then the
coefficient `p_n` of `v ^ n` is a unit: the line `u = 0` is not tangent to `V(r)`. -/
theorem isUnit_coeff_of_not_mem_span_sup_pow {u v r : R} {n : ℕ} {p : R[X]}
    (hv : v ∈ maximalIdeal R)
    (hr : r = ∑ j ∈ Finset.range (n + 1), p.coeff j * u ^ (n - j) * v ^ j)
    (hr' : r ∉ Ideal.span {u} ⊔ maximalIdeal R ^ (n + 1)) : IsUnit (p.coeff n) := by
  by_contra hn
  apply hr'
  rw [hr, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Submodule.sum_mem _ fun j hj => ?_))
    (Ideal.mem_sup_right ?_)
  · rw [Finset.mem_range] at hj
    rw [show n - j = n - j - 1 + 1 by omega, pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
      (Ideal.mem_span_singleton_self u)))
  · rw [pow_succ']
    exact Ideal.mul_mem_mul ((mem_maximalIdeal _).mpr hn) (Ideal.pow_mem_pow hv n)

/-- If `r = ∑_{j ≤ n} p_j u ^ (n - j) v ^ j` with `u, v ∈ 𝔪` and `r ∉ 𝔪 ^ (n + 1)`, then the
reduction of `p` modulo `𝔪` is a nonzero polynomial over the residue field. -/
theorem map_residue_ne_zero_of_not_mem_pow {u v r : R} {n : ℕ} {p : R[X]}
    (hu : u ∈ maximalIdeal R) (hv : v ∈ maximalIdeal R)
    (hr : r = ∑ j ∈ Finset.range (n + 1), p.coeff j * u ^ (n - j) * v ^ j)
    (hr' : r ∉ maximalIdeal R ^ (n + 1)) : p.map (residue R) ≠ 0 := by
  intro h
  apply hr'
  rw [hr]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hj' : p.coeff j ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, ← coeff_map, h, coeff_zero]
  rw [mul_assoc, pow_succ', show n = n - j + j by omega, pow_add, Nat.add_sub_cancel]
  exact Ideal.mul_mem_mul hj' (Ideal.mul_mem_mul (Ideal.pow_mem_pow hu _) (Ideal.pow_mem_pow hv _))

omit [IsLocalRing R] in
/-- If `r = ∑_{j ≤ n} p_j u ^ (n - j) v ^ j` with `p_n` a unit, then `v ^ n ∈ (u, r)`. -/
theorem pow_mem_span_pair_of_isUnit_coeff {u v r : R} {n : ℕ} {p : R[X]}
    (hr : r = ∑ j ∈ Finset.range (n + 1), p.coeff j * u ^ (n - j) * v ^ j)
    (hu : IsUnit (p.coeff n)) : v ^ n ∈ Ideal.span {u, r} := by
  have hs : ∑ j ∈ Finset.range n, p.coeff j * u ^ (n - j) * v ^ j ∈ Ideal.span {u, r} := by
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show n - j = n - j - 1 + 1 by omega, pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
      (Ideal.subset_span (by simp))))
  have h1 : p.coeff n * v ^ n ∈ Ideal.span {u, r} := by
    have key : r - ∑ j ∈ Finset.range n, p.coeff j * u ^ (n - j) * v ^ j = p.coeff n * v ^ n := by
      rw [hr, Finset.sum_range_succ, add_sub_cancel_left, Nat.sub_self, pow_zero, mul_one]
    rw [← key]
    exact Ideal.sub_mem _ (Ideal.subset_span (by simp)) hs
  have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : R) h1
  rwa [← mul_assoc, hu.val_inv_mul, one_mul] at this

end IsLocalRing
