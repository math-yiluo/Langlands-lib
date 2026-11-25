/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.GaloisResidueRoot
public import WeilConjectures.RingTheory.Valuation.KummerNormalForm
import Mathlib.Tactic.FieldSimp

/-!
# Hensel's lemma for Kummer equations of exponent `p` in a subfield

Let `Ω` be an algebraically closed field, `𝒪` a valuation subring of `Ω` and `N` a subfield of
`Ω` over which `Ω` is algebraic, such that every automorphism of `Ω/N` maps `𝒪` into itself.
Let `p` be a prime with `0 < v(p) < 1` and `ϖ ∈ N` with `ϖ ^ (p - 1) = -p`.

* `ValuationSubring.exists_pow_eq_one_add`: if `x ∈ N` is negligible, i.e.
  `v(x) ^ (p - 1) ≤ v(p) ^ p`, and the Artin–Schreier equation `n ^ p - n = x / ϖ ^ p` has a
  residual solution in `N ∩ 𝒪`, then `1 + x` is a `p`-th power in `N`.

The substitution `y = 1 + ϖ Z` transforms `y ^ p = 1 + x` into the equation
`(Z + ϖ⁻¹) ^ p = (1 + x) / ϖ ^ p`, which is congruent to `Z ^ p - Z = x / ϖ ^ p` modulo the
maximal ideal of `𝒪`.
-/

@[expose] public section

open Polynomial

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

/-- If `ϖ ^ (p - 1) = -p` with `v(p) < 1`, then the polynomial `(X + ϖ⁻¹) ^ p - (1 + x) / ϖ ^ p`
is congruent to `X ^ p - X - x / ϖ ^ p` coefficientwise modulo the maximal ideal of `𝒪`. -/
theorem valuation_coeff_kummer_sub_lt_one (p : ℕ) [hp : Fact p.Prime]
    (hp1 : 𝒪.valuation (p : Ω) < 1) {ϖ : Ω} (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ^ (p - 1) = -(p : Ω))
    (x : Ω) (i : ℕ) :
    𝒪.valuation (((X + C ϖ⁻¹) ^ p - C ((1 + x) / ϖ ^ p) -
      (X ^ p - X - C (x / ϖ ^ p))).coeff i) < 1 := by
  have hp2 := hp.out.two_le
  have hvϖ : 𝒪.valuation ϖ ^ (p - 1) = 𝒪.valuation (p : Ω) := by
    rw [← map_pow, hϖ, Valuation.map_neg]
  have hvϖ0 : 𝒪.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  have hvϖ1 : 𝒪.valuation ϖ < 1 := by
    by_contra h
    rw [not_lt] at h
    exact hp1.not_ge (hvϖ ▸ one_le_pow₀ h)
  simp only [coeff_sub, coeff_X_add_C_pow, coeff_C, coeff_X_pow, coeff_X]
  rcases Nat.lt_or_ge p i with hpi | hip
  · simp [Nat.choose_eq_zero_of_lt hpi, show i ≠ 0 by omega, show i ≠ p by omega,
      show 1 ≠ i by omega]
  rcases eq_or_ne i 0 with rfl | hi0
  · have : ϖ⁻¹ ^ p * ((p.choose 0 : ℕ) : Ω) - (1 + x) / ϖ ^ p -
        ((if 0 = p then 1 else 0) - (if 1 = 0 then 1 else 0) - x / ϖ ^ p) = 0 := by
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.choose_zero_right, inv_pow]
      field_simp
      ring
    simp only [Nat.sub_zero, ite_true]
    rw [this, map_zero]
    exact zero_lt_one
  rcases eq_or_ne i p with h | hip'
  · simp [h, show p ≠ 0 by omega, show 1 ≠ p by omega]
  rcases eq_or_ne i 1 with rfl | hi1
  · have hp0 : (p : Ω) ≠ 0 := by
      intro h
      rw [h, neg_zero] at hϖ
      exact hϖ0 (pow_eq_zero_iff (by omega) |>.1 hϖ)
    simp only [one_ne_zero, hip', ite_false, ite_true, sub_zero, zero_sub, sub_neg_eq_add]
    rw [inv_pow, hϖ, Nat.choose_one_right, inv_neg, neg_mul, inv_mul_cancel₀ hp0, neg_add_cancel,
      map_zero]
    exact zero_lt_one
  · simp only [hi0, hip', Ne.symm hi1, ite_false, sub_zero]
    obtain ⟨m, hm⟩ := hp.out.dvd_choose_self hi0 (lt_of_le_of_ne hip hip')
    rw [hm, Nat.cast_mul, map_mul, map_mul, map_pow, map_inv₀, ← hvϖ]
    have hvm : 𝒪.valuation (m : Ω) ≤ 1 := (valuation_le_one_iff _ _).2 (natCast_mem 𝒪 m)
    have hexp : p - 1 = (p - i) + (i - 1) := by omega
    rw [hexp, pow_add, inv_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hvϖ0),
      one_mul]
    exact mul_lt_one_of_lt_of_le (pow_lt_one₀ zero_le hvϖ1 (by omega)) hvm

/-- If `ϖ ^ (p - 1) = -p` and `x` is negligible, then `x / ϖ ^ p` lies in `𝒪`. -/
theorem valuation_div_pow_le_one_of_isKummerNegligible (p : ℕ) [hp : Fact p.Prime] {ϖ : Ω}
    (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ^ (p - 1) = -(p : Ω)) {x : Ω}
    (hx : 𝒪.valuation.IsKummerNegligible p x) : 𝒪.valuation (x / ϖ ^ p) ≤ 1 := by
  have hvϖ : 𝒪.valuation ϖ ^ (p - 1) = 𝒪.valuation (p : Ω) := by
    rw [← map_pow, hϖ, Valuation.map_neg]
  rw [map_div₀, map_pow, div_le_one₀ (pow_pos (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hϖ0)) _)]
  rw [Valuation.IsKummerNegligible, ← hvϖ, ← pow_mul, mul_comm, pow_mul] at hx
  exact (pow_le_pow_iff_left₀ zero_le zero_le (by have := hp.out.two_le; omega)).1 hx

/-- **Hensel's lemma for Kummer equations of exponent `p`.** Let `Ω` be algebraically closed and
algebraic over a subfield `N`, such that every automorphism of `Ω/N` maps `𝒪` into itself. Let
`p` be a prime with `0 < v(p) < 1`, `ϖ ∈ N` with `ϖ ^ (p - 1) = -p` and `x ∈ N` negligible.
If `n ^ p - n ≡ x / ϖ ^ p` modulo the maximal ideal for some `n ∈ N ∩ 𝒪`, then `1 + x` is a
`p`-th power in `N`. -/
theorem exists_pow_eq_one_add [IsAlgClosed Ω] (N : Subfield Ω) [Algebra.IsAlgebraic N Ω]
    (h𝒪 : ∀ σ : Ω ≃ₐ[N] Ω, ∀ x ∈ 𝒪, σ x ∈ 𝒪) (p : ℕ) [hp : Fact p.Prime]
    (hp1 : 𝒪.valuation (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    {ϖ : Ω} (hϖN : ϖ ∈ N) (hϖ : ϖ ^ (p - 1) = -(p : Ω))
    {x : Ω} (hxN : x ∈ N) (hx : 𝒪.valuation.IsKummerNegligible p x)
    {n : Ω} (hnN : n ∈ N) (hn𝒪 : n ∈ 𝒪) (hn : 𝒪.valuation (n ^ p - n - x / ϖ ^ p) < 1) :
    ∃ y ∈ N, y ^ p = 1 + x := by
  have hp2 := hp.out.two_le
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), eq_comm, neg_eq_zero] at hϖ
    exact hp0 hϖ
  have hvϖ : 𝒪.valuation ϖ ^ (p - 1) = 𝒪.valuation (p : Ω) := by
    rw [← map_pow, hϖ, Valuation.map_neg]
  have hvϖ0 : 𝒪.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  have hvϖ1 : 𝒪.valuation ϖ < 1 := by
    by_contra h
    rw [not_lt] at h
    exact hp1.not_ge (hvϖ ▸ one_le_pow₀ h)
  -- the constant term `x / ϖ ^ p` is integral
  have hc : x / ϖ ^ p ∈ 𝒪 := (valuation_le_one_iff _ _).1
    (valuation_div_pow_le_one_of_isKummerNegligible 𝒪 p hϖ0 hϖ hx)
  set g : Ω[X] := (X + C ϖ⁻¹) ^ p - C ((1 + x) / ϖ ^ p) with hg
  have hD := valuation_coeff_kummer_sub_lt_one 𝒪 p hp1 hϖ0 hϖ x
  have hg𝒪 (i : ℕ) : g.coeff i ∈ 𝒪 := by
    rw [← sub_add_cancel g (X ^ p - X - C (x / ϖ ^ p)), coeff_add]
    exact AddMemClass.add_mem ((valuation_le_one_iff _ _).1 (hD i).le)
      (coeff_X_pow_sub_X_sub_C_mem p hc i)
  have hgN (i : ℕ) : g.coeff i ∈ N := by
    simp only [hg, coeff_sub, coeff_X_add_C_pow, coeff_C]
    refine sub_mem (MulMemClass.mul_mem (pow_mem (inv_mem hϖN) _) (natCast_mem _ _)) ?_
    split_ifs
    · exact div_mem (AddMemClass.add_mem (OneMemClass.one_mem _) hxN) (pow_mem hϖN _)
    · exact ZeroMemClass.zero_mem _
  have hmonic : g.Monic := by
    refine ((monic_X_add_C _).pow p).sub_of_left (degree_C_le.trans_lt ?_)
    rw [degree_pow, degree_X_add_C, nsmul_one]
    exact_mod_cast hp.out.pos
  have hgn : 𝒪.valuation (g.eval n) < 1 := by
    have h1 : 𝒪.valuation ((g - (X ^ p - X - C (x / ϖ ^ p))).eval n) < 1 := by
      rw [eval_eq_sum_range]
      refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
      rw [map_mul, map_pow]
      exact mul_lt_one_of_lt_of_le (hD i) (pow_le_one' ((valuation_le_one_iff _ _).2 hn𝒪) _)
    rw [← sub_add_cancel g (X ^ p - X - C (x / ϖ ^ p)), eval_add]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt h1 ?_)
    simpa using hn
  obtain ⟨r, hr, hrn⟩ := exists_isRoot_valuation_sub_lt_one 𝒪 hmonic hgn
  have hr𝒪 : r ∈ 𝒪 := by
    rw [← sub_add_cancel r n]
    exact AddMemClass.add_mem ((valuation_le_one_iff _ _).1 hrn.le) hn𝒪
  have hr' : (r + ϖ⁻¹) ^ p = (1 + x) / ϖ ^ p := by
    simpa [hg, sub_eq_zero] using hr.eq_zero
  have hy : 1 + ϖ * r = ϖ * (r + ϖ⁻¹) := by
    rw [mul_add, mul_inv_cancel₀ hϖ0, add_comm]
  have hv1 : 𝒪.valuation (1 + ϖ * r) = 1 := by
    refine Valuation.map_one_add_of_lt _ ?_
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hvϖ1 ((valuation_le_one_iff _ _).2 hr𝒪)
  have hder : 𝒪.valuation (g.derivative.eval r) = 1 := by
    simp only [hg, derivative_sub, derivative_C, sub_zero, derivative_X_add_C_pow, eval_mul,
      eval_C, eval_pow, eval_add, eval_X, map_mul, map_pow, ← hvϖ, ← mul_pow]
    rw [← map_mul, ← hy, hv1, one_pow]
  refine ⟨1 + ϖ * r, AddMemClass.add_mem (OneMemClass.one_mem _) (MulMemClass.mul_mem hϖN
    (mem_of_isRoot_of_valuation_sub_lt_one 𝒪 N h𝒪 hgN hg𝒪 hr hder hnN hn𝒪 hrn)), ?_⟩
  rw [hy, mul_pow, hr', mul_div_cancel₀ _ (pow_ne_zero _ hϖ0)]

end ValuationSubring
