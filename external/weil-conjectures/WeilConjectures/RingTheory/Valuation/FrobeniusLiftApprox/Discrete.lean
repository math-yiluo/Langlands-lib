/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ValuationIndependence
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.Finite

/-!
# Discreteness of finite extensions of discretely valued subfields

Let `v` be a valuation on a field `F` and `K₀ ⊆ F` a subfield whose nonzero values are the integral
powers of `v ϖ`, `0 < v ϖ < 1`. We show that a finite extension of `K₀` inside `F` is again
discretely valued (`Valuation.exists_uniformizer_of_finiteDimensional`): if `n` is its degree,
then the `n!`-th powers of its values are powers of `v ϖ`, and the exponents form a subgroup of `ℤ`.

We also record the elementary precision lemma `Valuation.exists_pow_lt_of_pow_eq_zpow`.
-/

@[expose] public section

open Polynomial

namespace Valuation

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀}

/-- If some power `δ ^ n`, `n > 0`, is an integral power of `0 < γ < 1`, then `δ` exceeds some
natural power of `γ`. -/
lemma exists_pow_lt_of_pow_eq_zpow {γ δ : Γ₀} (hγ0 : γ ≠ 0) (hγ1 : γ < 1) {n : ℕ} (hn : 0 < n)
    {m : ℤ} (h : δ ^ n = γ ^ m) : ∃ N : ℕ, γ ^ N < δ := by
  refine ⟨m.toNat + 1, lt_of_pow_lt_pow_left₀ n zero_le ?_⟩
  rw [h, ← pow_mul, ← zpow_natCast]
  refine zpow_lt_zpow_right_of_lt_one₀ (zero_lt_iff.2 hγ0) hγ1 ?_
  push_cast
  nlinarith [Int.self_le_toNat m]

/-- An integral power `γ ^ m < 1` of `0 < γ < 1` is at most `γ`. -/
lemma zpow_le_self_of_zpow_lt_one {γ : Γ₀} (hγ0 : γ ≠ 0) (hγ1 : γ < 1) {m : ℤ} (h : γ ^ m < 1) :
    γ ^ m ≤ γ := by
  have h0 : 0 < γ := zero_lt_iff.2 hγ0
  have hm : 0 < m := by
    by_contra hm
    exact (one_le_zpow_of_nonpos₀ h0 hγ1.le (not_lt.1 hm)).not_gt h
  simpa using zpow_le_zpow_right_of_le_one₀ h0 hγ1.le (Int.add_one_le_iff.2 hm)

/-- If the nonzero values of a subfield `K₀` are integral powers of `γ ≠ 0`, and `z ≠ 0` is a
root of a nonzero polynomial `P` over `K₀`, then `v z ^ r` is an integral power of `γ` for some
`0 < r ≤ deg P`: two nonzero terms of `P (z)` have the same value. -/
lemma exists_pow_eq_zpow_of_aeval_eq_zero {K₀ : Subfield F} {γ : Γ₀} (hγ : γ ≠ 0)
    (hK₀ : ∀ a ∈ K₀, a ≠ 0 → ∃ m : ℤ, v a = γ ^ m) {P : K₀[X]} (hP : P ≠ 0) {z : F}
    (hz : z ≠ 0) (hPz : aeval z P = 0) :
    ∃ r : ℕ, 0 < r ∧ r ≤ P.natDegree ∧ ∃ m : ℤ, v z ^ r = γ ^ m := by
  classical
  set x : Fin (P.natDegree + 1) → F := fun j ↦ (P.coeff j : F) * z ^ (j : ℕ) with hx
  have hsum : ∑ j, x j = 0 := by
    rw [← hPz, aeval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    rfl
  have hlead : x (Fin.last _) ≠ 0 :=
    mul_ne_zero (by simpa using hP) (pow_ne_zero _ hz)
  have key (i i' : Fin (P.natDegree + 1)) (hlt : i < i') (hi : x i ≠ 0)
      (hv : v (x i) = v (x i')) : ∃ r : ℕ, 0 < r ∧ r ≤ P.natDegree ∧ ∃ m : ℤ, v z ^ r = γ ^ m := by
    have hci : (P.coeff i : F) ≠ 0 := left_ne_zero_of_mul hi
    have hci' : (P.coeff i' : F) ≠ 0 := by
      intro h0
      simp only [hx, h0, zero_mul, map_zero] at hv
      exact hi (v.zero_iff.1 hv)
    obtain ⟨mi, hmi⟩ := hK₀ _ (P.coeff i).2 hci
    obtain ⟨mi', hmi'⟩ := hK₀ _ (P.coeff i').2 hci'
    have hvz : v z ^ (i : ℕ) ≠ 0 := pow_ne_zero _ ((v.ne_zero_iff).2 hz)
    refine ⟨i' - i, Nat.sub_pos_of_lt hlt, (Nat.sub_le _ _).trans (Nat.lt_succ_iff.1 i'.2),
      mi - mi', ?_⟩
    rw [zpow_sub₀ hγ, eq_div_iff (zpow_ne_zero _ hγ)]
    refine mul_right_cancel₀ hvz ?_
    rw [hx, map_mul, map_mul, map_pow, map_pow, hmi, hmi',
      ← Nat.add_sub_of_le hlt.le, pow_add] at hv
    rw [hv]
    ac_rfl
  by_contra hne
  refine hlead (Valuation.eq_zero_of_sum_eq_zero (v := v) (fun i i' hii' hi hi' hv ↦ hne ?_)
    hsum _)
  rcases lt_or_gt_of_ne hii' with h | h
  · exact key i i' h hi hv
  · exact key i' i h hi' hv.symm

/-- In a finite extension `Kst` of degree `n` of a subfield `K₀` whose nonzero values are powers
of `v ϖ`, the `n!`-th powers of the nonzero values are powers of `v ϖ`. -/
lemma exists_pow_factorial_eq_zpow {K₀ : Subfield F} (Kst : IntermediateField K₀ F)
    [FiniteDimensional K₀ Kst] {γ : Γ₀} (hγ : γ ≠ 0)
    (hK₀ : ∀ a ∈ K₀, a ≠ 0 → ∃ m : ℤ, v a = γ ^ m) {z : F} (hzK : z ∈ Kst) (hz : z ≠ 0) :
    ∃ m : ℤ, v z ^ (Module.finrank K₀ Kst).factorial = γ ^ m := by
  have hint : IsIntegral K₀ z :=
    IntermediateField.isIntegral_iff.1 (IsIntegral.of_finite K₀ (⟨z, hzK⟩ : Kst))
  have hdeg : (minpoly K₀ z).natDegree ≤ Module.finrank K₀ Kst := by
    rw [← IntermediateField.minpoly_eq ⟨z, hzK⟩]
    exact minpoly.natDegree_le _
  obtain ⟨r, hr0, hrd, m, hm⟩ := exists_pow_eq_zpow_of_aeval_eq_zero hγ hK₀
    (minpoly.ne_zero hint) hz (minpoly.aeval K₀ z)
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hr0 (hrd.trans hdeg)
  refine ⟨m * q, ?_⟩
  rw [hq, pow_mul, hm, zpow_mul, zpow_natCast]
/-- **Finite extensions of discretely valued subfields are discretely valued.** If the nonzero
values of `K₀` are the powers of `v ϖ`, `0 < v ϖ < 1`, then the nonzero values of a finite
extension `Kst` of `K₀` are the powers of `v ϖ'` for some `ϖ' ∈ Kst` with `0 < v ϖ' < 1`, and
`v ϖ' ^ M ≤ v ϖ` for some `M > 0`. -/
theorem exists_uniformizer_of_finiteDimensional {K₀ : Subfield F} (Kst : IntermediateField K₀ F)
    [FiniteDimensional K₀ Kst] {ϖ : F} (hϖK : ϖ ∈ K₀) (hϖ0 : ϖ ≠ 0) (hϖ1 : v ϖ < 1)
    (hK₀ : ∀ a ∈ K₀, a ≠ 0 → ∃ m : ℤ, v a = v ϖ ^ m) :
    ∃ ϖ' ∈ Kst, 0 < v ϖ' ∧ v ϖ' < 1 ∧ (∀ c ∈ Kst, c ≠ 0 → ∃ n : ℤ, v c = v ϖ' ^ n) ∧
      ∃ M : ℕ, 0 < M ∧ v ϖ' ^ M ≤ v ϖ := by
  classical
  set M := (Module.finrank K₀ Kst).factorial with hM
  have hM0 : 0 < M := Nat.factorial_pos _
  have hγ : v ϖ ≠ 0 := (v.ne_zero_iff).2 hϖ0
  have hγ0 : 0 < v ϖ := zero_lt_iff.2 hγ
  have hex : ∃ g : ℕ, 0 < g ∧ ∃ z ∈ Kst, z ≠ 0 ∧ v z ^ M = v ϖ ^ (g : ℤ) :=
    ⟨M, hM0, ϖ, Kst.algebraMap_mem ⟨ϖ, hϖK⟩, hϖ0, by rw [zpow_natCast]⟩
  obtain ⟨hg0, ϖ', hϖ'K, hϖ'0, hϖ'⟩ := Nat.find_spec hex
  set g := Nat.find hex with hg
  have hv' : v ϖ' ≠ 0 := (v.ne_zero_iff).2 hϖ'0
  have hlt : v ϖ' < 1 := by
    by_contra h
    have h1 : 1 ≤ v ϖ' ^ M := one_le_pow₀ (not_lt.1 h)
    rw [hϖ', zpow_natCast] at h1
    exact h1.not_gt (pow_lt_one₀ hγ0.le hϖ1 hg0.ne')
  refine ⟨ϖ', hϖ'K, zero_lt_iff.2 hv', hlt, fun c hc hc0 ↦ ?_, M, hM0, ?_⟩
  · obtain ⟨m, hm⟩ := exists_pow_factorial_eq_zpow Kst hγ hK₀ hc hc0
    have hy : c * ϖ' ^ (-(m / g)) ∈ Kst := mul_mem hc (zpow_mem hϖ'K _)
    have hy0 : c * ϖ' ^ (-(m / g)) ≠ 0 := mul_ne_zero hc0 (zpow_ne_zero _ hϖ'0)
    have hvy : v (c * ϖ' ^ (-(m / g))) ^ M = v ϖ ^ (m % g) := by
      rw [map_mul, map_zpow₀, mul_pow, hm, ← zpow_natCast (v ϖ' ^ _) M, ← zpow_mul,
        mul_comm (-(m / g)) (M : ℤ), zpow_mul, zpow_natCast, hϖ', ← zpow_mul,
        ← zpow_add₀ hγ, Int.emod_def]
      ring_nf
    have hg0' : (0 : ℤ) < g := Nat.cast_pos.2 hg0
    have hr : m % g = 0 := by
      by_contra hr
      have hr0 : 0 ≤ m % g := Int.emod_nonneg _ hg0'.ne'
      have hrg : m % g < g := Int.emod_lt_of_pos m hg0'
      refine Nat.find_min hex (m := (m % g).toNat) (by omega)
        ⟨by omega, _, hy, hy0, ?_⟩
      rw [Int.toNat_of_nonneg hr0, hvy]
    rw [hr, zpow_zero, ← one_pow M, pow_left_inj₀ zero_le zero_le hM0.ne', map_mul, map_zpow₀,
      zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hv')] at hvy
    exact ⟨_, hvy⟩
  · rw [hϖ', zpow_natCast]
    exact pow_le_of_le_one hγ0.le hϖ1.le hg0.ne'

end Valuation
