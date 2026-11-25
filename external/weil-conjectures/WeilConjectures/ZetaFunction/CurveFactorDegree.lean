/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import WeilConjectures.Mathlib.Analysis.Complex.Norm
public import WeilConjectures.ZetaFunction.WeilFactorization

/-!
# The degree of the middle factor of a Weil factorization in dimension one

Let `Z = P₁ / ((1 - T) (1 - q T))` be a Weil factorization in dimension `d = 1` whose middle
factor `P₁` satisfies the Riemann hypothesis. If the coefficients of `Z` grow like those of the
zeta function of a curve of genus `g`, that is `(q - 1) Z_n = h (q^{n + 1 - g} - 1)` for all large
`n` divisible by some `δ ≥ 1` and `Z_n = 0` for the other large `n`, then `deg P₁ = 2 g`.

The proof is elementary. Partial fractions give `(q - 1) Z_n = q^{n + 1} P₁(1/q) - P₁(1)` for
`n ≥ deg P₁`. Comparing with the given growth first forces `δ = 1` (three consecutive
coefficients `0, H, 0` with `H ≠ 0` cannot have this shape) and then `P₁(1) = h` and
`P₁(1/q) = h q^{-g}`. The Riemann hypothesis `|z| = q^{-1/2}` for the roots `z` of `P₁` gives
`|1/q - z| = q^{-1/2} |1 - z|`, hence `|P₁(1/q)| = q^{-deg P₁ / 2} |P₁(1)|`, and so
`q^{-g} = q^{-deg P₁ / 2}`.

This is the arithmetic half of the classical proof (F. K. Schmidt) that the middle factor of the
zeta function of a curve has degree `2 g`; the growth of the coefficients is Riemann–Roch.

## Main statements

- `AlgebraicGeometry.IsWeilFactorization.sub_one_mul_coeff_eq`: the partial fraction formula
  `(q - 1) Z_n = q^{n + 1} P₁(1/q) - P₁(1)` for `n ≥ deg P₁`.
- `AlgebraicGeometry.IsWeilFactorization.natDegree_eq_two_mul_of_coeff`: `deg P₁ = 2 g`.
-/

@[expose] public section

open Polynomial

namespace AlgebraicGeometry

namespace IsWeilFactorization

variable {q : ℕ} {Z : PowerSeries ℚ} {P : Fin (2 * 1 + 1) → Polynomial ℤ}

/-- In dimension one, `Z (1 - T) (1 - q T) = P₁`. -/
theorem mul_one_sub_mul_one_sub (h : IsWeilFactorization q 1 Z P) :
    Z * ((1 - PowerSeries.X) * (1 - PowerSeries.C (q : ℚ) * PowerSeries.X)) =
      ((P 1).map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
  have he : Finset.univ.filter (fun i : Fin (2 * 1 + 1) ↦ Even i.1) = {0, Fin.last (2 * 1)} := by
    decide
  have ho : Finset.univ.filter (fun i : Fin (2 * 1 + 1) ↦ Odd i.1) = {1} := by
    decide
  have e := h.factorization
  rw [he, ho, Finset.prod_singleton, Finset.prod_pair (by decide), h.apply_zero,
    h.apply_last] at e
  rw [← e]
  congr 2 <;> simp only [map_natCast, pow_one, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_mul, Polynomial.map_natCast, map_X, coe_sub, coe_one, coe_mul, coe_X,
    sub_right_inj, mul_eq_mul_right_iff, PowerSeries.X_ne_zero, or_false]
  exact (map_natCast (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) q).symm

/-- **Partial fractions.** For a Weil factorization in dimension one and `n ≥ deg P₁`,
`(q - 1) Z_n = q^{n + 1} P₁(1/q) - P₁(1)`: the coefficients of `1 / ((1 - T) (1 - q T))` are
`(q^{m + 1} - 1) / (q - 1)`. -/
theorem sub_one_mul_coeff_eq (h : IsWeilFactorization q 1 Z P) (hq : q ≠ 0) {n : ℕ}
    (hn : (P 1).natDegree ≤ n) :
    ((q : ℚ) - 1) * PowerSeries.coeff n Z =
      (q : ℚ) ^ (n + 1) * ((P 1).map (Int.castRingHom ℚ)).eval (q⁻¹ : ℚ) -
        ((P 1).map (Int.castRingHom ℚ)).eval 1 := by
  set Q : Polynomial ℚ := (P 1).map (Int.castRingHom ℚ) with hQ
  have hdeg : Q.natDegree ≤ n := (natDegree_map_le).trans hn
  -- `A = ∑ Tᵐ` and `B = ∑ qᵐ Tᵐ` invert `1 - T` and `1 - q T`
  set A : PowerSeries ℚ := PowerSeries.mk 1 with hA
  set B : PowerSeries ℚ := PowerSeries.mk fun m ↦ (q : ℚ) ^ m with hB
  have hA1 : A * (1 - PowerSeries.X) = 1 := PowerSeries.mk_one_mul_one_sub_eq_one ℚ
  have hB1 : B * (1 - PowerSeries.C (q : ℚ) * PowerSeries.X) = 1 := by
    have := congrArg (PowerSeries.rescale (q : ℚ)) (PowerSeries.mk_one_mul_one_sub_eq_one ℚ)
    simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X, PowerSeries.rescale_mk] at this
    simpa [hB, mul_comm] using this
  have hZ : Z = (Q : PowerSeries ℚ) * (A * B) := by
    rw [← h.mul_one_sub_mul_one_sub]
    calc Z = Z * ((A * (1 - PowerSeries.X)) * (B * (1 - PowerSeries.C (q : ℚ) * PowerSeries.X))) :=
          by rw [hA1, hB1, mul_one, mul_one]
      _ = _ := by ring
  -- the coefficients of `A * B` are the geometric sums
  have hAB (m : ℕ) : ((q : ℚ) - 1) * PowerSeries.coeff m (A * B) = (q : ℚ) ^ (m + 1) - 1 := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [hA, hB, PowerSeries.coeff_mk, Pi.one_apply, one_mul]
    rw [mul_comm, Finset.sum_mul]
    have : ∑ k ∈ Finset.range (m + 1), (q : ℚ) ^ (m - k) =
        ∑ k ∈ Finset.range (m + 1), (q : ℚ) ^ k :=
      Finset.sum_range_reflect (fun k ↦ (q : ℚ) ^ k) (m + 1)
    rw [← Finset.sum_mul, this, geom_sum_mul]
  rw [hZ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  simp only [Polynomial.coeff_coe]
  -- only the indices `k ≤ deg Q` contribute
  have hrange : ∑ k ∈ Finset.range (n + 1), ((q : ℚ) - 1) *
        (Q.coeff k * PowerSeries.coeff (n - k) (A * B)) =
      ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((q : ℚ) ^ (n - k + 1) - 1) := by
    rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hdeg)]
    rw [Finset.sum_eq_zero (s := Finset.Ico _ _) fun k hk ↦ by
      rw [coeff_eq_zero_of_natDegree_lt (by simp at hk; omega)]; ring, add_zero]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← hAB]
    ring
  rw [hrange, eval_eq_sum_range, eval_eq_sum_range, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : k ≤ n := by simp at hk; omega
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  rw [inv_pow, one_pow, mul_one, show n + 1 = (n - k + 1) + k by omega, pow_add]
  field_simp
  ring

/-- **Riemann hypothesis and the values at `1` and `1/q`.** If every complex root of `P₁` has
absolute value `q^{-1/2}`, then `|P₁(1/q)| = q^{-deg P₁ / 2} |P₁(1)|`. -/
theorem norm_eval_inv_eq (hrh : WeilRiemannHypothesis q 1 P) (hq : 0 < q) :
    ‖((P 1).map (Int.castRingHom ℂ)).eval ((q : ℂ)⁻¹)‖ =
      (q : ℝ) ^ (-((P 1).natDegree : ℝ) / 2) *
        ‖((P 1).map (Int.castRingHom ℂ)).eval 1‖ := by
  set Pc := (P 1).map (Int.castRingHom ℂ) with hPc
  have hdeg : Pc.natDegree = (P 1).natDegree :=
    natDegree_map_eq_of_injective (RingHom.injective_int _) _
  have hcard : Multiset.card Pc.roots = Pc.natDegree :=
    Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _)
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have heval (t : ℂ) : ‖Pc.eval t‖ =
      ‖Pc.leadingCoeff‖ * (Pc.roots.map fun z ↦ ‖t - z‖).prod := by
    conv_lhs => rw [← hprod]
    rw [eval_mul, eval_C, eval_multiset_prod, norm_mul, Multiset.map_map]
    congr 1
    exact (map_multiset_prod (normHom (α := ℂ)) _).trans (by simp [Multiset.map_map])
  rw [heval, heval]
  have hs : ((q : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (q : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq'.le]
    norm_num [Real.rpow_neg_one]
  have hroot : ∀ z ∈ Pc.roots, ‖((q : ℝ) : ℂ)⁻¹ - z‖ = (q : ℝ) ^ (-(1 : ℝ) / 2) * ‖1 - z‖ := by
    intro z hz
    have hz' : ‖z‖ = (q : ℝ) ^ (-(1 : ℝ) / 2) := by simpa using hrh 1 z hz
    refine (sq_eq_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hq'.le _) (norm_nonneg _))).1 ?_
    rw [mul_pow, hs]
    exact Complex.sq_norm_inv_sub_eq (by rw [hz', hs])
  have hmap : (Pc.roots.map fun z ↦ ‖((q : ℝ) : ℂ)⁻¹ - z‖) =
      Pc.roots.map fun z ↦ (q : ℝ) ^ (-(1 : ℝ) / 2) * ‖1 - z‖ :=
    Multiset.map_congr rfl hroot
  rw [show ((q : ℂ))⁻¹ = ((q : ℝ) : ℂ)⁻¹ by simp, hmap, Multiset.prod_map_mul,
    Multiset.map_const', Multiset.prod_replicate, hcard, hdeg, ← Real.rpow_natCast,
    ← Real.rpow_mul hq'.le]
  ring_nf

/-- **The degree of the middle factor.** Let `Z = P₁ / ((1 - T) (1 - q T))` be a Weil
factorization in dimension one satisfying the Riemann hypothesis, and suppose that for some
`δ ≥ 1`, `c > 0` and all large `n`, `(q - 1) Z_n = c (q^{n + 1 - g} - 1)` if `δ ∣ n` and
`Z_n = 0` otherwise. Then `deg P₁ = 2 g` (and, in fact, `δ = 1`). -/
theorem natDegree_eq_two_mul_of_coeff (h : IsWeilFactorization q 1 Z P)
    (hrh : WeilRiemannHypothesis q 1 P) (hq : 1 < q) {g δ N₀ : ℕ} {c : ℚ} (hδ : 0 < δ)
    (hc : 0 < c)
    (hZ : ∀ n, N₀ ≤ n → ((q : ℚ) - 1) * PowerSeries.coeff n Z =
      if δ ∣ n then c * ((q : ℚ) ^ (n + 1 - g) - 1) else 0) :
    (P 1).natDegree = 2 * g := by
  set Q : Polynomial ℚ := (P 1).map (Int.castRingHom ℚ) with hQ
  set D := (P 1).natDegree with hD
  set x : ℚ := Q.eval (q : ℚ)⁻¹ with hx
  set y : ℚ := Q.eval 1 with hy
  have hq0 : q ≠ 0 := by omega
  have hq1 : (1 : ℚ) < q := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < q := by linarith
  -- the two descriptions of the coefficients
  have key (n : ℕ) (hn : max D N₀ ≤ n) : (q : ℚ) ^ (n + 1) * x - y =
      if δ ∣ n then c * ((q : ℚ) ^ (n + 1 - g) - 1) else 0 := by
    rw [← h.sub_one_mul_coeff_eq hq0 (le_of_max_le_left hn), hZ n (le_of_max_le_right hn)]
  -- `δ = 1`
  have hδ1 : δ = 1 := by
    by_contra hne
    have hδ2 : 2 ≤ δ := by omega
    set n := δ * (max D N₀ + g + 1) - 1 with hn
    have hge : max D N₀ + g ≤ n := by
      have : max D N₀ + g + 1 ≤ δ * (max D N₀ + g + 1) := Nat.le_mul_of_pos_left _ hδ
      omega
    have hn1 : n + 1 = δ * (max D N₀ + g + 1) := by
      have : 1 ≤ δ * (max D N₀ + g + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      omega
    have hdvd1 : δ ∣ n + 1 := hn1 ▸ dvd_mul_right _ _
    have hndvd0 : ¬ δ ∣ n := fun hd ↦ by
      have := (Nat.dvd_add_right hd).1 hdvd1
      exact absurd (Nat.le_of_dvd one_pos this) (by omega)
    have hndvd2 : ¬ δ ∣ n + 2 := fun hd ↦ by
      have := (Nat.dvd_add_right hdvd1).1 (by rwa [show n + 2 = n + 1 + 1 by ring] at hd)
      exact absurd (Nat.le_of_dvd one_pos this) (by omega)
    have e0 := key n (by omega)
    have e1 := key (n + 1) (by omega)
    have e2 := key (n + 2) (by omega)
    rw [ite_eq_right hndvd0] at e0
    rw [ite_eq_left hdvd1] at e1
    rw [ite_eq_right hndvd2] at e2
    have hx0 : x = 0 := by
      have : (q : ℚ) ^ (n + 1) * ((q : ℚ) ^ 2 - 1) * x = 0 := by
        have : (q : ℚ) ^ (n + 2 + 1) = (q : ℚ) ^ (n + 1) * (q : ℚ) ^ 2 := by ring
        rw [this] at e2
        linear_combination e2 - e0
      rcases mul_eq_zero.1 this with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact absurd h'' (pow_ne_zero _ hqpos.ne')
        · nlinarith
      · exact h'
    have hy0 : y = 0 := by rw [hx0] at e0; linarith
    rw [hx0, hy0] at e1
    have : (1 : ℚ) < (q : ℚ) ^ (n + 1 + 1 - g) := one_lt_pow₀ hq1 (by omega)
    nlinarith
  subst hδ1
  -- `x q^g = c` and `y = c`
  set N := max D N₀ + g with hN
  have e0 := key N (by omega)
  have e1 := key (N + 1) (by omega)
  simp only [one_dvd, ite_true] at e0 e1
  have hpowN : (q : ℚ) ^ (N + 1) = (q : ℚ) ^ (N + 1 - g) * (q : ℚ) ^ g := by
    rw [← pow_add]; congr 1; omega
  have hpowN1 : (q : ℚ) ^ (N + 1 + 1 - g) = (q : ℚ) ^ (N + 1 - g) * q := by
    rw [← pow_succ]; congr 1; omega
  have hxg : x * (q : ℚ) ^ g = c := by
    have h1 : (q : ℚ) ^ (N + 1 - g) * ((q : ℚ) - 1) * (x * (q : ℚ) ^ g - c) = 0 := by
      rw [hpowN1, pow_succ, hpowN] at e1
      rw [hpowN] at e0
      linear_combination e1 - e0
    rcases mul_eq_zero.1 h1 with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' (pow_ne_zero _ hqpos.ne')
      · linarith
    · linarith
  have hyc : y = c := by
    rw [hpowN] at e0
    linear_combination -e0 + (q : ℚ) ^ (N + 1 - g) * hxg
  -- the Riemann hypothesis
  have hnorm := norm_eval_inv_eq hrh (by omega : 0 < q)
  have hcast (t : ℚ) : ((P 1).map (Int.castRingHom ℂ)).eval (t : ℂ) = ((Q.eval t : ℚ) : ℂ) := by
    have hm : (P 1).map (Int.castRingHom ℂ) = Q.map (Rat.castHom ℂ) := by
      rw [hQ, Polynomial.map_map]
      congr 1
    rw [hm, eval_map]
    exact eval₂_at_apply (Rat.castHom ℂ) t
  have hnorm' : |(x : ℝ)| = (q : ℝ) ^ (-(D : ℝ) / 2) * |(y : ℝ)| := by
    rw [← Complex.norm_ratCast, ← Complex.norm_ratCast, hx, hy, ← hcast, ← hcast]
    simpa using hnorm
  have hxr : (x : ℝ) * (q : ℝ) ^ g = c := by exact_mod_cast hxg
  have hyr : (y : ℝ) = c := by exact_mod_cast hyc
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hqr : (1 : ℝ) < q := by exact_mod_cast hq
  have hxpos : 0 < (x : ℝ) := by
    by_contra hneg
    have : (x : ℝ) * (q : ℝ) ^ g ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (by positivity)
    linarith
  rw [abs_of_pos hxpos, hyr, abs_of_pos hcr] at hnorm'
  have h1 : (q : ℝ) ^ ((g : ℝ) - D / 2) = (q : ℝ) ^ (0 : ℝ) := by
    rw [Real.rpow_zero, Real.rpow_sub (by linarith), Real.rpow_natCast, div_eq_one_iff_eq
      (Real.rpow_pos_of_pos (by linarith) _).ne']
    have : (q : ℝ) ^ (-(D : ℝ) / 2) * (q : ℝ) ^ ((D : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by linarith), show -(D : ℝ) / 2 + D / 2 = 0 by ring, Real.rpow_zero]
    nlinarith [Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < q) ((D : ℝ) / 2)]
  have h2 := (Real.rpow_right_inj (by linarith) hqr.ne').1 h1
  have : (D : ℝ) = 2 * g := by linarith
  exact_mod_cast this

end IsWeilFactorization

end AlgebraicGeometry
