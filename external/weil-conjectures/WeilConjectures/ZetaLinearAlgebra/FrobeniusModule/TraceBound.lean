/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.Topology.MetricSpace.Sequences
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace

/-!
# Weights from bounds on traces

If the power sums `∑ zᵏ` of a finite family of complex numbers are bounded by `C · Rᵏ` for all
`k ≥ 1`, then every member of the family has absolute value at most `R`. Applied to the
eigenvalues of the Frobenius, a bound `|ι tr (Fᵏ)| ≤ C · q^{kw/2}` on the traces of the powers
of the Frobenius of a Frobenius module implies that it has weights at most `w`.

## Main results

- `Complex.norm_le_of_norm_sum_pow_le`, `Multiset.norm_le_of_norm_sum_map_pow_le`: bounds on
  power sums bound the members.
- `FrobeniusModule.hasWeightsAtMost_of_norm_map_trace_pow_le`: bounds on the traces of the
  powers of the Frobenius bound the weights.
-/

@[expose] public section

universe u v

open Filter Topology

/-- If the power sums `∑ᵢ (f i)ᵏ`, `k ≥ 1`, of a finite family of complex numbers are bounded by
`C · Rᵏ` with `R > 0`, then `‖f j‖ ≤ R` for all `j`. Otherwise, normalising by the maximal
absolute value `ρ > R`, the members of absolute value `ρ` become unit complex numbers, and a
simultaneous return of their powers close to `1` (by compactness of the torus) contradicts the
bound `C · (R / ρ)ᵏ → 0`. -/
theorem Complex.norm_le_of_norm_sum_pow_le {ι : Type*} [Fintype ι] (f : ι → ℂ) {C R : ℝ}
    (hR : 0 < R) (h : ∀ k : ℕ, 1 ≤ k → ‖∑ i, f i ^ k‖ ≤ C * R ^ k) (j : ι) : ‖f j‖ ≤ R := by
  classical
  by_contra hj
  rw [not_le] at hj
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ (fun i ↦ ‖f i‖) ⟨j, Finset.mem_univ _⟩
  set ρ := ‖f i₀‖ with hρ_def
  have hρR : R < ρ := hj.trans_le (hi₀ j (Finset.mem_univ _))
  have hρ : 0 < ρ := hR.trans hρR
  set w : ι → ℂ := fun i ↦ f i / (ρ : ℂ) with hw_def
  have hw_norm : ∀ i, ‖w i‖ = ‖f i‖ / ρ := fun i ↦ by
    rw [hw_def, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  have hw_le : ∀ i, ‖w i‖ ≤ 1 := fun i ↦ by
    rw [hw_norm, div_le_one hρ]; exact hi₀ i (Finset.mem_univ _)
  have hw₀ : ‖w i₀‖ = 1 := by rw [hw_norm, div_self hρ.ne']
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨i₀⟩)
  set η : ℝ := 1 / (4 * Fintype.card ι) with hη_def
  have hη : 0 < η := by positivity
  have hev : ∀ᶠ d : ℕ in atTop, 1 ≤ d ∧ C * (R / ρ) ^ d < 1 / 2 ∧
      ∀ i, ‖w i‖ < 1 → ‖w i‖ ^ d < η := by
    refine (eventually_ge_atTop 1).and (Eventually.and ?_ ?_)
    · have : Tendsto (fun d : ℕ ↦ C * (R / ρ) ^ d) atTop (𝓝 (C * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hR hρ).le
          ((div_lt_one hρ).2 hρR)).const_mul C
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    · rw [eventually_all]
      intro i
      by_cases hi : ‖w i‖ < 1
      · exact ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hi).eventually
          (gt_mem_nhds hη)).mono fun d hd _ ↦ hd
      · exact Eventually.of_forall fun d hd ↦ absurd hd hi
  obtain ⟨D, hD⟩ := eventually_atTop.1 hev
  obtain ⟨L, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : ι → ℂ)) (r := 1))
    (x := fun k i ↦ w i ^ k) (fun k ↦ by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hw_le i))
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq (1 / 4) (by norm_num)
  have hadd := hφ.add_le_nat D N
  set d := φ (D + N) - φ N with hd
  obtain ⟨hd1, hdC, hdsmall⟩ := hD d (by omega)
  have hclose : ∀ i, ‖w i‖ = 1 → ‖w i ^ d - 1‖ < 1 / 4 := fun i hi ↦ by
    have h1 := hN (D + N) (by omega)
    rw [dist_eq_norm] at h1
    have h2 := (norm_le_pi_norm (((fun k i ↦ w i ^ k) ∘ φ) (D + N) -
      ((fun k i ↦ w i ^ k) ∘ φ) N) i).trans_lt h1
    have h3 : φ (D + N) = φ N + d := by omega
    simp only [Pi.sub_apply, Function.comp_apply, h3, pow_add] at h2
    rwa [← mul_sub_one, norm_mul, norm_pow, hi, one_pow, one_mul] at h2
  have hre_one : ∀ i, ‖w i‖ = 1 → 3 / 4 ≤ (w i ^ d).re := fun i hi ↦ by
    have h1 := Complex.abs_re_le_norm (w i ^ d - 1)
    have h2 := hclose i hi
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [neg_abs_le ((w i ^ d).re - 1)]
  have hre : ∀ i, -η ≤ (w i ^ d).re := fun i ↦ by
    rcases (hw_le i).lt_or_eq with hi | hi
    · have h1 := Complex.abs_re_le_norm (w i ^ d)
      rw [norm_pow] at h1
      linarith [hdsmall i hi, neg_abs_le (w i ^ d).re]
    · linarith [hre_one i hi]
  have hsum : 1 / 2 ≤ (∑ i, w i ^ d).re := by
    rw [Complex.re_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have h1 := Finset.card_nsmul_le_sum (Finset.univ.erase i₀) (fun i ↦ (w i ^ d).re) (-η)
      fun i _ ↦ hre i
    have h2 : ((Finset.univ.erase i₀).card : ℝ) ≤ Fintype.card ι :=
      Nat.cast_le.2 ((Finset.card_le_card (Finset.erase_subset _ _)).trans_eq Finset.card_univ)
    have h3 : (Fintype.card ι : ℝ) * η = 1 / 4 := by
      rw [hη_def]; field_simp
    rw [nsmul_eq_mul] at h1
    have h4 := mul_le_mul_of_nonneg_right h2 hη.le
    linarith [hre_one i₀ hw₀]
  have hsum_eq : ∑ i, w i ^ d = (∑ i, f i ^ d) / (ρ : ℂ) ^ d := by
    simp only [hw_def, div_pow, Finset.sum_div]
  have h1 := hsum.trans (Complex.re_le_norm _)
  rw [hsum_eq, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ.le,
    le_div_iff₀ (by positivity)] at h1
  have h2 := h d hd1
  rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)] at hdC
  linarith

/-- If the power sums `∑ zᵏ`, `k ≥ 1`, of a multiset `s` of complex numbers are bounded by
`C · Rᵏ` with `R > 0`, then every `z ∈ s` satisfies `‖z‖ ≤ R`. -/
theorem Multiset.norm_le_of_norm_sum_map_pow_le (s : Multiset ℂ) {C R : ℝ} (hR : 0 < R)
    (h : ∀ k : ℕ, 1 ≤ k → ‖(s.map (· ^ k)).sum‖ ≤ C * R ^ k) {z : ℂ} (hz : z ∈ s) :
    ‖z‖ ≤ R := by
  have key := Complex.norm_le_of_norm_sum_pow_le (fun x : s ↦ (x : ℂ)) hR (fun k hk ↦ by
    have hs : ∑ x : s, (x : ℂ) ^ k = (s.map (· ^ k)).sum := by
      rw [← Multiset.map_univ]
      rfl
    rw [hs]
    exact h k hk) (s.mkToType z ⟨0, Multiset.count_pos.2 hz⟩)
  rwa [Multiset.coe_mk] at key

namespace FrobeniusModule

/-- If the traces of the powers `Fᵏ`, `k ≥ 1`, of the Frobenius of `M` satisfy
`|ι tr (Fᵏ)| ≤ C · q^{kw/2}`, then `M` has weights at most `w`. -/
theorem hasWeightsAtMost_of_norm_map_trace_pow_le {K : Type v} [Field K] [IsAlgClosed K]
    {ι : K →+* ℂ} {q : ℕ} (hq : 1 ≤ q) (M : FrobeniusModule.{u, v} K) {w C : ℝ}
    (h : ∀ k : ℕ, 1 ≤ k →
      ‖ι (LinearMap.trace K _ (M.frobeniusEnd ^ k))‖ ≤ C * ((q : ℝ) ^ (w / 2)) ^ k) :
    M.HasWeightsAtMost ι q w := by
  intro α hα
  have hroot : α ∈ M.frobeniusEnd.charpoly.roots :=
    (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).2
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).1 hα)
  refine Multiset.norm_le_of_norm_sum_map_pow_le (M.frobeniusEnd.charpoly.roots.map ι) (C := C)
    (Real.rpow_pos_of_pos (by exact_mod_cast hq) _) (fun k hk ↦ ?_)
    (Multiset.mem_map_of_mem ι hroot)
  rw [Multiset.map_map]
  convert h k hk using 3
  rw [trace_frobeniusEnd_pow_eq_sum, map_multiset_sum, Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun x _ ↦ (map_pow ι x k).symm)

end FrobeniusModule
