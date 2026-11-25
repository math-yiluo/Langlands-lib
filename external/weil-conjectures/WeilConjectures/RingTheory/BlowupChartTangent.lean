/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.BlowupChartRegular

/-!
# Tangent directions on a regular local surface

Let `R` be a regular local ring of dimension `2` with maximal ideal `𝔪 = (x, y)`, and let
`r = ∑_{j ≤ n} p_j x ^ (n - j) y ^ j ∈ 𝔪 ^ n` be a homogeneous expansion. The initial form of `r`
vanishes on the tangent direction `y = τ x` exactly when `p(τ) ∈ 𝔪`.

## Main results

- `BlowupChart.not_mem_span_sup_pow_of_eval_ne_zero`: the line `x₀ + c y₀ = 0` is not tangent to
  `V(r)` if `-c` is not a root of the reduction of `p` (expansion in `(y₀, x₀)`).
- `BlowupChart.not_eval_mem_and_eval_mem`: if the tangent cones of `V(f)` and `V(g)` meet only at
  the origin, `p_f` and `p_g` have no common root modulo `𝔪`.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

namespace BlowupChart

variable {R : Type u} [CommRing R]

/-- Modulo an ideal in which `y` becomes `τ x`, a homogeneous form `∑ p_j x ^ (n - j) y ^ j`
becomes `x ^ n p(τ)`. -/
theorem mk_sum_eq_pow_mul_eval {I : Ideal R} {x y τ : R}
    (hy : Ideal.Quotient.mk I y = Ideal.Quotient.mk I τ * Ideal.Quotient.mk I x)
    (p : R[X]) {n : ℕ} (hp : p.natDegree ≤ n) :
    Ideal.Quotient.mk I (∑ j ∈ Finset.range (n + 1), p.coeff j * x ^ (n - j) * y ^ j) =
      Ideal.Quotient.mk I x ^ n * Ideal.Quotient.mk I (p.eval τ) := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  simp only [map_sum, map_mul, map_pow, Finset.mul_sum, hy]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [mul_pow, show n = n - j + j by omega, pow_add, Nat.add_sub_cancel]
  ring

variable [IsRegularLocalRing R]

/-- **Generic directions are not tangent.** Let `𝔪 = (x₀, y₀)` and
`r = ∑_{j ≤ n} p_j y₀ ^ (n - j) x₀ ^ j`. If `-c` is not a root of the reduction of `p`, then
`r ∉ (x₀ + c y₀) + 𝔪 ^ (n + 1)`: the line `x₀ + c y₀ = 0` is not tangent to `V(r)`. -/
theorem not_mem_span_sup_pow_of_eval_ne_zero (hdim : ringKrullDim R = 2) {x₀ y₀ : R}
    (hm : maximalIdeal R = Ideal.span {x₀, y₀}) {r : R} {n : ℕ} {p : R[X]}
    (hp : p.natDegree ≤ n)
    (hr : r = ∑ j ∈ Finset.range (n + 1), p.coeff j * y₀ ^ (n - j) * x₀ ^ j) (c : R)
    (hc : (p.map (residue R)).eval (-residue R c) ≠ 0) :
    r ∉ Ideal.span {x₀ + c * y₀} ⊔ maximalIdeal R ^ (n + 1) := by
  set x := x₀ + c * y₀
  have hm' : maximalIdeal R = Ideal.span {x, y₀} := by rw [hm, span_pair_add_mul]
  obtain ⟨-, hreg⟩ := isDomain_quotient_and_mul_eq_zero hdim hm'
  set π := Ideal.Quotient.mk (Ideal.span {x})
  have hx : π x = 0 := Ideal.Quotient.mk_singleton_self x
  have hx₀ : π x₀ = π (-c) * π y₀ := by
    rw [map_neg, neg_mul, eq_neg_iff_add_eq_zero, ← map_mul, ← map_add]
    exact hx
  intro hmem
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hmem
  have hπr : π r = π t := by
    rw [← hst, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hs, zero_add]
  have hπt : π t ∈ Ideal.span {π y₀ ^ (n + 1)} := by
    have := Ideal.mem_map_of_mem π ht
    rwa [Ideal.map_pow, hm', Ideal.map_span, Set.image_pair, hx, Ideal.span_insert_zero,
      Ideal.span_singleton_pow] at this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hπt
  rw [← hπr, hr, mk_sum_eq_pow_mul_eval hx₀ p hp] at hw
  have hpow : ∀ (k : ℕ) {a : R ⧸ Ideal.span {x}}, π y₀ ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      rw [pow_succ', mul_assoc] at ha
      exact ih (hreg _ ha)
  have h1 : π (p.eval (-c)) = w * π y₀ := by
    apply sub_eq_zero.mp
    apply hpow n
    have hw' : w * π y₀ ^ (n + 1) = π y₀ ^ n * π (eval (-c) p) := hw
    rw [mul_sub, ← hw']
    ring
  apply hc
  rw [eval_map, ← map_neg, eval₂_at_apply, residue_eq_zero_iff]
  obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [← map_mul, Ideal.Quotient.eq] at h1
  have hxm : Ideal.span {x} ≤ maximalIdeal R := by
    rw [hm']
    exact Ideal.span_mono (by simp)
  have := Ideal.add_mem _ (hxm h1) (Ideal.mul_mem_left _ w'
    (show y₀ ∈ maximalIdeal R from hm' ▸ Ideal.subset_span (by simp)))
  rwa [sub_add_cancel] at this

/-- **Separated tangent cones have no common tangent direction.** Let `𝔪 = (x, y)`, and let
`f = ∑_{j ≤ d} p_j x ^ (d - j) y ^ j` and `g = ∑_{j ≤ e} q_j x ^ (e - j) y ^ j` be such that
`𝔪 ^ n ⊆ f 𝔪 ^ (n - d) + g 𝔪 ^ (n - e) + 𝔪 ^ (n + 1)` for large `n`. Then `p(τ)` and `q(τ)` do not
both lie in `𝔪`: otherwise, modulo `y - τ x`, both `f` and `g` would have order larger than `d` and
`e` along the line `y = τ x`. -/
theorem not_eval_mem_and_eval_mem (hdim : ringKrullDim R = 2) {x y : R}
    (hm : maximalIdeal R = Ideal.span {x, y}) {f g : R} {d e : ℕ} {p q : R[X]}
    (hp : p.natDegree ≤ d) (hf : f = ∑ j ∈ Finset.range (d + 1), p.coeff j * x ^ (d - j) * y ^ j)
    (hq : q.natDegree ≤ e) (hg : g = ∑ j ∈ Finset.range (e + 1), q.coeff j * x ^ (e - j) * y ^ j)
    (hT : ∃ N : ℕ, ∀ n ≥ N, maximalIdeal R ^ n ≤ Ideal.span {f} * maximalIdeal R ^ (n - d) ⊔
      Ideal.span {g} * maximalIdeal R ^ (n - e) ⊔ maximalIdeal R ^ (n + 1))
    (τ : R) (hpτ : p.eval τ ∈ maximalIdeal R) (hqτ : q.eval τ ∈ maximalIdeal R) : False := by
  set z := y + -τ * x
  have hm' : maximalIdeal R = Ideal.span {z, x} := by
    rw [hm, span_pair_add_mul, Set.pair_comm]
  obtain ⟨-, hreg⟩ := isDomain_quotient_and_mul_eq_zero hdim hm'
  set π := Ideal.Quotient.mk (Ideal.span {z})
  have hz : π z = 0 := Ideal.Quotient.mk_singleton_self z
  have hy : π y = π τ * π x := by
    rw [← sub_eq_zero, ← map_mul, ← map_sub, ← hz]
    congr 1
    ring
  have hmap : (maximalIdeal R).map π = Ideal.span {π x} := by
    rw [hm', Ideal.map_span, Set.image_pair, hz, Ideal.span_insert_zero]
  have key : ∀ {k : ℕ} {r : R} {P : R[X]}, P.natDegree ≤ k →
      r = ∑ j ∈ Finset.range (k + 1), P.coeff j * x ^ (k - j) * y ^ j →
      P.eval τ ∈ maximalIdeal R → π r ∈ Ideal.span {π x ^ (k + 1)} := by
    intro k r P hP hr hPτ
    have h1 := Ideal.mem_map_of_mem π hPτ
    rw [hmap, Ideal.mem_span_singleton'] at h1
    obtain ⟨w, hw⟩ := h1
    rw [Ideal.mem_span_singleton', hr, mk_sum_eq_pow_mul_eval hy P hP, ← hw]
    exact ⟨w, by ring⟩
  have hpow : ∀ (k : ℕ) {a : R ⧸ Ideal.span {z}}, π x ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      rw [pow_succ', mul_assoc] at ha
      exact ih (hreg _ ha)
  obtain ⟨N, hN⟩ := hT
  set n := N + d + e
  have hxn : x ^ n ∈ maximalIdeal R ^ n :=
    Ideal.pow_mem_pow (hm ▸ Ideal.subset_span (by simp)) n
  have hmem := Ideal.mem_map_of_mem π (hN n (by omega) hxn)
  have hle : ∀ {k : ℕ} {r : R}, π r ∈ Ideal.span {π x ^ (k + 1)} → k ≤ n →
      Ideal.span {π r} * Ideal.span {π x ^ (n - k)} ≤ Ideal.span {π x ^ (n + 1)} := by
    intro k r hr hk
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hr
    rw [Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_le_span_singleton, ← hw, show n + 1 = k + 1 + (n - k) by omega,
      pow_add]
    exact ⟨w, by ring⟩
  rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_mul, Ideal.map_mul, Ideal.map_pow, Ideal.map_pow,
    Ideal.map_pow, hmap, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton] at hmem
  simp only [Ideal.span_singleton_pow] at hmem
  have hmem' : π (x ^ n) ∈ Ideal.span {π x ^ (n + 1)} := by
    exact (sup_le (sup_le (hle (key hp hf hpτ) (by omega)) (hle (key hq hg hqτ) (by omega)))
      le_rfl) hmem
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem'
  have h1 : 1 - w * π x = 0 := by
    apply hpow n
    rw [map_pow] at hw
    linear_combination -hw
  obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [← map_mul, ← map_one π, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h1
  have hzm : Ideal.span {z} ≤ maximalIdeal R := by
    rw [hm']
    exact Ideal.span_mono (by simp)
  have := Ideal.add_mem _ (hzm h1) (Ideal.mul_mem_left _ w'
    (show x ∈ maximalIdeal R from hm ▸ Ideal.subset_span (by simp)))
  rw [sub_add_cancel] at this
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)

end BlowupChart
