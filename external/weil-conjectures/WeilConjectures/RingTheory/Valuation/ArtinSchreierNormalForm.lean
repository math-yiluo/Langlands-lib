/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!

# Artin–Schreier normal forms over a Frobenius-closed lifted basis

Let `Ω` be a field of characteristic `p` with a valuation `v`, and `K ≤ L₁ ≤ L₂` subfields of `Ω`,
where `K` is perfect and Artin–Schreier closed. Let `w : ι → L₁` be a family of elements of value
`1`, *valuation independent* over `K`: the value of a `K`-combination `∑ cᵢ wᵢ` is at least the
value of each coefficient. The elements `w i ^ p ^ n` play the role of the lifts of a
Frobenius-closed basis of the residue field (Kuhlmann).

The Artin–Schreier class of an element of `L₁` approximated, up to an error of value `≤ 1`, by
`d₀ + ∑ d_{i,n} w i ^ p ^ n` (`dᵢₙ ∈ K`) is that of `∑ dᵢₙ^{1/pⁿ} wᵢ`, by the telescoping identity
`X^{pⁿ} - X = ∑_{m<n} ℘(X^{p^m})` (`℘ X = X ^ p - X`). If such an element is in `℘(L₂)` and the
residues of the `wᵢ` are never congruent to a `p`-th power of an element of `L₂` (the hypothesis
`hres`), then the leading coefficients vanish, so the element lies in `℘(L₁)`
(`AddValuation`-free statement: `exists_artinSchreier_root_of_approx`).

This is the equal-characteristic case of the stability argument of F.-V. Kuhlmann, *Elimination
of ramification I: the generalized stability theorem*, Trans. AMS 362 (2010), Prop. 4.14.

-/

@[expose] public section

open Finset

variable {Ω : Type*} [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]

omit hp [CharP Ω p] in
/-- The telescoping identity `X ^ p ^ n - X = ∑_{m < n} ((X ^ p ^ m) ^ p - X ^ p ^ m)`. -/
lemma pow_prime_pow_sub_eq_sum (X : Ω) (n : ℕ) :
    X ^ p ^ n - X = ∑ m ∈ range n, ((X ^ p ^ m) ^ p - X ^ p ^ m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← ih, ← pow_mul, ← pow_succ]
    ring

/-- An element `d * w ^ p ^ n` is Artin–Schreier equivalent to `e * w` where `e ^ p ^ n = d`. -/
lemma exists_mem_sub_artinSchreier (S : Subfield Ω) {e w : Ω} (he : e ∈ S) (hw : w ∈ S) (n : ℕ) :
    ∃ y ∈ S, e ^ p ^ n * w ^ p ^ n - e * w = y ^ p - y := by
  refine ⟨∑ m ∈ range n, (e * w) ^ p ^ m, sum_mem fun m _ ↦ pow_mem (mul_mem he hw) _, ?_⟩
  rw [← mul_pow, pow_prime_pow_sub_eq_sum p, sum_pow_char, ← sum_sub_distrib]

section NormalForm

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation Ω Γ₀)
  (K L₁ L₂ : Subfield Ω) {ι : Type*} (w : ι → Ω)

/-- **Artin–Schreier normal form.** Let `K ≤ L₁ ≤ L₂` be subfields of a valued field `Ω` of
characteristic `p`, with `K` perfect and Artin–Schreier closed, and `w : ι → L₁` a family which is
valuation independent over `K` (`hval`). Assume that every element of `L₁` of value `≤ 1` is in
`℘(L₁)` (`hhens`), and that no nonzero residual combination of the `wᵢ` is the residue of a `p`-th
power of an element of `L₂` (`hres`). Then an element `a ∈ L₁ ∩ ℘(L₂)` which is approximated, up
to an error of value `≤ 1`, by `d₀ + ∑ dⱼ (w j.1) ^ p ^ j.2` with coefficients in `K`, lies in
`℘(L₁)`. -/
theorem exists_artinSchreier_root_of_approx
    (hKL₁ : K ≤ L₁) (hL : L₁ ≤ L₂)
    (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c) (hAS : ∀ c ∈ K, ∃ d ∈ K, d ^ p - d = c)
    (hw : ∀ i, w i ∈ L₁) (hw1 : ∀ i, v (w i) = 1)
    (hval : ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      ∀ i ∈ s, v (c i) ≤ v (∑ j ∈ s, c j * w j))
    (hhens : ∀ b ∈ L₁, v b ≤ 1 → ∃ θ ∈ L₁, θ ^ p - θ = b)
    (hres : ∀ z ∈ L₂, v z ≤ 1 → ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      (∀ i ∈ s, v (c i) ≤ 1) → v (z ^ p - ∑ i ∈ s, c i * w i) < 1 → ∀ i ∈ s, v (c i) < 1)
    {a : Ω} (ha : a ∈ L₁) (s : Finset (ι × ℕ)) (d : ι × ℕ → Ω) (hd : ∀ j ∈ s, d j ∈ K)
    {d₀ : Ω} (hd₀ : d₀ ∈ K) (happrox : v (a - d₀ - ∑ j ∈ s, d j * w j.1 ^ p ^ j.2) ≤ 1)
    (h₂ : ∃ θ ∈ L₂, θ ^ p - θ = a) :
    ∃ θ ∈ L₁, θ ^ p - θ = a := by
  classical
  -- the set of elements of `L₁` in `℘(L₁)` is an additive subgroup
  let wp : Ω →+ Ω := (frobenius Ω p).toAddMonoidHom - AddMonoidHom.id Ω
  let P : AddSubgroup Ω := L₁.toAddSubgroup.map wp
  -- choose `p ^ n`-th roots of the coefficients
  have hroots : ∀ c ∈ K, ∀ n : ℕ, ∃ e ∈ K, e ^ p ^ n = c := by
    intro c hc n
    induction n generalizing c with
    | zero => exact ⟨c, hc, by simp⟩
    | succ n ih =>
      obtain ⟨e, he, rfl⟩ := hroot c hc
      obtain ⟨f, hf, rfl⟩ := ih e he
      exact ⟨f, hf, by rw [← pow_mul, pow_succ]⟩
  choose! e he hep using fun j (hj : j ∈ s) ↦ hroots (d j) (hd j hj) j.2
  -- the normal form `r₀ = ∑ᵢ Eᵢ wᵢ`
  let t : Finset ι := s.image Prod.fst
  let E : ι → Ω := fun i ↦ ∑ j ∈ s with j.1 = i, e j
  have hE : ∀ i ∈ t, E i ∈ K := fun i _ ↦ sum_mem fun j hj ↦ he j (mem_filter.1 hj).1
  have hsum : ∑ j ∈ s, e j * w j.1 = ∑ i ∈ t, E i * w i := by
    rw [← sum_fiberwise_of_maps_to (g := Prod.fst) (t := t) fun j hj ↦ mem_image_of_mem _ hj]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_mul]
    exact sum_congr rfl fun j hj ↦ by rw [(mem_filter.1 hj).2]
  -- `a - r₀ ∈ ℘(L₁)`
  have hdiff : a - ∑ i ∈ t, E i * w i ∈ P := by
    have h1 : a - d₀ - ∑ j ∈ s, d j * w j.1 ^ p ^ j.2 ∈ P :=
      hhens _ (sub_mem (sub_mem ha (hKL₁ hd₀))
        (sum_mem fun j hj ↦ mul_mem (hKL₁ (hd j hj)) (pow_mem (hw _) _))) happrox
    have h2 : d₀ ∈ P := by
      obtain ⟨θ, hθ, h⟩ := hAS d₀ hd₀
      exact ⟨θ, hKL₁ hθ, h⟩
    have h3 : ∑ j ∈ s, d j * w j.1 ^ p ^ j.2 - ∑ i ∈ t, E i * w i ∈ P := by
      rw [← hsum, ← sum_sub_distrib]
      refine sum_mem fun j hj ↦ ?_
      obtain ⟨y, hy, h⟩ := exists_mem_sub_artinSchreier p L₁ (hKL₁ (he j hj)) (hw j.1) j.2
      rw [← hep j hj]
      exact ⟨y, hy, h.symm⟩
    convert add_mem (add_mem h1 h2) h3 using 1
    ring
  -- the image of `℘(L₁)` in `L₂`
  have hP₂ : ∀ b ∈ P, ∃ θ ∈ L₂, θ ^ p - θ = b := fun b ⟨θ, hθ, h⟩ ↦ ⟨θ, hL hθ, h⟩
  by_cases hsmall : ∀ i ∈ t, v (E i) ≤ 1
  · -- the normal form has value `≤ 1`
    have hr₀ : ∑ i ∈ t, E i * w i ∈ P := by
      refine hhens _ (sum_mem fun i hi ↦ mul_mem (hKL₁ (hE i hi)) (hw i)) ?_
      refine Valuation.map_sum_le v fun i hi ↦ ?_
      rw [map_mul, hw1, mul_one]
      exact hsmall i hi
    obtain ⟨θ, hθ, h⟩ := add_mem hdiff hr₀
    have h' : θ ^ p - θ = a - ∑ i ∈ t, E i * w i + ∑ i ∈ t, E i * w i := h
    exact ⟨θ, hθ, by rw [h']; ring⟩
  · simp only [not_forall, not_le, exists_prop] at hsmall
    obtain ⟨i₁, hi₁, hbig₁⟩ := hsmall
    obtain ⟨i₀, hi₀, hmax⟩ := t.exists_max_image (fun i ↦ v (E i)) ⟨i₁, hi₁⟩
    have hbig : 1 < v (E i₀) := hbig₁.trans_le (hmax i₁ hi₁)
    set r₀ := ∑ i ∈ t, E i * w i with hr₀def
    have hvr₀ : v r₀ = v (E i₀) := by
      refine le_antisymm (Valuation.map_sum_le v fun i hi ↦ ?_) (hval t E hE i₀ hi₀)
      rw [map_mul, hw1, mul_one]
      exact hmax i hi
    obtain ⟨θ₂, hθ₂, h₂⟩ := h₂
    obtain ⟨θ₁, hθ₁, h₁⟩ := hdiff
    have h₁' : θ₁ ^ p - θ₁ = a - r₀ := h₁
    set ϑ := θ₂ - θ₁ with hϑdef
    have hϑ : ϑ ∈ L₂ := sub_mem hθ₂ (hL hθ₁)
    have hϑeq : ϑ ^ p - ϑ = r₀ := by
      rw [hϑdef, sub_pow_char]
      linear_combination h₂ - h₁'
    have hvϑ : 1 < v ϑ := by
      by_contra hle
      rw [not_lt] at hle
      have : v (ϑ ^ p - ϑ) ≤ 1 :=
        Valuation.map_sub_le v (by rw [map_pow]; exact pow_le_one' hle _) hle
      rw [hϑeq, hvr₀] at this
      exact (not_le.2 hbig) this
    have hp1 : 1 < p := hp.out.one_lt
    have hvϑp : v ϑ < v (ϑ ^ p) := by
      rw [map_pow]
      calc v ϑ = v ϑ ^ 1 := (pow_one _).symm
        _ < v ϑ ^ p := pow_lt_pow_right₀ hvϑ hp1
    have hvr₀' : v r₀ = v ϑ ^ p := by
      rw [← hϑeq, Valuation.map_sub_eq_of_lt_left v hvϑp, map_pow]
    obtain ⟨γ, hγK, hγ⟩ := hroot (E i₀) (hE i₀ hi₀)
    have hvγ : v γ = v ϑ := by
      have hpow : v γ ^ p = v ϑ ^ p := by
        rw [← map_pow, hγ, ← hvr₀, hvr₀']
      exact pow_left_injective hp.out.ne_zero hpow
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.out.ne_zero] at hγ
      rw [← hγ, map_zero] at hbig
      exact absurd hbig (not_lt.2 zero_le)
    have hγL₂ : γ ∈ L₂ := hL (hKL₁ hγK)
    have hvγ0 : v γ ≠ 0 := by rwa [Ne, Valuation.zero_iff]
    let c : ι → Ω := fun i ↦ E i / γ ^ p
    have hcK : ∀ i ∈ t, c i ∈ K := fun i hi ↦ div_mem (hE i hi) (pow_mem hγK _)
    have hvc : ∀ i ∈ t, v (c i) ≤ 1 := by
      intro i hi
      rw [map_div₀, map_pow, ← map_pow, hγ, div_le_one₀ (by
        rw [← hvr₀]; exact zero_lt_one.trans (hvr₀ ▸ hbig))]
      exact hmax i hi
    have hc₀ : v (c i₀) = 1 := by
      rw [map_div₀, map_pow, ← map_pow, hγ, div_self (by
        intro h0; rw [h0] at hbig; exact absurd hbig (not_lt.2 zero_le))]
    have hz : ϑ / γ ∈ L₂ := div_mem hϑ hγL₂
    have hvz : v (ϑ / γ) ≤ 1 := by rw [map_div₀, hvγ, div_self (by
      intro h0; rw [h0] at hvϑ; exact absurd hvϑ (not_lt.2 zero_le))]
    have hkey : (ϑ / γ) ^ p - ∑ i ∈ t, c i * w i = ϑ / γ ^ p := by
      have : ∑ i ∈ t, c i * w i = r₀ / γ ^ p := by
        rw [hr₀def, div_eq_mul_inv, Finset.sum_mul]
        exact sum_congr rfl fun i _ ↦ by ring
      rw [this, ← hϑeq, div_pow]
      field_simp
      ring
    have hlt : v ((ϑ / γ) ^ p - ∑ i ∈ t, c i * w i) < 1 := by
      rw [hkey, map_div₀, map_pow, hvγ, div_lt_one₀ (pow_pos (zero_lt_one.trans hvϑ) _)]
      calc v ϑ = v ϑ ^ 1 := (pow_one _).symm
        _ < v ϑ ^ p := pow_lt_pow_right₀ hvϑ hp1
    have := hres _ hz hvz t c hcK hvc hlt i₀ hi₀
    rw [hc₀] at this
    exact (lt_irrefl _ this).elim

end NormalForm
