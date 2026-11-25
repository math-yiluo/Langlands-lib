/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!

# Kummer normal forms over a Frobenius-closed lifted basis (mixed characteristic)

Let `Ω` be a field with a valuation `v` and `p` a prime with `0 < v p < 1` (mixed
characteristic), `K ≤ L₁ ≤ L₂` subfields with `K` closed under `p`-th roots, and `w : ι → L₁` a
family of units which is valuation independent over `K`. We show that a `1`-unit `u ∈ L₁ ∩ L₂^p`
is a `p`-th power in `L₁` (`exists_pow_eq_of_approx`), given approximations of the elements of
`L₁` by `K`-combinations of the `w i ^ p ^ n` and the usual residual hypothesis `hres` on `L₂`.

The proof follows F.-V. Kuhlmann, *Elimination of ramification I*, Trans. AMS 362 (2010),
Prop. 4.16, in two stages, where an element `x` is *negligible* if `v x ^ (p - 1) ≤ v p ^ p`
(i.e. its additive value is at least `p v(p)/(p-1)`), so that `1 + x` is a `p`-th power by
Hensel's lemma:
* stage 1, for terms of value `≥ v p`: modulo `1 + p𝔪`, `(1 + c) ^ p ≡ 1 + c ^ p`; the leading
  terms are `p`-th powers of lifted basis elements, which are cancelled exactly; the values of
  the terms stay in a finitely generated monoid, so the process terminates;
* stage 2, for terms of value `< v p`: modulo negligible elements the problem is linear, and a
  term `d w ^ p ^ (n + 1)` is replaced by `- p d^{1/p} w ^ p ^ n`.

-/

@[expose] public section

open Finset

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation Ω Γ₀) (p : ℕ)

/-- An element is *negligible* (for the Kummer theory of exponent `p`) if its additive value is
at least `p v(p) / (p - 1)`. -/
def Valuation.IsKummerNegligible (x : Ω) : Prop :=
  v x ^ (p - 1) ≤ v (p : Ω) ^ p

namespace Valuation.IsKummerNegligible

variable {v p}

lemma zero (hp : 1 < p) : v.IsKummerNegligible p 0 := by
  rw [IsKummerNegligible, map_zero, zero_pow (by omega)]
  exact zero_le

lemma add {x y : Ω} (hx : v.IsKummerNegligible p x) (hy : v.IsKummerNegligible p y) :
    v.IsKummerNegligible p (x + y) := by
  rcases le_total (v x) (v y) with h | h
  · exact (pow_le_pow_left₀ zero_le ((v.map_add x y).trans (max_eq_right h).le) _).trans hy
  · exact (pow_le_pow_left₀ zero_le ((v.map_add x y).trans (max_eq_left h).le) _).trans hx

lemma neg {x : Ω} (hx : v.IsKummerNegligible p x) : v.IsKummerNegligible p (-x) := by
  rwa [IsKummerNegligible, map_neg]

lemma sub {x y : Ω} (hx : v.IsKummerNegligible p x) (hy : v.IsKummerNegligible p y) :
    v.IsKummerNegligible p (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

lemma mul_of_le_one {x y : Ω} (hx : v.IsKummerNegligible p x) (hy : v y ≤ 1) :
    v.IsKummerNegligible p (x * y) := by
  refine le_trans ?_ hx
  rw [map_mul, mul_pow]
  exact mul_le_of_le_one_right' (pow_le_one' hy _)

lemma of_le {x y : Ω} (hx : v.IsKummerNegligible p x) (h : v y ≤ v x) :
    v.IsKummerNegligible p y :=
  (pow_le_pow_left₀ zero_le h _).trans hx

/-- The product of two elements of value `< v p` is negligible. -/
lemma mul_of_lt (hp : 2 ≤ p) (hp1 : v (p : Ω) < 1) {x y : Ω} (hx : v x < v (p : Ω))
    (hy : v y < v (p : Ω)) : v.IsKummerNegligible p (x * y) := by
  rw [IsKummerNegligible, map_mul, mul_pow]
  calc v x ^ (p - 1) * v y ^ (p - 1) ≤ v (p : Ω) ^ (p - 1) * v (p : Ω) ^ (p - 1) :=
        mul_le_mul' (pow_le_pow_left₀ zero_le hx.le _) (pow_le_pow_left₀ zero_le hy.le _)
    _ = v (p : Ω) ^ (2 * (p - 1)) := by rw [← pow_add]; ring_nf
    _ ≤ v (p : Ω) ^ p := pow_le_pow_right_of_le_one' hp1.le (by omega)

end Valuation.IsKummerNegligible

namespace Valuation

variable {v}

lemma map_natCast_le_one' (n : ℕ) : v (n : Ω) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact v.map_add_le ih (by rw [map_one])

/-- `(1 + c) ^ p = 1 + c ^ p + p c + B`, `B` the middle binomial terms. -/
lemma one_add_pow_eq (hp : 2 ≤ p) (c : Ω) :
    (1 + c) ^ p = 1 + c ^ p + (p : Ω) * c +
      ∑ i ∈ Ico 2 p, (p.choose i : Ω) * c ^ i := by
  rw [add_comm (1 : Ω) c, add_pow]
  simp only [one_pow, mul_one]
  have h1 : range (p + 1) = insert p (insert 0 (insert 1 (Ico 2 p))) := by
    ext i; simp only [mem_range, mem_insert, mem_Ico]; omega
  rw [h1, sum_insert (by simp; omega), sum_insert (by simp), sum_insert (by simp)]
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one,
    Nat.cast_one, mul_one]
  rw [sum_congr rfl fun i _ ↦ mul_comm (c ^ i) _]
  ring

/-- The middle binomial terms of `(1 + c) ^ p` are negligible when `v c ^ p < v p`. -/
lemma isKummerNegligible_binomial (hp : p.Prime) (hp1 : v (p : Ω) < 1) {c : Ω}
    (hc : v c ^ p < v (p : Ω)) :
    v.IsKummerNegligible p (∑ i ∈ Ico 2 p, (p.choose i : Ω) * c ^ i) := by
  have hp2 := hp.two_le
  have hc1 : v c < 1 := by
    by_contra h
    rw [not_lt] at h
    exact (not_le.2 (hc.trans hp1)) (one_le_pow₀ h)
  -- each term has value `≤ v p * v c ^ 2`, which is negligible
  have hneg : ∀ x : Ω, v x ≤ v (p : Ω) * v c ^ 2 → v.IsKummerNegligible p x := by
    intro x hx
    refine (pow_le_pow_left₀ zero_le hx _).trans ?_
    rw [mul_pow, ← pow_mul]
    calc v (p : Ω) ^ (p - 1) * v c ^ (2 * (p - 1))
        ≤ v (p : Ω) ^ (p - 1) * v c ^ p :=
          mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hc1.le (by omega))
      _ ≤ v (p : Ω) ^ (p - 1) * v (p : Ω) := mul_le_mul' le_rfl hc.le
      _ = v (p : Ω) ^ p := by rw [← pow_succ]; congr 1; omega
  refine hneg _ (v.map_sum_le fun i hi ↦ ?_)
  rw [mem_Ico] at hi
  obtain ⟨m, hm⟩ := hp.dvd_choose_self (by omega : i ≠ 0) hi.2
  rw [hm, Nat.cast_mul, map_mul, map_mul, map_pow]
  calc v (p : Ω) * v (m : Ω) * v c ^ i ≤ v (p : Ω) * 1 * v c ^ 2 :=
        mul_le_mul' (mul_le_mul' le_rfl (map_natCast_le_one' m))
          (pow_le_pow_right_of_le_one' hc1.le hi.1)
    _ = v (p : Ω) * v c ^ 2 := by rw [mul_one]

/-- The middle binomial terms of `(1 + c) ^ p` have value at most `v p * v c ^ i`. -/
lemma valuation_choose_mul_pow_le (hp : p.Prime) (c : Ω) {i : ℕ} (hi : i ∈ Ico 2 p) :
    v ((p.choose i : Ω) * c ^ i) ≤ v (p : Ω) * v c ^ i := by
  rw [mem_Ico] at hi
  obtain ⟨m, hm⟩ := hp.dvd_choose_self (by omega : i ≠ 0) hi.2
  rw [hm, Nat.cast_mul, map_mul, map_mul, map_pow]
  exact mul_le_mul' (mul_le_of_le_one_right' (map_natCast_le_one' m)) le_rfl

end Valuation

section Stage2

/-- The combination `∑ⱼ dⱼ (w j.1) ^ p ^ j.2` of lifted Frobenius powers. -/
noncomputable def liftedSum (p : ℕ) {ι : Type*} (w : ι → Ω) (d : ι × ℕ →₀ Ω) : Ω :=
  d.sum fun j c ↦ c * w j.1 ^ p ^ j.2

variable {v p} {ι : Type*} (w : ι → Ω)

variable {w} in
lemma liftedSum_add (d d' : ι × ℕ →₀ Ω) :
    liftedSum p w (d + d') = liftedSum p w d + liftedSum p w d' :=
  Finsupp.sum_add_index' (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _

lemma liftedSum_single (j : ι × ℕ) (c : Ω) :
    liftedSum p w (Finsupp.single j c) = c * w j.1 ^ p ^ j.2 :=
  Finsupp.sum_single_index (zero_mul _)

lemma liftedSum_erase (d : ι × ℕ →₀ Ω) (j : ι × ℕ) :
    liftedSum p w d = liftedSum p w (d.erase j) + d j * w j.1 ^ p ^ j.2 := by
  classical
  conv_lhs => rw [← Finsupp.erase_add_single j d]
  rw [liftedSum_add, liftedSum_single]

/-- The value of a lifted sum is at most the largest value of its coefficients. -/
lemma valuation_liftedSum_le (hw1 : ∀ i, v (w i) = 1) (d : ι × ℕ →₀ Ω) {γ : Γ₀}
    (hd : ∀ j, v (d j) ≤ γ) : v (liftedSum p w d) ≤ γ := by
  refine v.map_sum_le fun j _ ↦ ?_
  rw [map_mul, map_pow, hw1, one_pow, mul_one]
  exact hd j

end Stage2

section Stage2Step

variable {v p} {ι : Type*} {w : ι → Ω}

lemma valuation_one_add_eq_one {x : Ω} (hx : v x < 1) : v (1 + x) = 1 := by
  rw [add_comm, Valuation.map_add_eq_of_lt_right v (by rwa [map_one])]
  exact map_one v

/-- **One replacement step of stage 2**: a term `d (w i) ^ p ^ (k + 1)` of value `< v p` is
replaced, up to the `p`-th power `(1 + c) ^ p` (`c = d^{1/p} (w i) ^ p ^ k`) and a negligible
error, by `- p d^{1/p} (w i) ^ p ^ k`. -/
lemma kummer_stage2_step (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hw1 : ∀ i, v (w i) = 1) (d : ι × ℕ →₀ Ω) (hdv : ∀ j, v (d j) < v (p : Ω)) {d₀ : Ω}
    (hd₀ : v d₀ < v (p : Ω)) {n : Ω} (hn : v.IsKummerNegligible p n) (i : ι) (k : ℕ) {e : Ω}
    (he : e ^ p = d (i, k + 1)) :
    ∃ n', v.IsKummerNegligible p n' ∧
      (1 + d₀ + liftedSum p w d) * (1 + n) = (1 + e * w i ^ p ^ k) ^ p *
        ((1 + d₀ + liftedSum p w (d.erase (i, k + 1) + Finsupp.single (i, k) (-(p : Ω) * e))) *
          (1 + n')) ∧
      v (e * w i ^ p ^ k) < 1 ∧
      ∀ j, v ((d.erase (i, k + 1) + Finsupp.single (i, k) (-(p : Ω) * e)) j) < v (p : Ω) := by
  classical
  have hp2 := hp.two_le
  set c := e * w i ^ p ^ k with hcdef
  set d' := d.erase (i, k + 1) + Finsupp.single (i, k) (-(p : Ω) * e) with hd'def
  set T := d₀ + liftedSum p w d' with hTdef
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  have hvce : v c = v e := by rw [hcdef, map_mul, map_pow, hw1, one_pow, mul_one]
  have hvc : v c ^ p = v (d (i, k + 1)) := by rw [hvce, ← map_pow, he]
  have hvcp : v c ^ p < v (p : Ω) := hvc ▸ hdv _
  have hc1 : v c < 1 := by
    by_contra h
    rw [not_lt] at h
    exact (not_le.2 (hvcp.trans hp1)) (one_le_pow₀ h)
  have he1 : v e < 1 := hvce ▸ hc1
  have hd' : ∀ j, v (d' j) < v (p : Ω) := by
    intro j
    rw [hd'def, Finsupp.add_apply]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [Finsupp.erase_apply]
      split_ifs
      · rw [map_zero]; exact hvp
      · exact hdv j
    · rw [Finsupp.single_apply]
      split_ifs
      · rw [map_mul, v.map_neg]
        exact mul_lt_of_lt_one_right hvp he1
      · rw [map_zero]; exact hvp
  have hSd : liftedSum p w d = liftedSum p w d' + c ^ p + (p : Ω) * c := by
    rw [liftedSum_erase w d (i, k + 1), hd'def, liftedSum_add, liftedSum_single, hcdef,
      mul_pow, ← pow_mul, ← pow_succ, he]
    ring
  have hTv : v T < v (p : Ω) := by
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt hd₀ ?_)
    exact v.map_sum_lt hvp.ne' fun j _ ↦ by
      rw [map_mul, map_pow, hw1, one_pow, mul_one]; exact hd' j
  have hT1 : v T < 1 := hTv.trans hp1
  have hB := Valuation.isKummerNegligible_binomial p hp hp1 hvcp
  set B := ∑ i ∈ Ico 2 p, (p.choose i : Ω) * c ^ i with hBdef
  set D := (1 + c) ^ p * (1 + T) with hDdef
  have hD : v D = 1 := by
    rw [hDdef, map_mul, map_pow, valuation_one_add_eq_one hc1, valuation_one_add_eq_one hT1,
      one_pow, one_mul]
  have hD0 : D ≠ 0 := by intro h; rw [h, map_zero] at hD; exact zero_ne_one hD
  set A := 1 + d₀ + liftedSum p w d with hAdef
  have hA1 : v A ≤ 1 := by
    rw [hAdef, hSd]
    refine v.map_add_le (v.map_add_le (by rw [map_one]) (hd₀.trans hp1).le)
      (v.map_add_le (v.map_add_le ?_ ?_) ?_)
    · exact v.map_sum_le fun j _ ↦ by
        rw [map_mul, map_pow, hw1, one_pow, mul_one]; exact (hd' j).le.trans hp1.le
    · rw [map_pow]; exact pow_le_one' hc1.le _
    · rw [map_mul]; exact mul_le_one' hp1.le hc1.le
  have hkey : A * (1 + n) - D = A * n - T * (c ^ p + (p : Ω) * c) - B * (1 + T) := by
    rw [hDdef, Valuation.one_add_pow_eq p hp.two_le c, hAdef, hSd, hTdef]
    ring
  have hnum : v.IsKummerNegligible p (A * (1 + n) - D) := by
    rw [hkey]
    have hAn : v.IsKummerNegligible p (A * n) := by rw [mul_comm]; exact hn.mul_of_le_one hA1
    refine (hAn.sub ?_).sub ?_
    · refine Valuation.IsKummerNegligible.mul_of_lt hp.two_le hp1 hTv ?_
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
      · rw [map_pow]; exact hvcp
      · rw [map_mul]; exact mul_lt_of_lt_one_right hvp hc1
    · exact hB.mul_of_le_one (v.map_add_le (by rw [map_one]) hT1.le)
  refine ⟨(A * (1 + n) - D) / D, ?_, ?_, hc1, hd'⟩
  · refine hnum.of_le ?_
    rw [map_div₀, hD, div_one]
  · have hD' : (1 + c) ^ p * (1 + d₀ + liftedSum p w d') = D := by
      rw [hDdef, hTdef, add_assoc]
    rw [← mul_assoc, hD']
    field_simp
    ring

end Stage2Step

section Stage2Base

variable {v p} {ι : Type*} {w : ι → Ω} (K L₁ L₂ : Subfield Ω)

/-- **Stage 2, base case**: a `1`-unit `(1 + d₀ + ∑ᵢ Eᵢ wᵢ) (1 + n)` of `L₁` with coefficients of
value `< v p` in `K` and `n` negligible, which is a `p`-th power in `L₂`, is a `p`-th power in
`L₁`. -/
theorem kummer_stage2_base (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hKL₁ : K ≤ L₁) (hL : L₁ ≤ L₂) (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c)
    (hw : ∀ i, w i ∈ L₁) (hw1 : ∀ i, v (w i) = 1)
    (hval : ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      ∀ i ∈ s, v (c i) ≤ v (∑ j ∈ s, c j * w j))
    (hhens : ∀ x ∈ L₁, v.IsKummerNegligible p x → ∃ y ∈ L₁, y ^ p = 1 + x)
    (hres : ∀ z ∈ L₂, v z ≤ 1 → ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      (∀ i ∈ s, v (c i) ≤ 1) → v (z ^ p - ∑ i ∈ s, c i * w i) < 1 → ∀ i ∈ s, v (c i) < 1)
    (s : Finset ι) (E : ι → Ω) (hE : ∀ i ∈ s, E i ∈ K) (hEv : ∀ i ∈ s, v (E i) < v (p : Ω))
    {d₀ : Ω} (hd₀ : d₀ ∈ K) (hd₀v : v d₀ < v (p : Ω)) {n : Ω} (hnL : n ∈ L₁)
    (hn : v.IsKummerNegligible p n)
    (h₂ : ∃ y ∈ L₂, y ^ p = (1 + d₀ + ∑ i ∈ s, E i * w i) * (1 + n)) :
    ∃ y ∈ L₁, y ^ p = (1 + d₀ + ∑ i ∈ s, E i * w i) * (1 + n) := by
  classical
  have hp2 := hp.two_le
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  have hd₀1 : v d₀ < 1 := hd₀v.trans hp1
  have h1d : v (1 + d₀) = 1 := valuation_one_add_eq_one hd₀1
  have h1d0 : 1 + d₀ ≠ 0 := by intro h; rw [h, map_zero] at h1d; exact zero_ne_one h1d
  obtain ⟨g, hgK, hg⟩ := hroot (1 + d₀) (add_mem (one_mem _) hd₀)
  have hg0 : g ≠ 0 := by rintro rfl; rw [zero_pow hp.ne_zero] at hg; exact h1d0 hg.symm
  set E' : ι → Ω := fun i ↦ E i / (1 + d₀) with hE'def
  set F := ∑ i ∈ s, E' i * w i with hFdef
  have hE'K : ∀ i ∈ s, E' i ∈ K := fun i hi ↦ div_mem (hE i hi) (add_mem (one_mem _) hd₀)
  have hE'v : ∀ i, v (E' i) = v (E i) := fun i ↦ by rw [hE'def, map_div₀, h1d, div_one]
  have hfac : 1 + d₀ + ∑ i ∈ s, E i * w i = (1 + d₀) * (1 + F) := by
    rw [hFdef, mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hE'def]; field_simp
  have hFL : F ∈ L₁ := sum_mem fun i hi ↦ mul_mem (hKL₁ (hE'K i hi)) (hw i)
  have hFv : v F < v (p : Ω) := v.map_sum_lt hvp.ne' fun i hi ↦ by
    rw [map_mul, hw1, mul_one, hE'v]; exact hEv i hi
  by_cases hFn : v.IsKummerNegligible p F
  · -- the element is a `p`-th power by Hensel's lemma
    have hx : v.IsKummerNegligible p (F + n + F * n) :=
      (hFn.add hn).add (by rw [mul_comm]; exact hn.mul_of_le_one (hFv.trans hp1).le)
    obtain ⟨y₀, hy₀, hy₀p⟩ := hhens _ (add_mem (add_mem hFL hnL) (mul_mem hFL hnL)) hx
    refine ⟨g * y₀, mul_mem (hKL₁ hgK) hy₀, ?_⟩
    rw [mul_pow, hg, hy₀p, hfac]
    ring
  · exfalso
    rw [Valuation.IsKummerNegligible, not_le] at hFn
    have hsne : s.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [hFdef, h, Finset.sum_empty, map_zero, zero_pow (by omega)] at hFn
      exact not_lt.2 zero_le hFn
    obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image (fun i ↦ v (E' i)) hsne
    have hvF : v F = v (E' i₀) := le_antisymm
      (v.map_sum_le fun i hi ↦ by rw [map_mul, hw1, mul_one]; exact hmax i hi)
      (hval s E' hE'K i₀ hi₀)
    obtain ⟨y, hyL, hyp⟩ := h₂
    set Y := y / g with hYdef
    have hYL : Y ∈ L₂ := div_mem hyL (hL (hKL₁ hgK))
    set n₂ := n * (1 + F) with hn₂def
    have hYp : Y ^ p = 1 + F + n₂ := by
      rw [hYdef, div_pow, hyp, hfac, hg, hn₂def]
      field_simp
    have hn₂ : v.IsKummerNegligible p n₂ :=
      hn.mul_of_le_one (v.map_add_le (by rw [map_one]) (hFv.trans hp1).le)
    have hn₂F : v n₂ < v F := by
      by_contra h
      rw [not_lt] at h
      exact (not_le.2 hFn) ((pow_le_pow_left₀ zero_le h _).trans hn₂)
    set s₀ := Y - 1 with hs₀def
    set B := ∑ i ∈ Ico 2 p, (p.choose i : Ω) * s₀ ^ i with hBdef
    have hexp : F + n₂ = s₀ ^ p + ((p : Ω) * s₀ + B) := by
      have h := Valuation.one_add_pow_eq p hp2 s₀
      rw [show 1 + s₀ = Y by rw [hs₀def]; ring, hYp] at h
      linear_combination h
    have hvFn₂ : v (F + n₂) = v F := v.map_add_eq_of_lt_left hn₂F
    set σ := v s₀ with hσdef
    have hBle : ∀ i ∈ Ico 2 p, v ((p.choose i : Ω) * s₀ ^ i) ≤ v (p : Ω) * σ ^ i :=
      fun i hi ↦ Valuation.valuation_choose_mul_pow_le p hp s₀ hi
    have hFp : v F < 1 := hFv.trans hp1
    -- `σ < 1`
    have hσ1 : σ < 1 := by
      by_contra h
      rw [not_lt] at h
      have hσpos : 0 < σ ^ (p - 1) := pow_pos (zero_lt_one.trans_le h) _
      have hbig : v (p : Ω) * σ ^ (p - 1) < σ ^ p :=
        calc v (p : Ω) * σ ^ (p - 1) < σ ^ (p - 1) := mul_lt_of_lt_one_left hσpos hp1
          _ ≤ σ ^ p := pow_le_pow_right₀ h (by omega)
      have hrest : v ((p : Ω) * s₀ + B) < σ ^ p := by
        refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_mul' le_rfl (le_self_pow₀ h (by omega))) hbig
        · refine lt_of_le_of_lt (v.map_sum_le fun i hi ↦ (hBle i hi).trans ?_) hbig
          exact mul_le_mul' le_rfl (pow_le_pow_right₀ h (by rw [mem_Ico] at hi; omega))
      have := congrArg v hexp
      rw [hvFn₂, v.map_add_eq_of_lt_left (by rwa [map_pow])] at this
      rw [map_pow] at this
      exact not_le.2 hFp (this ▸ one_le_pow₀ h)
    have hrest : v ((p : Ω) * s₀ + B) ≤ v (p : Ω) * σ := by
      refine v.map_add_le (by rw [map_mul]) (v.map_sum_le fun i hi ↦ (hBle i hi).trans ?_)
      exact mul_le_mul' le_rfl (pow_le_of_le_one zero_le hσ1.le (by rw [mem_Ico] at hi; omega))
    by_cases hsm : σ ^ (p - 1) ≤ v (p : Ω)
    · -- then `F` would be negligible
      have hle : v F ≤ v (p : Ω) * σ := by
        rw [← hvFn₂, hexp]
        refine v.map_add_le ?_ hrest
        rw [map_pow, ← pow_sub_one_mul (by omega : p ≠ 0)]
        exact mul_le_mul' hsm le_rfl
      refine (not_le.2 hFn) ((pow_le_pow_left₀ zero_le hle _).trans ?_)
      rw [mul_pow]
      calc v (p : Ω) ^ (p - 1) * σ ^ (p - 1) ≤ v (p : Ω) ^ (p - 1) * v (p : Ω) :=
            mul_le_mul' le_rfl hsm
        _ = v (p : Ω) ^ p := by rw [← pow_succ]; congr 1; omega
    · rw [not_le] at hsm
      have hσ0 : σ ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by omega)] at hsm
        exact not_lt.2 zero_le hsm
      have hlt : v (p : Ω) * σ < σ ^ p := by
        rw [← pow_sub_one_mul (by omega : p ≠ 0)]
        exact mul_lt_mul_of_pos_right hsm (zero_lt_iff.2 hσ0)
      have hvFσ : v F = σ ^ p := by
        rw [← hvFn₂, hexp, v.map_add_eq_of_lt_left (by rw [map_pow]; exact hrest.trans_lt hlt),
          map_pow]
      obtain ⟨γ, hγK, hγ⟩ := hroot (E' i₀) (hE'K i₀ hi₀)
      have hvγ : v γ = σ := by
        refine @pow_left_injective Γ₀ inferInstance inferInstance p hp.ne_zero _ _ ?_
        simp only
        rw [← map_pow, hγ, ← hvF, hvFσ]
      have hγ0 : γ ≠ 0 := by intro h; rw [h, map_zero] at hvγ; exact hσ0 hvγ.symm
      set c : ι → Ω := fun i ↦ E' i / γ ^ p with hcdef
      have hcK : ∀ i ∈ s, c i ∈ K := fun i hi ↦ div_mem (hE'K i hi) (pow_mem hγK _)
      have hγp : v (γ ^ p) = v F := by rw [map_pow, hvγ, hvFσ]
      have hFne : v F ≠ 0 := by rw [hvFσ]; exact pow_ne_zero _ hσ0
      have hcv : ∀ i ∈ s, v (c i) ≤ 1 := fun i hi ↦ by
        rw [hcdef, map_div₀, hγp, div_le_one₀ (zero_lt_iff.2 hFne), hvF]; exact hmax i hi
      have hc₀ : v (c i₀) = 1 := by rw [hcdef, map_div₀, hγp, hvF, div_self (hvF ▸ hFne)]
      have hzL : s₀ / γ ∈ L₂ := div_mem (sub_mem hYL (one_mem _)) (hL (hKL₁ hγK))
      have hz1 : v (s₀ / γ) ≤ 1 := by rw [map_div₀, hvγ, div_self hσ0]
      have hsum : ∑ i ∈ s, c i * w i = F / γ ^ p := by
        rw [hFdef, div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [hcdef]; ring
      have hident : (s₀ / γ) ^ p - ∑ i ∈ s, c i * w i = (n₂ - ((p : Ω) * s₀ + B)) / γ ^ p := by
        rw [hsum, div_pow]
        rw [div_sub_div_same]
        congr 1
        linear_combination -hexp
      have hlt1 : v ((s₀ / γ) ^ p - ∑ i ∈ s, c i * w i) < 1 := by
        rw [hident, map_div₀, hγp, div_lt_one₀ (zero_lt_iff.2 hFne)]
        refine lt_of_le_of_lt (v.map_sub _ _) (max_lt hn₂F ?_)
        rw [hvFσ]; exact hrest.trans_lt hlt
      have := hres _ hzL hz1 s c hcK hcv hlt1 i₀ hi₀
      rw [hc₀] at this
      exact lt_irrefl _ this

end Stage2Base

section Stage2Main

variable {v p} {ι : Type*} {w : ι → Ω} (K L₁ L₂ : Subfield Ω)

/-- The lifted sum of a combination of depth zero. -/
lemma liftedSum_eq_sum_image [DecidableEq ι] (d : ι × ℕ →₀ Ω) (h0 : ∀ j ∈ d.support, j.2 = 0) :
    liftedSum p w d = ∑ i ∈ d.support.image Prod.fst, d (i, 0) * w i := by
  rw [liftedSum, Finsupp.sum, Finset.sum_image]
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    obtain ⟨a, b⟩ := j
    obtain rfl : b = 0 := h0 _ hj
    simp
  · intro j hj j' hj' h
    exact Prod.ext h ((h0 j hj).trans (h0 j' hj').symm)

lemma sum_snd_support_lt (d : ι × ℕ →₀ Ω) (i : ι) (k : ℕ)
    (hj : (i, k + 1) ∈ d.support) (x : Ω) :
    (d.erase (i, k + 1) + Finsupp.single (i, k) x).support.sum Prod.snd <
      d.support.sum Prod.snd := by
  classical
  classical
  have hsub : (d.erase (i, k + 1) + Finsupp.single (i, k) x).support ⊆
      insert (i, k) (d.support.erase (i, k + 1)) := by
    refine Finsupp.support_add.trans ?_
    rw [Finsupp.support_erase]
    exact Finset.union_subset (Finset.subset_insert _ _)
      (Finsupp.support_single_subset.trans (by simp))
  calc (d.erase (i, k + 1) + Finsupp.single (i, k) x).support.sum Prod.snd
      ≤ (insert (i, k) (d.support.erase (i, k + 1))).sum Prod.snd :=
        Finset.sum_le_sum_of_subset hsub
    _ ≤ k + (d.support.erase (i, k + 1)).sum Prod.snd := by
        by_cases h : (i, k) ∈ d.support.erase (i, k + 1)
        · rw [Finset.insert_eq_of_mem h]; omega
        · rw [Finset.sum_insert h]
    _ < d.support.sum Prod.snd := by
        rw [← Finset.sum_erase_add d.support Prod.snd hj]
        rw [add_comm]; exact Nat.add_lt_add_left (Nat.lt_succ_self k) _

/-- **Stage 2 of the Kummer normal form.** -/
theorem kummer_stage2 (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hKL₁ : K ≤ L₁) (hL : L₁ ≤ L₂) (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c)
    (hw : ∀ i, w i ∈ L₁) (hw1 : ∀ i, v (w i) = 1)
    (hval : ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      ∀ i ∈ s, v (c i) ≤ v (∑ j ∈ s, c j * w j))
    (hhens : ∀ x ∈ L₁, v.IsKummerNegligible p x → ∃ y ∈ L₁, y ^ p = 1 + x)
    (hres : ∀ z ∈ L₂, v z ≤ 1 → ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      (∀ i ∈ s, v (c i) ≤ 1) → v (z ^ p - ∑ i ∈ s, c i * w i) < 1 → ∀ i ∈ s, v (c i) < 1)
    (d : ι × ℕ →₀ Ω) (hd : ∀ j, d j ∈ K) (hdv : ∀ j, v (d j) < v (p : Ω))
    {d₀ : Ω} (hd₀ : d₀ ∈ K) (hd₀v : v d₀ < v (p : Ω)) {n : Ω} (hnL : n ∈ L₁)
    (hn : v.IsKummerNegligible p n)
    (h₂ : ∃ y ∈ L₂, y ^ p = (1 + d₀ + liftedSum p w d) * (1 + n)) :
    ∃ y ∈ L₁, y ^ p = (1 + d₀ + liftedSum p w d) * (1 + n) := by
  classical
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  induction hN : d.support.sum Prod.snd using Nat.strong_induction_on generalizing d n with
  | _ N ih =>
  by_cases hex : ∃ j ∈ d.support, j.2 ≠ 0
  · obtain ⟨⟨i, k'⟩, hj, hk⟩ := hex
    obtain ⟨k, rfl⟩ : ∃ k, k' = k + 1 := ⟨k' - 1, by simp at hk; omega⟩
    obtain ⟨e, heK, he⟩ := hroot _ (hd (i, k + 1))
    obtain ⟨n', hn', heq, hc1, hd'v⟩ :=
      kummer_stage2_step hp hp1 hp0 hw1 d hdv hd₀v hn i k he
    set c := e * w i ^ p ^ k with hcdef
    set d' := d.erase (i, k + 1) + Finsupp.single (i, k) (-(p : Ω) * e) with hd'def
    have hcL : c ∈ L₁ := mul_mem (hKL₁ heK) (pow_mem (hw i) _)
    have h1c : (1 + c) ^ p ≠ 0 := pow_ne_zero _ (by
      intro h; have := valuation_one_add_eq_one hc1; rw [h, map_zero] at this
      exact zero_ne_one this)
    have hd'K : ∀ j, d' j ∈ K := fun j ↦ by
      rw [hd'def, Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply]
      refine add_mem (by split_ifs; exacts [zero_mem _, hd j]) (by
        split_ifs; exacts [mul_mem (neg_mem (natCast_mem _ _)) heK, zero_mem _])
    have hSL : liftedSum p w d' ∈ L₁ := sum_mem fun j _ ↦
      mul_mem (hKL₁ (hd'K j)) (pow_mem (hw j.1) _)
    have hT1 : v (d₀ + liftedSum p w d') < 1 := by
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt (hd₀v.trans hp1) ?_)
      exact (v.map_sum_lt hvp.ne' fun j _ ↦ by
        rw [map_mul, map_pow, hw1, one_pow, mul_one]; exact hd'v j).trans hp1
    have hA0 : 1 + d₀ + liftedSum p w d' ≠ 0 := by
      intro h; have := valuation_one_add_eq_one hT1; rw [← add_assoc, h, map_zero] at this
      exact zero_ne_one this
    have hn'L : n' ∈ L₁ := by
      have h1n' : 1 + n' = (1 + d₀ + liftedSum p w d) * (1 + n) /
          ((1 + c) ^ p * (1 + d₀ + liftedSum p w d')) := by
        rw [heq]; field_simp
      have : 1 + n' ∈ L₁ := by
        rw [h1n']
        refine div_mem (mul_mem (add_mem (add_mem (one_mem _) (hKL₁ hd₀)) (sum_mem fun j _ ↦
          mul_mem (hKL₁ (hd j)) (pow_mem (hw j.1) _))) (add_mem (one_mem _) hnL))
          (mul_mem (pow_mem (add_mem (one_mem _) hcL) _)
            (add_mem (add_mem (one_mem _) (hKL₁ hd₀)) hSL))
      simpa using sub_mem this (one_mem L₁)
    have hlt := sum_snd_support_lt d i k hj (-(p : Ω) * e)
    rw [hN] at hlt
    obtain ⟨y', hy'L, hy'⟩ := ih _ hlt d' hd'K hd'v hn'L hn' (by
      obtain ⟨y, hyL, hy⟩ := h₂
      refine ⟨y / (1 + c), div_mem hyL (hL (add_mem (one_mem _) hcL)), ?_⟩
      rw [div_pow, hy, heq]
      field_simp) rfl
    refine ⟨(1 + c) * y', mul_mem (add_mem (one_mem _) hcL) hy'L, ?_⟩
    rw [mul_pow, hy', heq]
  · push Not at hex
    have h0 : ∀ j ∈ d.support, j.2 = 0 := hex
    rw [liftedSum_eq_sum_image d h0] at h₂ ⊢
    refine kummer_stage2_base K L₁ L₂ hp hp1 hp0 hKL₁ hL hroot hw hw1 hval hhens hres _
      (fun i ↦ d (i, 0)) (fun i _ ↦ hd _) (fun i _ ↦ hdv _) hd₀ hd₀v hnL hn h₂

end Stage2Main
