/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.KummerNormalForm
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!

# Kummer normal forms, stage 1: terms of value at least `v p`

We continue the setting of `WeilConjectures.RingTheory.Valuation.KummerNormalForm`. Let
`m : Option (ι × ℕ) → Ω` be the lifted Frobenius monomials (`m none = 1`,
`m (some (i, n)) = w i ^ p ^ n`). In stage 1 of the Kummer normal form, a `1`-unit `u ∈ L₁` with
`u ∈ L₂ ^ p`, congruent modulo `{v < v p}` to a combination of the monomials with coefficients in
a *discretely valued* subfield `K* ≤ K`, is multiplied by `p`-th powers of `L₁` until
`v (u - 1) < v p` (`exists_valuation_div_pow_sub_one_lt`).

The leading terms of value `μ ≥ v p` are `p`-th powers of monomials (the residual hypothesis
`hres1`), hence cancelled by dividing by `(1 + c) ^ p` for an explicit `c ∈ L₁`, up to terms of
value `< v p` and products of monomials, which are re-expanded (`hprod`). The value `μ` takes
finitely many values in the discrete value group of `K*`, so the process terminates.

-/

@[expose] public section

open Finset

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation Ω Γ₀} {p : ℕ} {ι : Type*}

/-- The lifted Frobenius monomials: `1` and the `w i ^ p ^ n`. -/
def frobeniusMonomial (p : ℕ) (w : ι → Ω) (j : Option (ι × ℕ)) : Ω :=
  j.elim 1 fun i ↦ w i.1 ^ p ^ i.2

/-- A combination of lifted Frobenius monomials. -/
noncomputable def frobeniusComb (p : ℕ) (w : ι → Ω) (c : Option (ι × ℕ) →₀ Ω) : Ω :=
  c.sum fun j a ↦ a * frobeniusMonomial p w j

variable (p) {w : ι → Ω}

lemma frobeniusComb_add (c c' : Option (ι × ℕ) →₀ Ω) :
    frobeniusComb p w (c + c') = frobeniusComb p w c + frobeniusComb p w c' :=
  Finsupp.sum_add_index' (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _

lemma frobeniusComb_single (j : Option (ι × ℕ)) (a : Ω) :
    frobeniusComb p w (Finsupp.single j a) = a * frobeniusMonomial p w j :=
  Finsupp.sum_single_index (zero_mul _)

lemma frobeniusComb_zero : frobeniusComb p w (0 : Option (ι × ℕ) →₀ Ω) = 0 :=
  Finsupp.sum_zero_index

lemma frobeniusComb_smul (a : Ω) (c : Option (ι × ℕ) →₀ Ω) :
    frobeniusComb p w (a • c) = a * frobeniusComb p w c := by
  rw [frobeniusComb, Finsupp.sum_smul_index' (fun _ ↦ zero_mul _), frobeniusComb, Finsupp.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp only [smul_eq_mul, mul_assoc]

lemma valuation_frobeniusMonomial (hw1 : ∀ i, v (w i) = 1) (j : Option (ι × ℕ)) :
    v (frobeniusMonomial p w j) = 1 := by
  cases j with
  | none => exact map_one v
  | some i => rw [frobeniusMonomial, Option.elim_some, map_pow, hw1, one_pow]

lemma valuation_frobeniusComb_le (hw1 : ∀ i, v (w i) = 1) (c : Option (ι × ℕ) →₀ Ω) {γ : Γ₀}
    (hc : ∀ j, v (c j) ≤ γ) : v (frobeniusComb p w c) ≤ γ := by
  refine v.map_sum_le fun j _ ↦ ?_
  rw [map_mul, valuation_frobeniusMonomial p hw1, mul_one]
  exact hc j

lemma valuation_frobeniusComb_lt (hw1 : ∀ i, v (w i) = 1) (c : Option (ι × ℕ) →₀ Ω) {γ : Γ₀}
    (hγ : γ ≠ 0) (hc : ∀ j, v (c j) < γ) : v (frobeniusComb p w c) < γ := by
  refine v.map_sum_lt hγ fun j _ ↦ ?_
  rw [map_mul, valuation_frobeniusMonomial p hw1, mul_one]
  exact hc j


/-- A combination of the monomials is `d₀ + ∑ dⱼ (w j.1) ^ p ^ j.2`. -/
lemma frobeniusComb_eq (c : Option (ι × ℕ) →₀ Ω) :
    frobeniusComb p w c = c none + liftedSum p w c.some := by
  rw [frobeniusComb, Finsupp.sum_option_index _ _ (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _]
  simp [frobeniusMonomial, liftedSum]


lemma frobeniusMonomial_mem (L : Subfield Ω) (hw : ∀ i, w i ∈ L) (j : Option (ι × ℕ)) :
    frobeniusMonomial p w j ∈ L := by
  cases j with
  | none => exact one_mem L
  | some i => exact pow_mem (hw i.1) _

/-- `(a + b) ^ p - a ^ p - b ^ p` is the sum of the middle binomial terms. -/
lemma add_pow_sub_pow_sub_pow_eq (hp : 2 ≤ p) (a b : Ω) :
    (a + b) ^ p - a ^ p - b ^ p = ∑ i ∈ Ioo 0 p, a ^ i * b ^ (p - i) * (p.choose i : Ω) := by
  rw [add_pow]
  have h1 : range (p + 1) = insert p (insert 0 (Ioo 0 p)) := by
    ext i
    simp only [mem_range, mem_insert, mem_Ioo]
    omega
  rw [h1, sum_insert (by simp; omega), sum_insert (by simp)]
  simp only [Nat.choose_self, Nat.choose_zero_right, pow_zero, Nat.sub_self, Nat.sub_zero,
    Nat.cast_one, mul_one, one_mul]
  ring

/-- The middle binomial terms of `(a + b) ^ p` have value at most `v p * μ` when
`v a ^ p, v b ^ p ≤ μ`. -/
lemma valuation_add_pow_sub_pow_sub_pow_le (hp : p.Prime) {a b : Ω} {μ : Γ₀} (ha : v a ^ p ≤ μ)
    (hb : v b ^ p ≤ μ) : v ((a + b) ^ p - a ^ p - b ^ p) ≤ v (p : Ω) * μ := by
  have hδ : max (v a) (v b) ^ p ≤ μ := by
    rcases le_total (v a) (v b) with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  rw [add_pow_sub_pow_sub_pow_eq p hp.two_le]
  refine v.map_sum_le fun i hi ↦ ?_
  rw [mem_Ioo] at hi
  obtain ⟨m, hm⟩ := hp.dvd_choose_self (by omega : i ≠ 0) hi.2
  rw [hm, Nat.cast_mul, map_mul, map_mul, map_mul, map_pow, map_pow, mul_comm]
  calc v (p : Ω) * v (m : Ω) * (v a ^ i * v b ^ (p - i))
      ≤ v (p : Ω) * 1 * (max (v a) (v b) ^ i * max (v a) (v b) ^ (p - i)) :=
        mul_le_mul' (mul_le_mul' le_rfl (Valuation.map_natCast_le_one' m))
          (mul_le_mul' (pow_le_pow_left₀ zero_le (le_max_left _ _) _)
            (pow_le_pow_left₀ zero_le (le_max_right _ _) _))
    _ ≤ v (p : Ω) * μ := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hi.2.le]
        exact mul_le_mul' le_rfl hδ

/-- A `p`-th power of a sum is the sum of the `p`-th powers up to an error of value `≤ v p * μ`,
when all `v (x j) ^ p ≤ μ`. -/
lemma valuation_sum_pow_sub_sum_pow_le {α : Type*} (hp : p.Prime) (s : Finset α) (x : α → Ω)
    {μ : Γ₀} (hx : ∀ j ∈ s, v (x j) ^ p ≤ μ) :
    v (∑ j ∈ s, x j) ^ p ≤ μ ∧
      v ((∑ j ∈ s, x j) ^ p - ∑ j ∈ s, x j ^ p) ≤ v (p : Ω) * μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, map_zero, zero_pow hp.ne_zero, sub_zero]
    exact ⟨zero_le, zero_le⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun j hj ↦ hx j (mem_insert_of_mem hj)
    have hxa := hx a (mem_insert_self a s)
    rw [sum_insert ha, sum_insert ha]
    refine ⟨?_, ?_⟩
    · rcases le_total (v (x a)) (v (∑ j ∈ s, x j)) with h | h
      · exact (pow_le_pow_left₀ zero_le ((v.map_add _ _).trans (max_eq_right h).le) _).trans ih1
      · exact (pow_le_pow_left₀ zero_le ((v.map_add _ _).trans (max_eq_left h).le) _).trans hxa
    · have : (x a + ∑ j ∈ s, x j) ^ p - (x a ^ p + ∑ j ∈ s, x j ^ p) =
          ((x a + ∑ j ∈ s, x j) ^ p - x a ^ p - (∑ j ∈ s, x j) ^ p) +
            ((∑ j ∈ s, x j) ^ p - ∑ j ∈ s, x j ^ p) := by ring
      rw [this]
      exact v.map_add_le (valuation_add_pow_sub_pow_sub_pow_le p hp hxa ih1) ih2

variable (v w) in
/-- `x` is congruent, modulo `{y : v y < v p}`, to a combination of the lifted Frobenius
monomials with coefficients in `S`. -/
def IsFrobeniusApprox (S : Subfield Ω) (x : Ω) : Prop :=
  ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ S) ∧ v (x - frobeniusComb p w e) < v (p : Ω)

namespace IsFrobeniusApprox

variable {p} {S : Subfield Ω}

lemma comb (hvp : 0 < v (p : Ω)) (e : Option (ι × ℕ) →₀ Ω) (he : ∀ k, e k ∈ S) :
    IsFrobeniusApprox v p w S (frobeniusComb p w e) :=
  ⟨e, he, by rwa [sub_self, map_zero]⟩

lemma one (hvp : 0 < v (p : Ω)) : IsFrobeniusApprox v p w S 1 := by
  have h := comb (w := w) (S := S) hvp (Finsupp.single none 1) fun k ↦ by
    rw [Finsupp.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rwa [frobeniusComb_single, one_mul] at h

lemma of_sub_lt {x y : Ω} (hx : IsFrobeniusApprox v p w S x) (h : v (y - x) < v (p : Ω)) :
    IsFrobeniusApprox v p w S y := by
  obtain ⟨e, he, hlt⟩ := hx
  refine ⟨e, he, ?_⟩
  rw [← sub_add_sub_cancel y x]
  exact lt_of_le_of_lt (v.map_add _ _) (max_lt h hlt)

lemma add {x y : Ω} (hx : IsFrobeniusApprox v p w S x) (hy : IsFrobeniusApprox v p w S y) :
    IsFrobeniusApprox v p w S (x + y) := by
  obtain ⟨e, he, hlt⟩ := hx
  obtain ⟨e', he', hlt'⟩ := hy
  refine ⟨e + e', fun k ↦ add_mem (he k) (he' k), ?_⟩
  rw [frobeniusComb_add, add_sub_add_comm]
  exact lt_of_le_of_lt (v.map_add _ _) (max_lt hlt hlt')

lemma mul_left {a x : Ω} (ha : a ∈ S) (hav : v a ≤ 1) (hx : IsFrobeniusApprox v p w S x) :
    IsFrobeniusApprox v p w S (a * x) := by
  obtain ⟨e, he, hlt⟩ := hx
  refine ⟨a • e, fun k ↦ mul_mem ha (he k), ?_⟩
  rw [frobeniusComb_smul, ← mul_sub, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hav) hlt

lemma neg {x : Ω} (hx : IsFrobeniusApprox v p w S x) : IsFrobeniusApprox v p w S (-x) := by
  have h := mul_left (neg_mem (one_mem S)) (by rw [Valuation.map_neg, map_one]) hx
  rwa [neg_one_mul] at h

lemma sub {x y : Ω} (hx : IsFrobeniusApprox v p w S x) (hy : IsFrobeniusApprox v p w S y) :
    IsFrobeniusApprox v p w S (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

lemma sum {α : Type*} (hvp : 0 < v (p : Ω)) (s : Finset α) {x : α → Ω}
    (hx : ∀ j ∈ s, IsFrobeniusApprox v p w S (x j)) :
    IsFrobeniusApprox v p w S (∑ j ∈ s, x j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, ← frobeniusComb_zero p]
    exact comb hvp 0 fun _ ↦ zero_mem _
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (hx a (mem_insert_self a s)).add (ih fun j hj ↦ hx j (mem_insert_of_mem hj))

/-- The approximating combination of an element of value `≤ β` (with `v p ≤ β`) has
coefficients of value `≤ β`. -/
lemma exists_le {K : Subfield Ω} (hS : S ≤ K)
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      ∀ j, v (c j) ≤ v (frobeniusComb p w c)) {x : Ω} (hx : IsFrobeniusApprox v p w S x)
    {β : Γ₀} (hβ : v (p : Ω) ≤ β) (hxβ : v x ≤ β) :
    ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ S) ∧ v (x - frobeniusComb p w e) < v (p : Ω) ∧
      v (frobeniusComb p w e) ≤ β ∧ ∀ k, v (e k) ≤ β := by
  obtain ⟨e, he, hlt⟩ := hx
  have hcomb : v (frobeniusComb p w e) ≤ β := by
    rw [← sub_sub_cancel x (frobeniusComb p w e)]
    exact (v.map_sub _ _).trans (max_le hxβ (hlt.le.trans hβ))
  exact ⟨e, he, hlt, hcomb, fun k ↦ (hval e (fun j ↦ hS (he j)) k).trans hcomb⟩

/-- The approximating combination of an element of value `< β` (with `v p ≤ β`) has
coefficients of value `< β`. -/
lemma exists_lt {K : Subfield Ω} (hS : S ≤ K)
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      ∀ j, v (c j) ≤ v (frobeniusComb p w c)) {x : Ω} (hx : IsFrobeniusApprox v p w S x)
    {β : Γ₀} (hβ : v (p : Ω) ≤ β) (hxβ : v x < β) :
    ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ S) ∧ v (x - frobeniusComb p w e) < v (p : Ω) ∧
      ∀ k, v (e k) < β := by
  obtain ⟨e, he, hlt⟩ := hx
  have hcomb : v (frobeniusComb p w e) < β := by
    rw [← sub_sub_cancel x (frobeniusComb p w e)]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hxβ (hlt.trans_le hβ))
  exact ⟨e, he, hlt, fun k ↦ (hval e (fun j ↦ hS (he j)) k).trans_lt hcomb⟩

/-- The product of two combinations with coefficients of value `≤ 1` is approximated by a
combination (re-expanding the products of monomials with `hprod`). -/
lemma comb_mul (hvp : 0 < v (p : Ω))
    (hprod : ∀ j j', ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ S) ∧
      v (frobeniusMonomial p w j * frobeniusMonomial p w j' - frobeniusComb p w e) <
        v (p : Ω))
    (a b : Option (ι × ℕ) →₀ Ω) (ha : ∀ j, a j ∈ S) (hb : ∀ j, b j ∈ S) (ha1 : ∀ j, v (a j) ≤ 1)
    (hb1 : ∀ j, v (b j) ≤ 1) :
    IsFrobeniusApprox v p w S (frobeniusComb p w a * frobeniusComb p w b) := by
  have h : frobeniusComb p w a * frobeniusComb p w b = ∑ j ∈ a.support, ∑ j' ∈ b.support,
      a j * b j' * (frobeniusMonomial p w j * frobeniusMonomial p w j') := by
    rw [frobeniusComb, frobeniusComb, Finsupp.sum, Finsupp.sum, Finset.sum_mul_sum]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun j' _ ↦ by ring
  rw [h]
  refine sum hvp _ fun j _ ↦ sum hvp _ fun j' _ ↦ mul_left (mul_mem (ha j) (hb j'))
    (by rw [map_mul]; exact mul_le_one' (ha1 j) (hb1 j')) ?_
  obtain ⟨e, he, hlt⟩ := hprod j j'
  exact ⟨e, he, hlt⟩

lemma mul {K : Subfield Ω} (hS : S ≤ K) (hp1 : v (p : Ω) < 1) (hvp : 0 < v (p : Ω))
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      ∀ j, v (c j) ≤ v (frobeniusComb p w c))
    (hprod : ∀ j j', ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ S) ∧
      v (frobeniusMonomial p w j * frobeniusMonomial p w j' - frobeniusComb p w e) <
        v (p : Ω))
    {x y : Ω} (hx : IsFrobeniusApprox v p w S x) (hy : IsFrobeniusApprox v p w S y)
    (hx1 : v x ≤ 1) (hy1 : v y ≤ 1) : IsFrobeniusApprox v p w S (x * y) := by
  obtain ⟨e, he, hlt, -, he1⟩ := hx.exists_le hS hval hp1.le hx1
  obtain ⟨e', he', hlt', hc', he'1⟩ := hy.exists_le hS hval hp1.le hy1
  refine (comb_mul hvp hprod e e' he he' he1 he'1).of_sub_lt ?_
  have h : x * y - frobeniusComb p w e * frobeniusComb p w e' =
      x * (y - frobeniusComb p w e') + (x - frobeniusComb p w e) * frobeniusComb p w e' := by
    ring
  rw [h]
  refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx1) hlt'
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hc') hlt

lemma pow {K : Subfield Ω} (hS : S ≤ K) (hp1 : v (p : Ω) < 1) (hvp : 0 < v (p : Ω))
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      ∀ j, v (c j) ≤ v (frobeniusComb p w c))
    (hprod : ∀ j j', ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ S) ∧
      v (frobeniusMonomial p w j * frobeniusMonomial p w j' - frobeniusComb p w e) <
        v (p : Ω))
    {x : Ω} (hx : IsFrobeniusApprox v p w S x) (hx1 : v x ≤ 1) (n : ℕ) :
    IsFrobeniusApprox v p w S (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact one hvp
  | succ n ih =>
    rw [pow_succ]
    exact mul hS hp1 hvp hval hprod ih hx (by rw [map_pow]; exact pow_le_one' hx1 n) hx1

end IsFrobeniusApprox

/-- **The residual step of stage 1**: if a `p`-th power `y ^ p` of `L₂` is congruent modulo
`{v < v p}` to `1 + ∑ c j m j` with `μ = v (∑ c j m j) ≥ v p`, then the coefficients of the
monomials `w i` (of depth `0`) have value `< μ`. -/
lemma valuation_coeff_some_zero_lt (K L₂ : Subfield Ω) (hp : p.Prime) (hp1 : v (p : Ω) < 1)
    (hp0 : (p : Ω) ≠ 0) (hKL₂ : K ≤ L₂) (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c)
    (hw1 : ∀ i, v (w i) = 1)
    (hres1 : ∀ z ∈ L₂, v z ≤ 1 → ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      (∀ j, v (c j) ≤ 1) → v (z ^ p - frobeniusComb p w c) < 1 →
        ∀ i : ι, v (c (some (i, 0))) < 1)
    (c : Option (ι × ℕ) →₀ Ω) (hcK : ∀ j, c j ∈ K)
    (hcμ : ∀ j, v (c j) ≤ v (frobeniusComb p w c)) (hT1 : v (frobeniusComb p w c) < 1)
    (hTp : v (p : Ω) ≤ v (frobeniusComb p w c)) {y : Ω} (hy : y ∈ L₂)
    (hu1 : v (y ^ p - 1 - frobeniusComb p w c) < v (p : Ω)) (i : ι) :
    v (c (some (i, 0))) < v (frobeniusComb p w c) := by
  have hp2 := hp.two_le
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  set T := frobeniusComb p w c with hTdef
  set μ := v T with hμdef
  set s := y - 1 with hsdef
  set B := ∑ i ∈ Ico 2 p, (p.choose i : Ω) * s ^ i with hBdef
  have hexp : y ^ p - 1 = s ^ p + ((p : Ω) * s + B) := by
    have h := Valuation.one_add_pow_eq p hp2 s
    rw [hsdef, add_sub_cancel] at h
    rw [h]
    ring
  have hvu : v (y ^ p - 1) = μ := by
    have h : y ^ p - 1 = T + (y ^ p - 1 - T) := by ring
    rw [h, v.map_add_eq_of_lt_left (hu1.trans_le hTp)]
  set σ := v s with hσdef
  have hBle : ∀ i ∈ Ico 2 p, v ((p.choose i : Ω) * s ^ i) ≤ v (p : Ω) * σ ^ i :=
    fun i hi ↦ Valuation.valuation_choose_mul_pow_le p hp s hi
  -- `σ < 1`
  have hσ1 : σ < 1 := by
    by_contra h
    rw [not_lt] at h
    have hσpos : 0 < σ ^ (p - 1) := pow_pos (zero_lt_one.trans_le h) _
    have hbig : v (p : Ω) * σ ^ (p - 1) < σ ^ p :=
      calc v (p : Ω) * σ ^ (p - 1) < σ ^ (p - 1) := mul_lt_of_lt_one_left hσpos hp1
        _ ≤ σ ^ p := pow_le_pow_right₀ h (by omega)
    have hrest : v ((p : Ω) * s + B) < σ ^ p := by
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_mul' le_rfl (le_self_pow₀ h (by omega))) hbig
      · refine lt_of_le_of_lt (v.map_sum_le fun i hi ↦ (hBle i hi).trans ?_) hbig
        exact mul_le_mul' le_rfl (pow_le_pow_right₀ h (by rw [mem_Ico] at hi; omega))
    have h' := hvu
    rw [hexp, v.map_add_eq_of_lt_left (by rwa [map_pow]), map_pow] at h'
    exact not_le.2 hT1 (h' ▸ one_le_pow₀ h)
  have hrest : v ((p : Ω) * s + B) ≤ v (p : Ω) * σ := by
    refine v.map_add_le (by rw [map_mul]) (v.map_sum_le fun i hi ↦ (hBle i hi).trans ?_)
    exact mul_le_mul' le_rfl (pow_le_of_le_one zero_le hσ1.le (by rw [mem_Ico] at hi; omega))
  have hsm : v (p : Ω) < σ ^ (p - 1) := by
    by_contra hsm
    rw [not_lt] at hsm
    have hle : μ ≤ v (p : Ω) * σ := by
      rw [← hvu, hexp]
      refine v.map_add_le ?_ hrest
      rw [map_pow, ← pow_sub_one_mul (by omega : p ≠ 0)]
      exact mul_le_mul' hsm le_rfl
    exact not_lt.2 hTp (hle.trans_lt (mul_lt_of_lt_one_right hvp hσ1))
  have hσ0 : σ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hsm
    exact not_lt.2 zero_le hsm
  have hlt : v (p : Ω) * σ < σ ^ p := by
    rw [← pow_sub_one_mul (by omega : p ≠ 0)]
    exact mul_lt_mul_of_pos_right hsm (zero_lt_iff.2 hσ0)
  have hμσ : μ = σ ^ p := by
    rw [← hvu, hexp, v.map_add_eq_of_lt_left (by rw [map_pow]; exact hrest.trans_lt hlt),
      map_pow]
  -- a leading coefficient
  obtain ⟨j₀, hj₀⟩ : ∃ j, v (c j) = μ := by
    by_contra h
    push Not at h
    exact lt_irrefl _ (valuation_frobeniusComb_lt p hw1 c (hvp.trans_le hTp).ne'
      fun j ↦ lt_of_le_of_ne (hcμ j) (h j))
  obtain ⟨γ, hγK, hγ⟩ := hroot (c j₀) (hcK j₀)
  have hvγ : v γ = σ := by
    refine @pow_left_injective Γ₀ inferInstance inferInstance p hp.ne_zero _ _ ?_
    simp only
    rw [← map_pow, hγ, hj₀, hμσ]
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h, map_zero] at hvγ
    exact hσ0 hvγ.symm
  have hγp : v (γ ^ p) = μ := by rw [map_pow, hvγ, hμσ]
  have hμ0 : μ ≠ 0 := by
    rw [hμσ]
    exact pow_ne_zero _ hσ0
  have hzL : s / γ ∈ L₂ := div_mem (sub_mem hy (one_mem _)) (hKL₂ hγK)
  have hz1 : v (s / γ) ≤ 1 := by rw [map_div₀, hvγ, div_self hσ0]
  have hident : (s / γ) ^ p - frobeniusComb p w ((γ ^ p)⁻¹ • c) =
      ((y ^ p - 1 - T) - ((p : Ω) * s + B)) / γ ^ p := by
    rw [frobeniusComb_smul, div_pow, ← hTdef]
    field_simp
    linear_combination -hexp
  have hlt1 : v ((s / γ) ^ p - frobeniusComb p w ((γ ^ p)⁻¹ • c)) < 1 := by
    rw [hident, map_div₀, hγp, div_lt_one₀ (zero_lt_iff.2 hμ0)]
    refine lt_of_le_of_lt (v.map_sub _ _) (max_lt (hu1.trans_le hTp) ?_)
    rw [hμσ]
    exact hrest.trans_lt hlt
  have h := hres1 _ hzL hz1 ((γ ^ p)⁻¹ • c)
    (fun j ↦ mul_mem (inv_mem (pow_mem hγK _)) (hcK j))
    (fun j ↦ by
      rw [Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, hγp,
        inv_mul_le_one₀ (zero_lt_iff.2 hμ0)]
      exact hcμ j) hlt1 i
  rwa [Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, hγp,
    inv_mul_lt_one₀ (zero_lt_iff.2 hμ0)] at h

/-- **One step of stage 1**: if `u = y ^ p` is congruent modulo `{v < v p}` to `1 + ∑ c j m j`
with `μ = v (∑ c j m j) ≥ v p`, then dividing `u` by the `p`-th power of an explicit `1 + c₁ ∈ L₁`
yields an element congruent to `1 + ∑ c' j m j` with all `v (c' j) < μ`. -/
lemma kummer_stage1_step (K L₁ L₂ Kst : Subfield Ω)
    (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hKL₁ : K ≤ L₁) (hL : L₁ ≤ L₂) (hKst : Kst ≤ K)
    (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c)
    (hw : ∀ i, w i ∈ L₁) (hw1 : ∀ i, v (w i) = 1)
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      ∀ j, v (c j) ≤ v (frobeniusComb p w c))
    (hprod : ∀ j j', ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ Kst) ∧
      v (frobeniusMonomial p w j * frobeniusMonomial p w j' - frobeniusComb p w e) < v (p : Ω))
    (hres1 : ∀ z ∈ L₂, v z ≤ 1 → ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      (∀ j, v (c j) ≤ 1) → v (z ^ p - frobeniusComb p w c) < 1 →
        ∀ i : ι, v (c (some (i, 0))) < 1)
    {u : Ω} (c : Option (ι × ℕ) →₀ Ω) (hc : ∀ j, c j ∈ Kst)
    (hc1 : ∀ j, v (c j) < 1) (hu1 : v (u - 1 - frobeniusComb p w c) < v (p : Ω))
    {y : Ω} (hy : y ∈ L₂) (hyu : y ^ p = u) (hμ : v (p : Ω) ≤ v (frobeniusComb p w c))
    (M : ℕ) (hM : v (frobeniusComb p w c) ^ M < v (p : Ω)) :
    ∃ g ∈ L₁, g ≠ 0 ∧ ∃ c' : Option (ι × ℕ) →₀ Ω, (∀ j, c' j ∈ Kst) ∧
      (∀ j, v (c' j) < v (frobeniusComb p w c)) ∧
      v (u / g ^ p - 1 - frobeniusComb p w c') < v (p : Ω) := by
  classical
  classical
  have hp2 := hp.two_le
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  set T := frobeniusComb p w c with hTdef
  set μ := v T with hμdef
  have hμ0 : μ ≠ 0 := (hvp.trans_le hμ).ne'
  have hT1 : μ < 1 := valuation_frobeniusComb_lt p hw1 c one_ne_zero hc1
  have hcμ : ∀ j, v (c j) ≤ μ := hval c fun j ↦ hKst (hc j)
  have hlead0 (i : ι) : v (c (some (i, 0))) < μ :=
    valuation_coeff_some_zero_lt p K L₂ hp hp1 hp0 (hKL₁.trans hL) hroot hw1 hres1 c
      (fun j ↦ hKst (hc j)) hcμ hT1 hμ hy (by rwa [hyu]) i
  choose r hrK hrp using fun j ↦ hroot (c j) (hKst (hc j))
  -- the monomial `m j = m (down j) ^ p` for the leading indices `j`
  set down : Option (ι × ℕ) → Option (ι × ℕ) := Option.map fun x ↦ (x.1, x.2 - 1)
    with hdowndef
  have hdown (j : Option (ι × ℕ)) (hj : v (c j) = μ) :
      frobeniusMonomial p w (down j) ^ p = frobeniusMonomial p w j := by
    rcases j with _ | ⟨i, _ | n⟩
    · simp [hdowndef, frobeniusMonomial]
    · exact absurd hj (hlead0 i).ne
    · simp [hdowndef, frobeniusMonomial, ← pow_mul, pow_succ]
  set x : Option (ι × ℕ) → Ω := fun j ↦
    if v (c j) = μ then r j * frobeniusMonomial p w (down j) else 0 with hxdef
  set c₁ := ∑ j ∈ c.support, x j with hc₁def
  have hxp (j : Option (ι × ℕ)) :
      x j ^ p = if v (c j) = μ then c j * frobeniusMonomial p w j else 0 := by
    simp only [hxdef]
    split_ifs with h
    · rw [mul_pow, hrp, hdown j h]
    · exact zero_pow hp.ne_zero
  have hxv (j : Option (ι × ℕ)) (_ : j ∈ c.support) : v (x j) ^ p ≤ μ := by
    rw [← map_pow, hxp]
    split_ifs with h
    · rw [map_mul, valuation_frobeniusMonomial p hw1, mul_one, h]
    · rw [map_zero]
      exact zero_le
  set lead := c.filter fun j ↦ v (c j) = μ with hleaddef
  have hleadK (j : Option (ι × ℕ)) : lead j ∈ Kst := by
    rw [hleaddef, Finsupp.filter_apply]
    split_ifs
    exacts [hc j, zero_mem _]
  have hlead : frobeniusComb p w lead = ∑ j ∈ c.support, x j ^ p := by
    rw [frobeniusComb, Finsupp.sum_of_support_subset lead (s := c.support)
      (by rw [hleaddef, Finsupp.support_filter]; exact filter_subset _ _)
      (fun j a ↦ a * frobeniusMonomial p w j) fun _ _ ↦ zero_mul _]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [hleaddef, Finsupp.filter_apply, hxp]
    split_ifs <;> simp
  obtain ⟨hc₁μ, hc₁lead⟩ := valuation_sum_pow_sub_sum_pow_le p hp c.support x hxv
  rw [← hc₁def, ← hlead] at hc₁lead
  rw [← hc₁def] at hc₁μ
  have hc₁L : c₁ ∈ L₁ := sum_mem fun j _ ↦ by
    simp only [hxdef]
    split_ifs
    exacts [mul_mem (hKL₁ (hrK j)) (frobeniusMonomial_mem p L₁ hw _), zero_mem _]
  have hc₁1 : v c₁ < 1 := by
    by_contra h
    rw [not_lt] at h
    exact not_lt.2 (one_le_pow₀ h) (hc₁μ.trans_lt hT1)
  have hE : v (c₁ ^ p - frobeniusComb p w lead) < v (p : Ω) :=
    hc₁lead.trans_lt (mul_lt_of_lt_one_right hvp hT1)
  have hrest : v (T - frobeniusComb p w lead) < μ := by
    have h : T - frobeniusComb p w lead = frobeniusComb p w (c - lead) := by
      rw [hTdef, sub_eq_iff_eq_add, ← frobeniusComb_add, sub_add_cancel]
    rw [h]
    refine valuation_frobeniusComb_lt p hw1 _ hμ0 fun j ↦ ?_
    rw [Finsupp.coe_sub, Pi.sub_apply, hleaddef, Finsupp.filter_apply]
    split_ifs with h
    · rw [sub_self, map_zero]
      exact zero_lt_iff.2 hμ0
    · rw [sub_zero]
      exact lt_of_le_of_ne (hcμ j) h
  -- `D = (1 + c₁) ^ p`
  set D := (1 + c₁) ^ p with hDdef
  have hD1 : v D = 1 := by rw [hDdef, map_pow, valuation_one_add_eq_one hc₁1, one_pow]
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, map_zero] at hD1
    exact zero_ne_one hD1
  set B := ∑ i ∈ Ico 2 p, (p.choose i : Ω) * c₁ ^ i with hBdef
  have hpB : v ((p : Ω) * c₁ + B) < v (p : Ω) := by
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact mul_lt_of_lt_one_right hvp hc₁1
    · refine v.map_sum_lt hvp.ne' fun i hi ↦
        (Valuation.valuation_choose_mul_pow_le p hp c₁ hi).trans_lt
          (mul_lt_of_lt_one_right hvp (pow_lt_one₀ zero_le hc₁1 ?_))
      rw [mem_Ico] at hi
      omega
  have hDlead : v (D - 1 - frobeniusComb p w lead) < v (p : Ω) := by
    have h : D - 1 - frobeniusComb p w lead =
        (c₁ ^ p - frobeniusComb p w lead) + ((p : Ω) * c₁ + B) := by
      rw [hDdef, Valuation.one_add_pow_eq p hp2 c₁]
      ring
    rw [h]
    exact lt_of_le_of_lt (v.map_add _ _) (max_lt hE hpB)
  have huD : u - D = (u - 1 - T) + (T - frobeniusComb p w lead) -
      (D - 1 - frobeniusComb p w lead) := by ring
  have huDμ : v (u - D) < μ := by
    rw [huD]
    refine lt_of_le_of_lt (v.map_sub _ _) (max_lt (lt_of_le_of_lt (v.map_add _ _)
      (max_lt (hu1.trans_le hμ) hrest)) (hDlead.trans_le hμ))
  have hleadμ : v (frobeniusComb p w lead) ≤ μ := by
    refine valuation_frobeniusComb_le p hw1 lead fun j ↦ ?_
    rw [hleaddef, Finsupp.filter_apply]
    split_ifs
    · exact hcμ j
    · rw [map_zero]
      exact zero_le
  -- approximations by combinations
  have hA_uD : IsFrobeniusApprox v p w Kst (u - D) := by
    refine ((IsFrobeniusApprox.comb hvp c hc).sub
      (IsFrobeniusApprox.comb hvp lead hleadK)).of_sub_lt ?_
    have h : u - D - (T - frobeniusComb p w lead) =
        (u - 1 - T) - (D - 1 - frobeniusComb p w lead) := by ring
    rw [h]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hu1 hDlead)
  have hA_z : IsFrobeniusApprox v p w Kst (1 - D) := by
    have h := ((IsFrobeniusApprox.comb hvp lead hleadK).of_sub_lt hDlead).neg
    rwa [neg_sub] at h
  have hz : v (1 - D) ≤ μ := by
    have h : 1 - D = -(frobeniusComb p w lead + (D - 1 - frobeniusComb p w lead)) := by ring
    rw [h, Valuation.map_neg]
    exact v.map_add_le hleadμ (hDlead.le.trans hμ)
  have hgeom : D⁻¹ - ∑ k ∈ range M, (1 - D) ^ k = (1 - D) ^ M / D := by
    have h := geom_sum_mul (1 - D) M
    rw [sub_sub_cancel_left] at h
    rw [eq_div_iff hD0, sub_mul, inv_mul_cancel₀ hD0]
    linear_combination h
  have hA_Dinv : IsFrobeniusApprox v p w Kst D⁻¹ := by
    refine (IsFrobeniusApprox.sum hvp (range M) (x := fun k ↦ (1 - D) ^ k) fun k _ ↦
      hA_z.pow hKst hp1 hvp hval hprod (hz.trans hT1.le) k).of_sub_lt ?_
    rw [hgeom, map_div₀, hD1, div_one, map_pow]
    exact (pow_le_pow_left₀ zero_le hz M).trans_lt hM
  have hA : IsFrobeniusApprox v p w Kst ((u - D) * D⁻¹) :=
    hA_uD.mul hKst hp1 hvp hval hprod hA_Dinv (huDμ.le.trans hT1.le)
      (by rw [map_inv₀, hD1, inv_one])
  have hval' : v ((u - D) * D⁻¹) < μ := by rwa [map_mul, map_inv₀, hD1, inv_one, mul_one]
  obtain ⟨c', hc', hc'p, hc'μ⟩ := hA.exists_lt hKst hval hμ hval'
  have hD1c : 1 + c₁ ≠ 0 := by
    intro h
    rw [hDdef, h, zero_pow hp.ne_zero] at hD0
    exact hD0 rfl
  refine ⟨1 + c₁, add_mem (one_mem _) hc₁L, hD1c, c', hc', hc'μ, ?_⟩
  have h : u / (1 + c₁) ^ p - 1 = (u - D) * D⁻¹ := by
    rw [← hDdef]
    field_simp
  rwa [h]
/-- **Stage 1 of the Kummer normal form.** -/
theorem exists_valuation_div_pow_sub_one_lt (K L₁ L₂ Kst : Subfield Ω)
    (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hKL₁ : K ≤ L₁) (hL : L₁ ≤ L₂) (hKst : Kst ≤ K)
    (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c)
    (hw : ∀ i, w i ∈ L₁) (hw1 : ∀ i, v (w i) = 1)
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      ∀ j, v (c j) ≤ v (frobeniusComb p w c))
    (γ : Γ₀) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdisc : ∀ c ∈ Kst, c ≠ 0 → ∃ n : ℤ, v c = γ ^ n) (N : ℕ) (hN : γ ^ N < v (p : Ω))
    (hprod : ∀ j j', ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ Kst) ∧
      v (frobeniusMonomial p w j * frobeniusMonomial p w j' - frobeniusComb p w e) < v (p : Ω))
    (hres1 : ∀ z ∈ L₂, v z ≤ 1 → ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      (∀ j, v (c j) ≤ 1) → v (z ^ p - frobeniusComb p w c) < 1 →
        ∀ i : ι, v (c (some (i, 0))) < 1)
    {u : Ω} (hu : u ∈ L₁) (c : Option (ι × ℕ) →₀ Ω) (hc : ∀ j, c j ∈ Kst)
    (hc1 : ∀ j, v (c j) < 1) (hu1 : v (u - 1 - frobeniusComb p w c) < v (p : Ω))
    (h₂ : ∃ y ∈ L₂, y ^ p = u) :
    ∃ g ∈ L₁, g ≠ 0 ∧ v (u / g ^ p - 1) < v (p : Ω) := by
  classical
  classical
  obtain ⟨y, hyL, hyu⟩ := h₂
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  -- the case `v (∑ c j m j) < v p` is immediate
  have hdone {u : Ω} (c : Option (ι × ℕ) →₀ Ω) (hu1 : v (u - 1 - frobeniusComb p w c) < v (p : Ω))
      (hT : v (frobeniusComb p w c) < v (p : Ω)) :
      ∃ g ∈ L₁, g ≠ 0 ∧ v (u / g ^ p - 1) < v (p : Ω) := by
    refine ⟨1, one_mem _, one_ne_zero, ?_⟩
    rw [one_pow, div_one, ← sub_add_cancel (u - 1) (frobeniusComb p w c)]
    exact lt_of_le_of_lt (v.map_add _ _) (max_lt hu1 hT)
  suffices H : ∀ k : ℕ, ∀ u ∈ L₁, ∀ y ∈ L₂, y ^ p = u → ∀ c : Option (ι × ℕ) →₀ Ω,
      (∀ j, c j ∈ Kst) → (∀ j, v (c j) < γ ^ (N - k)) →
      v (u - 1 - frobeniusComb p w c) < v (p : Ω) →
        ∃ g ∈ L₁, g ≠ 0 ∧ v (u / g ^ p - 1) < v (p : Ω) from
    H N u hu y hyL hyu c hc (by rwa [Nat.sub_self, pow_zero]) hu1
  intro k
  induction k with
  | zero =>
    intro u _ y _ _ c _ hcN hu1
    exact hdone c hu1 (valuation_frobeniusComb_lt p hw1 c (pow_pos hγ0 N).ne' hcN |>.trans hN)
  | succ k ih =>
    intro u hu y hyL hyu c hc hck hu1
    by_cases hT : v (frobeniusComb p w c) < v (p : Ω)
    · exact hdone c hu1 hT
    rw [not_lt] at hT
    have hc1 (j : Option (ι × ℕ)) : v (c j) < 1 :=
      (hck j).trans_le (pow_le_one₀ zero_le hγ1.le)
    obtain ⟨j₀, hj₀⟩ : ∃ j, v (c j) = v (frobeniusComb p w c) := by
      by_contra h
      push Not at h
      exact lt_irrefl _ (valuation_frobeniusComb_lt p hw1 c (hvp.trans_le hT).ne'
        fun j ↦ lt_of_le_of_ne (hval c (fun j ↦ hKst (hc j)) j) (h j))
    have hj₀0 : c j₀ ≠ 0 := by
      intro h
      rw [h, map_zero] at hj₀
      exact not_le.2 hvp (hT.trans hj₀.symm.le)
    -- the value `μ` of the combination is a power `γ ^ n`, `n ≥ 1`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, v (c j₀) = γ ^ n := by
      obtain ⟨m, hm⟩ := hdisc _ (hc j₀) hj₀0
      rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
      · exact ⟨n, by rw [hm, zpow_natCast]⟩
      · refine ⟨0, ?_⟩
        rcases n.eq_zero_or_pos with rfl | hn
        · rw [hm, Nat.cast_zero, neg_zero, zpow_zero, pow_zero]
        · exfalso
          have h1 : v (c j₀) * γ ^ n = 1 := by
            rw [hm, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_pos hγ0 n).ne']
          have h2 : v (c j₀) * γ ^ n < 1 :=
            lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one₀ zero_le hγ1.le)) (hc1 j₀)
          exact h2.ne h1
    have hn1 : 1 ≤ n := by
      by_contra h
      have h0 : n = 0 := by omega
      rw [h0, pow_zero] at hn
      exact (hc1 j₀).ne hn
    have hM : v (frobeniusComb p w c) ^ N < v (p : Ω) := by
      rw [← hj₀, hn, ← pow_mul]
      exact (pow_le_pow_right_of_le_one' hγ1.le (Nat.le_mul_of_pos_left N hn1)).trans_lt hN
    obtain ⟨g₁, hg₁L, hg₁0, c', hc', hc'μ, hu'⟩ := kummer_stage1_step p K L₁ L₂ Kst hp hp1 hp0
      hKL₁ hL hKst hroot hw hw1 hval hprod hres1 c hc hc1 hu1 hyL hyu hT N hM
    have hnk : N - k ≤ n := by
      have h := hck j₀
      rw [hn, pow_lt_pow_iff_right_of_lt_one₀ hγ0 hγ1] at h
      omega
    have hc'k (j : Option (ι × ℕ)) : v (c' j) < γ ^ (N - k) := by
      refine (hc'μ j).trans_le ?_
      rw [← hj₀, hn]
      exact pow_le_pow_right_of_le_one' hγ1.le hnk
    obtain ⟨g', hg'L, hg'0, hg'⟩ := ih (u / g₁ ^ p) (div_mem hu (pow_mem hg₁L _)) (y / g₁)
      (div_mem hyL (hL hg₁L)) (by rw [div_pow, hyu]) c' hc' hc'k hu'
    refine ⟨g₁ * g', mul_mem hg₁L hg'L, mul_ne_zero hg₁0 hg'0, ?_⟩
    rwa [mul_pow, ← div_div]


/-- The combination `∑ i ∈ s, c i (w i)` of depth-zero monomials as a `frobeniusComb`. -/
lemma frobeniusComb_sum_single (s : Finset ι) (c : ι → Ω) :
    frobeniusComb p w (∑ i ∈ s, Finsupp.single (some (i, 0)) (c i)) = ∑ i ∈ s, c i * w i := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, frobeniusComb_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, frobeniusComb_add, ih, frobeniusComb_single]
    simp [frobeniusMonomial]

lemma sum_single_some_apply (s : Finset ι) (c : ι → Ω) {i : ι} (hi : i ∈ s) :
    (∑ i ∈ s, Finsupp.single (some (i, 0)) (c i)) (some (i, 0)) = c i := by
  classical
  rw [Finsupp.finsetSum_apply, sum_eq_single i (fun b _ hb ↦ by simp [hb]) (fun h ↦ absurd hi h),
    Finsupp.single_eq_same]

lemma sum_single_some_mem (S : Subfield Ω) (s : Finset ι) {c : ι → Ω}
    (hc : ∀ i ∈ s, c i ∈ S) (j : Option (ι × ℕ)) :
    (∑ i ∈ s, Finsupp.single (some (i, 0)) (c i)) j ∈ S := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine sum_mem fun i hi ↦ ?_
  rw [Finsupp.single_apply]
  split_ifs
  exacts [hc i hi, zero_mem _]
/-- **Kummer normal form**: a `1`-unit of `L₁` (approximated by a combination of lifted
Frobenius monomials with coefficients in a discrete subfield `K*`) which is a `p`-th power in `L₂`
is a `p`-th power in `L₁`. -/
theorem exists_pow_eq_of_kummer (K L₁c L₁ L₂ Kst : Subfield Ω)
    (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hKL₁ : K ≤ L₁c) (hL₁c : L₁c ≤ L₁) (hL : L₁ ≤ L₂) (hKst : Kst ≤ K)
    (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c)
    (hw : ∀ i, w i ∈ L₁c) (hw1 : ∀ i, v (w i) = 1)
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      ∀ j, v (c j) ≤ v (frobeniusComb p w c))
    (γ : Γ₀) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdisc : ∀ c ∈ Kst, c ≠ 0 → ∃ n : ℤ, v c = γ ^ n) (N : ℕ) (hN : γ ^ N < v (p : Ω))
    (hprod : ∀ j j', ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ Kst) ∧
      v (frobeniusMonomial p w j * frobeniusMonomial p w j' - frobeniusComb p w e) < v (p : Ω))
    (hres1 : ∀ z ∈ L₂, v z ≤ 1 → ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      (∀ j, v (c j) ≤ 1) → v (z ^ p - frobeniusComb p w c) < 1 →
        ∀ i : ι, v (c (some (i, 0))) < 1)
    (hhens : ∀ x ∈ L₁, v.IsKummerNegligible p x → ∃ y ∈ L₁, y ^ p = 1 + x)
    (hexp : ∀ y ∈ L₁c, ∃ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) ∧
      v.IsKummerNegligible p (y - frobeniusComb p w c))
    {u : Ω} (hu : u ∈ L₁c) (c : Option (ι × ℕ) →₀ Ω) (hc : ∀ j, c j ∈ Kst)
    (hc1 : ∀ j, v (c j) < 1) (hu1 : v (u - 1 - frobeniusComb p w c) < v (p : Ω))
    (h₂ : ∃ y ∈ L₂, y ^ p = u) :
    ∃ y ∈ L₁, y ^ p = u := by
  classical
  classical
  have hp2 := hp.two_le
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  obtain ⟨g, hgL, hg0, hgv⟩ := exists_valuation_div_pow_sub_one_lt p K L₁c L₂ Kst hp hp1 hp0
    hKL₁ (hL₁c.trans hL) hKst hroot hw hw1 hval γ hγ0 hγ1 hdisc N hN hprod hres1 hu c hc hc1 hu1 h₂
  set t := u / g ^ p - 1 with htdef
  have htL : t ∈ L₁c := sub_mem (div_mem hu (pow_mem hgL _)) (one_mem _)
  obtain ⟨c', hc'K, hc'n⟩ := hexp t htL
  -- the coefficients of `c'` have value `< v p`
  have hneg_lt : ∀ x : Ω, v.IsKummerNegligible p x → v x < v (p : Ω) := by
    intro x hx
    by_contra h
    rw [not_lt] at h
    have h1 : v (p : Ω) ^ (p - 1) ≤ v x ^ (p - 1) := pow_le_pow_left₀ zero_le h _
    have h2 : v (p : Ω) ^ p < v (p : Ω) ^ (p - 1) :=
      pow_lt_pow_right_of_lt_one₀ hvp hp1 (by omega)
    exact (not_le.2 (h2.trans_le h1)) hx
  have hcomb : v (frobeniusComb p w c') < v (p : Ω) := by
    have : frobeniusComb p w c' = t - (t - frobeniusComb p w c') := by ring
    rw [this]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hgv (hneg_lt _ hc'n))
  have hc'v : ∀ j, v (c' j) < v (p : Ω) := fun j ↦ (hval c' hc'K j).trans_lt hcomb
  -- stage 2
  have hn : v.IsKummerNegligible p (t - frobeniusComb p w c') := hc'n
  set T' := frobeniusComb p w c' with hT'def
  have h1T : v (1 + T') = 1 := valuation_one_add_eq_one (hcomb.trans hp1)
  have h1T0 : 1 + T' ≠ 0 := by
    intro h
    rw [h, map_zero] at h1T
    exact zero_ne_one h1T
  have hnn : v.IsKummerNegligible p ((t - T') / (1 + T')) :=
    hn.of_le (by rw [map_div₀, h1T, div_one])
  have hT'L : T' ∈ L₁c :=
    sum_mem fun j _ ↦ mul_mem (hKL₁ (hc'K j)) (frobeniusMonomial_mem p L₁c hw j)
  have hnL : (t - T') / (1 + T') ∈ L₁c := div_mem (sub_mem htL hT'L) (add_mem (one_mem _) hT'L)
  have hfac : u / g ^ p = (1 + c' none + liftedSum p w c'.some) * (1 + (t - T') / (1 + T')) := by
    rw [add_assoc, ← frobeniusComb_eq, ← hT'def, htdef]
    field_simp
    ring
  -- the hypotheses of stage 2 in terms of finite sums
  have hval' (s : Finset ι) (c₀ : ι → Ω) (hc₀ : ∀ i ∈ s, c₀ i ∈ K) (i : ι) (hi : i ∈ s) :
      v (c₀ i) ≤ v (∑ j ∈ s, c₀ j * w j) := by
    have h := hval _ (sum_single_some_mem K s hc₀) (some (i, 0))
    rwa [sum_single_some_apply s c₀ hi, frobeniusComb_sum_single] at h
  have hres' (z : Ω) (hz : z ∈ L₂) (hz1 : v z ≤ 1) (s : Finset ι) (c₀ : ι → Ω)
      (hc₀ : ∀ i ∈ s, c₀ i ∈ K) (hc₀1 : ∀ i ∈ s, v (c₀ i) ≤ 1)
      (hlt : v (z ^ p - ∑ i ∈ s, c₀ i * w i) < 1) (i : ι) (hi : i ∈ s) : v (c₀ i) < 1 := by
    have h := hres1 z hz hz1 _ (sum_single_some_mem K s hc₀) (fun j ↦ by
      rw [Finsupp.finsetSum_apply]
      refine v.map_sum_le fun i hi ↦ ?_
      rw [Finsupp.single_apply]
      split_ifs
      · exact hc₀1 i hi
      · rw [map_zero]
        exact zero_le) (by rwa [frobeniusComb_sum_single]) i
    rwa [sum_single_some_apply s c₀ hi] at h
  obtain ⟨y, hyL, hyu⟩ := h₂
  obtain ⟨y', hy'L, hy'⟩ := kummer_stage2 K L₁ L₂ hp hp1 hp0 (hKL₁.trans hL₁c) hL hroot
    (fun i ↦ hL₁c (hw i)) hw1 hval' hhens
    hres' c'.some (fun j ↦ hc'K _) (fun j ↦ hc'v _) (hc'K none) (hc'v none) (hL₁c hnL) hnn
    ⟨y / g, div_mem hyL (hL (hL₁c hgL)), by rw [div_pow, hyu, hfac]⟩
  refine ⟨g * y', mul_mem (hL₁c hgL) hy'L, ?_⟩
  rw [mul_pow, hy', ← hfac]
  field_simp
