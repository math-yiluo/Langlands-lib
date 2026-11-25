/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.KummerNormalFormStageOne
import Mathlib.Tactic.FieldSimp

/-!

# Kummer normal forms: general elements

We extend `exists_pow_eq_of_kummer` from `1`-units to arbitrary elements `α ∈ L₁` which are
approximated by combinations of the lifted Frobenius monomials with coefficients in the discrete
subfield `K*`: if `α` is a `p`-th power in `L₂`, then it is a `p`-th power in `L₁`
(`exists_pow_eq_of_kummer_of_approx`).

The element `α` is first replaced by a combination `E` of the monomials (up to a negligible
factor, handled by Hensel's lemma `hhens`), then `E` is normalized to value `1`. The normalized
combination is divided by the `p`-th power of an explicit unit `g` of the ring `A` (lifting a
`p`-th root of its residue), which yields a `1`-unit to which `exists_pow_eq_of_kummer` applies.

-/

@[expose] public section

open Finset

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation Ω Γ₀} {p : ℕ} {ι : Type*}

variable (p) {w : ι → Ω}

lemma frobeniusMonomial_mem_subring (A : Subring Ω) (hw : ∀ i, w i ∈ A) (j : Option (ι × ℕ)) :
    frobeniusMonomial p w j ∈ A := by
  cases j with
  | none => exact one_mem A
  | some i => exact pow_mem (hw i.1) _

/-- **Kummer normal form for combinations of value `1`**: a combination of the lifted Frobenius
monomials with coefficients in `K*` of value `≤ 1`, of value `1`, which is a `p`-th power in `L₂`,
is a `p`-th power in `L₁`. -/
theorem exists_pow_eq_frobeniusComb_of_kummer (K L₁ L₂ Kst : Subfield Ω)
    (A : Subring Ω) (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hKL₁ : K ≤ L₁) (hL : L₁ ≤ L₂) (hKst : Kst ≤ K) (hAL₁ : ∀ y ∈ A, y ∈ L₁)
    (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c)
    (hw : ∀ i, w i ∈ A) (hw1 : ∀ i, v (w i) = 1)
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) → ∀ j, v (c j) ≤ v (frobeniusComb p w c))
    (γ : Γ₀) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdisc : ∀ c ∈ Kst, c ≠ 0 → ∃ n : ℤ, v c = γ ^ n)
    (hγN : ∀ t ∈ L₁, t ≠ 0 → ∃ N : ℕ, γ ^ N < v t)
    (hAapprox : ∀ y ∈ A, ∀ t ∈ L₁, t ≠ 0 → ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ Kst) ∧
      v (y - frobeniusComb p w e) < v t)
    (hAinv : ∀ y ∈ A, v y = 1 → y⁻¹ ∈ A) (hKstA : ∀ c ∈ Kst, v c ≤ 1 → c ∈ A)
    (hKstroot : ∀ c ∈ Kst, v c ≤ 1 → ∃ d ∈ Kst, v (d ^ p - c) < 1)
    (hexp : ∀ y ∈ Subfield.closure (K ∪ A : Set Ω), ∀ t ∈ L₁, t ≠ 0 →
      ∃ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) ∧ v (y - frobeniusComb p w c) < v t)
    (hres1 : ∀ z ∈ L₂, v z ≤ 1 → ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      (∀ j, v (c j) ≤ 1) → v (z ^ p - frobeniusComb p w c) < 1 →
        ∀ i : ι, v (c (some (i, 0))) < 1)
    (hhens : ∀ x ∈ L₁, v.IsKummerNegligible p x → ∃ y ∈ L₁, y ^ p = 1 + x)
    (c : Option (ι × ℕ) →₀ Ω) (hc : ∀ j, c j ∈ Kst) (hc1 : ∀ j, v (c j) ≤ 1)
    (hE1 : v (frobeniusComb p w c) = 1) {z : Ω} (hz : z ∈ L₂)
    (hzp : z ^ p = frobeniusComb p w c) :
    ∃ y ∈ L₁, y ^ p = frobeniusComb p w c := by
  classical
  classical
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  have hpL : (p : Ω) ∈ L₁ := natCast_mem L₁ p
  set E := frobeniusComb p w c with hEdef
  have hz1 : v z = 1 := by
    rw [← pow_eq_one_iff_left hp.ne_zero, ← map_pow, hzp, hE1]
  have hlev0 : ∀ i, v (c (some (i, 0))) < 1 :=
    hres1 z hz hz1.le c (fun j ↦ hKst (hc j)) hc1
      (by simp [hzp, hEdef])
  choose d hdK hdp using fun j ↦ hKstroot (c j) (hc j) (hc1 j)
  have hd1 (j : Option (ι × ℕ)) : v (d j) ^ p ≤ 1 := by
    rw [← map_pow, ← sub_add_cancel (d j ^ p) (c j)]
    exact v.map_add_le (hdp j).le (hc1 j)
  have hd1' (j : Option (ι × ℕ)) : v (d j) ≤ 1 := (pow_le_one_iff hp.ne_zero).mp (hd1 j)
  set down : Option (ι × ℕ) → Option (ι × ℕ) := Option.map fun x ↦ (x.1, x.2 - 1)
    with hdowndef
  set x : Option (ι × ℕ) → Ω := fun j ↦ d j * frobeniusMonomial p w (down j) with hxdef
  have hxp (j : Option (ι × ℕ)) : v (x j ^ p - c j * frobeniusMonomial p w j) < 1 := by
    rcases j with _ | ⟨i, _ | n⟩
    · have h : x none ^ p - c none * frobeniusMonomial p w none = d none ^ p - c none := by
        simp [hxdef, hdowndef, frobeniusMonomial]
      rw [h]
      exact hdp none
    · have hdp0 : v (d (some (i, 0)) ^ p) < 1 := by
        rw [← sub_add_cancel (d _ ^ p) (c _)]
        exact lt_of_le_of_lt (v.map_add _ _) (max_lt (hdp _) (hlev0 i))
      refine lt_of_le_of_lt (v.map_sub _ _) (max_lt ?_ ?_)
      · rw [hxdef, mul_pow, map_mul, map_pow v (frobeniusMonomial _ _ _),
          valuation_frobeniusMonomial p hw1, one_pow, mul_one]
        exact hdp0
      · rw [map_mul, valuation_frobeniusMonomial p hw1, mul_one]
        exact hlev0 i
    · have hm : frobeniusMonomial p w (down (some (i, n + 1))) ^ p =
          frobeniusMonomial p w (some (i, n + 1)) := by
        simp [hdowndef, frobeniusMonomial, ← pow_mul, pow_succ]
      rw [hxdef, mul_pow, hm, ← sub_mul, map_mul, valuation_frobeniusMonomial p hw1, mul_one]
      exact hdp _
  set g := ∑ j ∈ c.support, x j with hgdef
  obtain ⟨-, hg⟩ :=
      valuation_sum_pow_sub_sum_pow_le (v := v) p hp c.support x (μ := 1) fun j _ ↦ by
    rw [hxdef, map_mul, valuation_frobeniusMonomial p hw1, mul_one]
    exact hd1 j
  have hgE : v (g ^ p - E) < 1 := by
    have h : g ^ p - E = (g ^ p - ∑ j ∈ c.support, x j ^ p) +
        ∑ j ∈ c.support, (x j ^ p - c j * frobeniusMonomial p w j) := by
      rw [hEdef, frobeniusComb, Finsupp.sum, sum_sub_distrib]
      ring
    rw [mul_one] at hg
    rw [h]
    exact lt_of_le_of_lt (v.map_add _ _)
      (max_lt (hg.trans_lt hp1) (v.map_sum_lt one_ne_zero fun j _ ↦ hxp j))
  have hvg : v g = 1 := by
    rw [← pow_eq_one_iff_left hp.ne_zero, ← map_pow, ← hE1]
    exact v.map_eq_of_sub_lt (by rwa [hE1])
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, map_zero] at hvg
    exact zero_ne_one hvg
  have hmA := frobeniusMonomial_mem_subring p A hw
  have hgA : g ∈ A := sum_mem fun j _ ↦ mul_mem (hKstA _ (hdK j) (hd1' j)) (hmA _)
  have hEA : E ∈ A := sum_mem fun j _ ↦ mul_mem (hKstA _ (hc j) (hc1 j)) (hmA j)
  set u := E * g⁻¹ ^ p with hudef
  have huA : u ∈ A := mul_mem hEA (pow_mem (hAinv g hgA hvg) _)
  have hu1 : v (u - 1) < 1 := by
    have h : u - 1 = (E - g ^ p) * g⁻¹ ^ p := by
      rw [hudef, sub_mul, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hg0)]
    rw [h, map_mul, map_pow, map_inv₀, hvg, inv_one, one_pow, mul_one, Valuation.map_sub_swap]
    exact hgE
  obtain ⟨c', hc', hc'u⟩ := hAapprox (u - 1) (sub_mem huA (one_mem A)) _ hpL hp0
  have hc'1 (j : Option (ι × ℕ)) : v (c' j) < 1 := by
    refine (hval c' (fun j ↦ hKst (hc' j)) j).trans_lt ?_
    rw [← sub_sub_cancel (u - 1) (frobeniusComb p w c')]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hu1 (hc'u.trans hp1))
  have huzp : (z / g) ^ p = u := by rw [div_pow, hzp, hudef, inv_pow, div_eq_mul_inv]
  obtain ⟨N, hN⟩ := hγN _ hpL hp0
  have hpp : ((p : Ω) ^ p) ∈ L₁ := pow_mem hpL p
  obtain ⟨r, hrL, hr⟩ := exists_pow_eq_of_kummer p K (Subfield.closure (K ∪ A : Set Ω)) L₁ L₂ Kst
    hp hp1 hp0 (fun x hx ↦ Subfield.subset_closure (Or.inl hx))
    (Subfield.closure_le.2 (Set.union_subset hKL₁ fun y hy ↦ hAL₁ y hy)) hL hKst hroot
    (fun i ↦ Subfield.subset_closure (Or.inr (hw i))) hw1 hval γ hγ0 hγ1 hdisc N hN
    (fun j j' ↦ hAapprox _ (mul_mem (hmA j) (hmA j')) _ hpL hp0) hres1 hhens
    (fun y hy ↦ by
      obtain ⟨c, hcK, hlt⟩ := hexp y hy _ hpp (pow_ne_zero p hp0)
      rw [map_pow] at hlt
      exact ⟨c, hcK, (pow_le_of_le_one zero_le (hlt.le.trans (pow_le_one₀ zero_le hp1.le))
        (Nat.sub_ne_zero_of_lt hp.one_lt)).trans hlt.le⟩)
    (Subfield.subset_closure (Or.inr huA)) c' hc' hc'1 hc'u
    ⟨z / g, div_mem hz (hL (hAL₁ g hgA)), huzp⟩
  refine ⟨r * g, mul_mem hrL (hAL₁ g hgA), ?_⟩
  rw [mul_pow, hr, hudef, inv_pow, inv_mul_cancel_right₀ (pow_ne_zero _ hg0)]

/-- **Kummer normal form for approximated elements**: an element `α ∈ L₁`, approximated
arbitrarily well by combinations of the lifted Frobenius monomials with coefficients in the
discrete subfield `K*`, which is a `p`-th power in `L₂`, is a `p`-th power in `L₁`. -/
theorem exists_pow_eq_of_kummer_of_approx (K L₁ L₂ Kst : Subfield Ω)
    (A : Subring Ω) (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hKL₁ : K ≤ L₁) (hL : L₁ ≤ L₂) (hKst : Kst ≤ K) (hAL₁ : ∀ y ∈ A, y ∈ L₁)
    (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c)
    (hw : ∀ i, w i ∈ A) (hw1 : ∀ i, v (w i) = 1) (_hA1 : ∀ y ∈ A, v y ≤ 1)
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) → ∀ j, v (c j) ≤ v (frobeniusComb p w c))
    (γ : Γ₀) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdisc : ∀ c ∈ Kst, c ≠ 0 → ∃ n : ℤ, v c = γ ^ n)
    (hγN : ∀ t ∈ L₁, t ≠ 0 → ∃ N : ℕ, γ ^ N < v t)
    (hAapprox : ∀ y ∈ A, ∀ t ∈ L₁, t ≠ 0 → ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ Kst) ∧
      v (y - frobeniusComb p w e) < v t)
    (hAinv : ∀ y ∈ A, v y = 1 → y⁻¹ ∈ A) (hKstA : ∀ c ∈ Kst, v c ≤ 1 → c ∈ A)
    (hKstroot : ∀ c ∈ Kst, v c ≤ 1 → ∃ d ∈ Kst, v (d ^ p - c) < 1)
    (hexp : ∀ y ∈ Subfield.closure (K ∪ A : Set Ω), ∀ t ∈ L₁, t ≠ 0 →
      ∃ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) ∧ v (y - frobeniusComb p w c) < v t)
    (hres1 : ∀ z ∈ L₂, v z ≤ 1 → ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      (∀ j, v (c j) ≤ 1) → v (z ^ p - frobeniusComb p w c) < 1 →
        ∀ i : ι, v (c (some (i, 0))) < 1)
    (hhens : ∀ x ∈ L₁, v.IsKummerNegligible p x → ∃ y ∈ L₁, y ^ p = 1 + x)
    {α : Ω} (hαL₁ : α ∈ L₁)
    (hα : ∀ t ∈ L₁, t ≠ 0 → ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ Kst) ∧
      v (α - frobeniusComb p w e) < v t)
    (h₂ : ∃ y ∈ L₂, y ^ p = α) : ∃ y ∈ L₁, y ^ p = α := by
  classical
  classical
  by_cases hα0 : α = 0
  · exact ⟨0, zero_mem _, by rw [hα0, zero_pow hp.ne_zero]⟩
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  have hvα : 0 < v α := v.pos_iff.2 hα0
  -- approximate `α` by a combination `E`
  obtain ⟨e, he, hαE⟩ := hα (α * (p : Ω) ^ 2) (mul_mem hαL₁ (pow_mem (natCast_mem L₁ p) 2))
    (mul_ne_zero hα0 (pow_ne_zero 2 hp0))
  rw [map_mul, map_pow] at hαE
  set E := frobeniusComb p w e with hEdef
  have hp21 : v (p : Ω) ^ 2 < 1 := pow_lt_one₀ zero_le hp1 two_ne_zero
  have hvE : v E = v α :=
    v.map_eq_of_sub_lt (by
      rw [Valuation.map_sub_swap]
      exact hαE.trans_le (mul_le_of_le_one_right' hp21.le))
  have hE0 : E ≠ 0 := by
    intro h
    rw [h, map_zero] at hvE
    exact hvα.ne hvE
  set ε := (α - E) / E with hεdef
  have hε : v ε < v (p : Ω) ^ 2 := by
    rw [hεdef, map_div₀, hvE, div_lt_iff₀ hvα, mul_comm]
    exact hαE
  have hεn : v.IsKummerNegligible p ε := by
    have := hp.two_le
    calc v ε ^ (p - 1) ≤ (v (p : Ω) ^ 2) ^ (p - 1) := pow_le_pow_left₀ zero_le hε.le _
      _ = v (p : Ω) ^ (2 * (p - 1)) := by rw [← pow_mul]
      _ ≤ v (p : Ω) ^ p := pow_le_pow_right_of_le_one' hp1.le (by omega)
  have hEL : E ∈ L₁ := sum_mem fun j _ ↦ mul_mem (hKL₁ (hKst (he j)))
    (hAL₁ _ (frobeniusMonomial_mem_subring p A hw j))
  obtain ⟨y₁, hy₁L, hy₁⟩ := hhens ε (div_mem (sub_mem hαL₁ hEL) hEL) hεn
  have h1ε : 1 + ε ≠ 0 := by
    intro h
    have h' := valuation_one_add_eq_one (v := v) (hε.trans hp21)
    rw [h, map_zero] at h'
    exact zero_ne_one h'
  have hy₁0 : y₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hy₁
    exact h1ε hy₁.symm
  have hαfac : α = E * (1 + ε) := by
    rw [hεdef]
    field_simp
    ring
  -- normalize `E` to value `1`
  obtain ⟨j₀, hj₀⟩ : ∃ j, v (e j) = v E := by
    by_contra h
    push Not at h
    exact lt_irrefl _ (valuation_frobeniusComb_lt p hw1 e (hvE ▸ hvα.ne')
      fun j ↦ lt_of_le_of_ne (hval e (fun j ↦ hKst (he j)) j) (h j))
  set a := e j₀ with hadef
  have hva : 0 < v a := by rwa [hj₀, hvE]
  have ha0 : a ≠ 0 := v.pos_iff.1 hva
  have hcomb : frobeniusComb p w (a⁻¹ • e) = a⁻¹ * E := frobeniusComb_smul p a⁻¹ e
  obtain ⟨d₀, hd₀K, hd₀⟩ := hroot a (hKst (he j₀))
  have hd₀0 : d₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hd₀
    exact ha0 hd₀.symm
  obtain ⟨θ, hθL, hθ⟩ := h₂
  obtain ⟨r, hrL, hr⟩ := exists_pow_eq_frobeniusComb_of_kummer p K L₁ L₂ Kst A hp hp1 hp0 hKL₁
    hL hKst hAL₁ hroot hw hw1 hval γ hγ0 hγ1 hdisc hγN hAapprox hAinv hKstA hKstroot hexp hres1
    hhens (a⁻¹ • e) (fun j ↦ mul_mem (inv_mem (he j₀)) (he j))
    (fun j ↦ by
      rw [Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, inv_mul_le_one₀ hva, hj₀]
      exact hval e (fun j ↦ hKst (he j)) j)
    (by rw [hcomb, map_mul, map_inv₀, ← hj₀, inv_mul_cancel₀ hva.ne'])
    (div_mem hθL (mul_mem (hL hy₁L) (hL (hKL₁ hd₀K))))
    (by
      rw [hcomb, div_pow, mul_pow, hθ, hy₁, hd₀, hαfac]
      field_simp)
  refine ⟨r * d₀ * y₁, mul_mem (mul_mem hrL (hKL₁ hd₀K)) hy₁L, ?_⟩
  rw [mul_pow, mul_pow, hr, hcomb, hd₀, hy₁, hαfac]
  field_simp
