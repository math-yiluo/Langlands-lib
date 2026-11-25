/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.GaussStability.Package
public import WeilConjectures.RingTheory.Valuation.ArtinSchreierNormalForm

/-!
# Stability of residually transcendental extensions: Artin–Schreier case

See `WeilConjectures.RingTheory.Valuation.GaussStability`.
-/

@[expose] public section

open IsLocalRing IntermediateField

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

/-- **Stability, Artin–Schreier case.** -/
theorem exists_artinSchreier_root_of_transcendental {p : ℕ} [Fact p.Prime] [CharP Ω p]
    [CharP (ResidueField 𝒪) p] (K K₀ B L₂ : Subfield Ω) [IsAlgClosed K] (hK₀K : K₀ ≤ K)
    (hK₀B : K₀ ≤ B) {ϖ : Ω} (hϖ : ϖ ∈ K₀) (hϖ0 : ϖ ≠ 0) (hϖ1 : 𝒪.valuation ϖ < 1)
    (hdisc : ∀ z ∈ B, z ≠ 0 → ∃ m : ℤ, 𝒪.valuation z = 𝒪.valuation ϖ ^ m)
    (harch : ∀ z : Ω, z ≠ 0 →
      ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, 𝒪.valuation z ^ n = 𝒪.valuation ϖ ^ m)
    (halg : ∀ c ∈ K, IsAlgebraic K₀ c)
    (hfull : ∀ y ∈ K, 𝒪.valuation y ≤ 1 → ∃ z ∈ K₀, 𝒪.valuation (y - z) < 1)
    {x : 𝒪} (hxB : (x : Ω) ∈ B)
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    (hBalg : ∀ b ∈ B, IsAlgebraic (adjoin K₀ {(x : Ω)}) b)
    (hBsep : ∀ b : 𝒪, (b : Ω) ∈ B →
      IsSeparable (adjoin (𝒪.residueSubfield K) {residue 𝒪 x}) (residue 𝒪 b))
    (hL : Subfield.closure ((K : Set Ω) ∪ B) ≤ L₂)
    (hxp : ∀ z ∈ L₂, 𝒪.valuation z ≤ 1 → 𝒪.valuation ((x : Ω) - z ^ p) = 1)
    (hhens : ∀ b ∈ Subfield.closure ((K : Set Ω) ∪ B), 𝒪.valuation b ≤ 1 →
      ∃ θ ∈ Subfield.closure ((K : Set Ω) ∪ B), θ ^ p - θ = b)
    {α : Ω} (hα : α ∈ Subfield.closure ((K : Set Ω) ∪ B)) (h₂ : ∃ θ ∈ L₂, θ ^ p - θ = α) :
    ∃ θ ∈ Subfield.closure ((K : Set Ω) ∪ B), θ ^ p - θ = α := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set v := 𝒪.valuation
  set L₁ := Subfield.closure ((K : Set Ω) ∪ B)
  obtain ⟨ι, w, A, Kst, hKst, hwA, hA, hw1, hval, hpb, -, -, hP6, -⟩ :=
    exists_frobeniusLift_package_of_transcendental 𝒪 K K₀ B hK₀K hK₀B hϖ hϖ0 hϖ1 hdisc harch
      halg hfull hxB htr hBalg hBsep hα
  have hKL₁ : K ≤ L₁ := fun _ h ↦ Subfield.subset_closure (Or.inl h)
  -- `p`-th powers and Artin–Schreier roots of constants
  have hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c := by
    intro c hc
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (⟨c, hc⟩ : K) (Nat.pos_of_ne_zero hp0)
    exact ⟨d, d.2, congrArg Subtype.val hd⟩
  have hAS : ∀ c ∈ K, ∃ d ∈ K, d ^ p - d = c := by
    intro c hc
    have h1 : (Polynomial.X : Polynomial K).degree < (Polynomial.X ^ p : Polynomial K).degree := by
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.X -
      Polynomial.C (⟨c, hc⟩ : K)) (by
        rw [Polynomial.degree_sub_C (by
          rw [Polynomial.degree_sub_eq_left_of_degree_lt h1, Polynomial.degree_X_pow]
          exact_mod_cast Nat.pos_of_ne_zero hp0),
          Polynomial.degree_sub_eq_left_of_degree_lt h1, Polynomial.degree_X_pow]
        exact_mod_cast hp0)
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at hd
    exact ⟨d, d.2, congrArg Subtype.val hd⟩
  have hval' : ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      ∀ i ∈ s, v (c i) ≤ v (∑ j ∈ s, c j * w j) := by
    intro s c hc i hi
    have h := hval (∑ j ∈ s, Finsupp.single (some (j, 0)) (c j))
      (sum_single_some_mem _ s hc) (some (i, 0))
    rwa [sum_single_some_apply s c hi, frobeniusComb_sum_single] at h
  -- powers of congruent elements are congruent
  have hpowcong (S T : Ω) (hS : v S ≤ 1) (hT : v T ≤ 1) (hST : v (S - T) < 1) (k : ℕ) :
      v (S ^ k - T ^ k) < 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h : S ^ (k + 1) - T ^ (k + 1) = S * (S ^ k - T ^ k) + T ^ k * (S - T) := by ring
      rw [h]
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        exact (mul_le_of_le_one_left zero_le hS).trans_lt ih
      · rw [map_mul, map_pow]
        exact (mul_le_of_le_one_left zero_le (pow_le_one' hT _)).trans_lt hST
  have hres : ∀ z ∈ L₂, v z ≤ 1 → ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      (∀ i ∈ s, v (c i) ≤ 1) → v (z ^ p - ∑ i ∈ s, c i * w i) < 1 →
        ∀ i ∈ s, v (c i) < 1 := by
    intro z hz hz1 s c hcK hc1 hlt i hi
    by_contra hge
    rw [not_lt] at hge
    obtain ⟨N, y, hy, hyv⟩ := hpb (∑ j ∈ s, Finsupp.single (some (j, 0)) (c j))
      (sum_single_some_mem _ s hcK) (fun j ↦ by
        rw [Finsupp.finsetSum_apply]
        refine v.map_sum_le fun j' hj' ↦ ?_
        rw [Finsupp.single_apply]
        split_ifs
        exacts [hc1 j' hj', by simp])
      ⟨i, (sum_single_some_apply s c hi).symm ▸ le_antisymm (hc1 i hi) hge⟩
    rw [frobeniusComb_sum_single] at hyv
    set S := ∑ j ∈ s, c j * w j
    set Z := ∑ k ∈ Finset.range N, y k * z ^ k with hZdef
    have hZL : Z ∈ L₂ := sum_mem fun k _ ↦ L₂.mul_mem (hL (hy k).1) (L₂.pow_mem hz _)
    have hZ1 : v Z ≤ 1 := v.map_sum_le fun k _ ↦ by
      rw [map_mul, map_pow]
      exact mul_le_one' (hy k).2 (pow_le_one' hz1 _)
    have hZp : Z ^ p = ∑ k ∈ Finset.range N, y k ^ p * (z ^ p) ^ k := by
      rw [hZdef, sum_pow_char]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k p]
    have hzp1 : v (z ^ p) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one' hz1 _
    have hS1 : v S ≤ 1 := by
      rw [← sub_sub_cancel (z ^ p) S]
      exact v.map_sub_le hzp1 hlt.le
    have h2 : v (∑ k ∈ Finset.range N, y k ^ p * S ^ k - Z ^ p) < 1 := by
      rw [hZp, ← Finset.sum_sub_distrib]
      refine v.map_sum_lt one_ne_zero fun k _ ↦ ?_
      rw [← mul_sub, map_mul, map_pow]
      refine (mul_le_of_le_one_left zero_le (pow_le_one' (hy k).2 _)).trans_lt ?_
      refine hpowcong S (z ^ p) hS1 hzp1 ?_ k
      rw [← v.map_neg, neg_sub]
      exact hlt
    have h3 : v ((x : Ω) - Z ^ p) < 1 := by
      rw [← sub_add_sub_cancel (x : Ω) (∑ k ∈ Finset.range N, y k ^ p * S ^ k) (Z ^ p)]
      exact lt_of_le_of_lt (v.map_add _ _) (max_lt hyv h2)
    rw [hxp Z hZL hZ1] at h3
    exact lt_irrefl _ h3
  obtain ⟨e, he, hev⟩ := hP6 1 one_ne_zero
  rw [map_one] at hev
  refine exists_artinSchreier_root_of_approx p v K L₁ L₂ w hKL₁ hL hroot hAS
    (fun i ↦ (hA _ (hwA i)).1) hw1 hval' hhens hres hα e.some.support e.some
    (fun j _ ↦ hKst (he _)) (hKst (he none)) ?_ h₂
  have h : α - e none - ∑ j ∈ e.some.support, e.some j * w j.1 ^ p ^ j.2 =
      α - frobeniusComb p w e := by
    rw [frobeniusComb_eq, liftedSum, Finsupp.sum]
    ring
  rw [h]
  exact hev.le

end ValuationSubring
