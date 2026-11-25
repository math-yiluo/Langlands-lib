/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.GaussStability.Package
public import WeilConjectures.RingTheory.Valuation.KummerNormalFormGeneral

/-!
# Stability of residually transcendental extensions: Kummer case

See `WeilConjectures.RingTheory.Valuation.GaussStability`.
-/

@[expose] public section

open IsLocalRing IntermediateField

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

/-- If `S` and `T` are integral and congruent modulo the maximal ideal, so are their powers. -/
lemma _root_.Valuation.map_pow_sub_pow_lt_one {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {S T : R} (hS : v S ≤ 1)
    (hT : v T ≤ 1) (hST : v (S - T) < 1) (k : ℕ) : v (S ^ k - T ^ k) < 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : S ^ (k + 1) - T ^ (k + 1) = S * (S ^ k - T ^ k) + T ^ k * (S - T) := by ring
    rw [e]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact (mul_le_of_le_one_left zero_le hS).trans_lt ih
    · rw [map_mul, map_pow]
      exact (mul_le_of_le_one_left zero_le (pow_le_one' hT _)).trans_lt hST

/-- **Stability, Kummer case.** -/
theorem exists_pow_root_of_transcendental {p : ℕ} [Fact p.Prime] [CharZero Ω]
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
    (hhens : ∀ y ∈ Subfield.closure ((K : Set Ω) ∪ B), 𝒪.valuation.IsKummerNegligible p y →
      ∃ z ∈ Subfield.closure ((K : Set Ω) ∪ B), z ^ p = 1 + y)
    {α : Ω} (hα : α ∈ Subfield.closure ((K : Set Ω) ∪ B)) (h₂ : ∃ θ ∈ L₂, θ ^ p = α) :
    ∃ θ ∈ Subfield.closure ((K : Set Ω) ∪ B), θ ^ p = α := by
  classical
  set v := 𝒪.valuation
  set L₁ := Subfield.closure ((K : Set Ω) ∪ B)
  have hp : p.Prime := Fact.out
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hp1 : v (p : Ω) < 1 := by
    have hpm : (p : 𝒪) ∈ maximalIdeal 𝒪 := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
    simpa using (𝒪.valuation_lt_one_iff _).1 hpm
  obtain ⟨ι, w, A, Kst, hKst, hwA, hA, hw1, hval, hpb, ⟨ϖ', hϖ'K, hϖ'0, hϖ'1, hdisc', hϖ'N⟩,
    hAapp, hαapp, hexp, hAinv, hKstA, hKstroot⟩ :=
    𝒪.exists_frobeniusLift_package_of_transcendental K K₀ B hK₀K hK₀B hϖ hϖ0 hϖ1 hdisc harch
      halg hfull hxB htr hBalg hBsep hα
  have hKL₁ : K ≤ L₁ := fun z hz ↦ Subfield.subset_closure (Or.inl hz)
  have hroot (c : Ω) (hc : c ∈ K) : ∃ d ∈ K, d ^ p = c := by
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (⟨c, hc⟩ : K) hp.pos
    exact ⟨d, d.2, congrArg Subtype.val hd⟩
  have hres (z : Ω) (hz : z ∈ L₂) (hz1 : v z ≤ 1) (c : Option (ι × ℕ) →₀ Ω)
      (hcK : ∀ j, c j ∈ K) (hc1 : ∀ j, v (c j) ≤ 1)
      (hlt : v (z ^ p - frobeniusComb p w c) < 1) (i : ι) : v (c (some (i, 0))) < 1 := by
    by_contra hge
    obtain ⟨N, y, hy, hyv⟩ := hpb c hcK hc1 ⟨i, le_antisymm (hc1 _) (not_lt.1 hge)⟩
    set S := frobeniusComb p w c
    have hy1 (k : ℕ) : v (y k) ≤ 1 := (hy k).2
    set Z := ∑ k ∈ Finset.range N, y k * z ^ k
    have hZL : Z ∈ L₂ :=
      sum_mem fun k _ ↦ L₂.mul_mem (hL (hy k).1) (L₂.pow_mem hz _)
    have hZ1 : v Z ≤ 1 := v.map_sum_le fun k _ ↦ by
      rw [map_mul, map_pow]
      exact mul_le_one' (hy1 k) (pow_le_one' hz1 _)
    have hZp : v (Z ^ p - ∑ k ∈ Finset.range N, y k ^ p * (z ^ p) ^ k) < 1 := by
      have h := (valuation_sum_pow_sub_sum_pow_le p hp (Finset.range N)
        (fun k ↦ y k * z ^ k) (v := v) (μ := 1) fun k _ ↦ pow_le_one' (by
          rw [map_mul, map_pow]
          exact mul_le_one' (hy1 k) (pow_le_one' hz1 _)) _).2
      have e : ∑ k ∈ Finset.range N, (y k * z ^ k) ^ p =
          ∑ k ∈ Finset.range N, y k ^ p * (z ^ p) ^ k :=
        Finset.sum_congr rfl fun k _ ↦ by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k p]
      rw [e, mul_one] at h
      exact h.trans_lt hp1
    have hS1 : v S ≤ 1 := by
      have e : S = z ^ p - (z ^ p - S) := by ring
      rw [e]
      exact v.map_sub_le (by rw [map_pow]; exact pow_le_one' hz1 _) hlt.le
    have h2 : v (∑ k ∈ Finset.range N, y k ^ p * S ^ k -
        ∑ k ∈ Finset.range N, y k ^ p * (z ^ p) ^ k) < 1 := by
      rw [← Finset.sum_sub_distrib]
      refine v.map_sum_lt one_ne_zero fun k _ ↦ ?_
      rw [← mul_sub, map_mul, map_pow]
      refine (mul_le_of_le_one_left zero_le (pow_le_one' (hy1 k) _)).trans_lt ?_
      refine v.map_pow_sub_pow_lt_one hS1 (by rw [map_pow]; exact pow_le_one' hz1 _) ?_ k
      rw [← v.map_neg, neg_sub]
      exact hlt
    have h3 : v ((x : Ω) - Z ^ p) < 1 := by
      have e : (x : Ω) - Z ^ p = ((x : Ω) - ∑ k ∈ Finset.range N, y k ^ p * S ^ k) +
          (∑ k ∈ Finset.range N, y k ^ p * S ^ k -
            ∑ k ∈ Finset.range N, y k ^ p * (z ^ p) ^ k) +
          (∑ k ∈ Finset.range N, y k ^ p * (z ^ p) ^ k - Z ^ p) := by ring
      rw [e]
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt (lt_of_le_of_lt (v.map_add _ _)
        (max_lt hyv h2)) ?_)
      rw [← v.map_neg, neg_sub]
      exact hZp
    rw [hxp Z hZL hZ1] at h3
    exact lt_irrefl _ h3
  exact exists_pow_eq_of_kummer_of_approx p K L₁ L₂ Kst A hp hp1 hp0 hKL₁ hL hKst
    (fun y hy ↦ (hA y hy).1) hroot hwA hw1 (fun y hy ↦ (hA y hy).2) hval (v ϖ') hϖ'0 hϖ'1
    hdisc' (fun t _ ht ↦ hϖ'N t ht) (fun y hy t _ ht ↦ hAapp y hy t ht) hAinv hKstA hKstroot
    (fun y hy t _ ht ↦ hexp y hy t ht) hres hhens hα (fun t _ ht ↦ hαapp t ht) h₂

end ValuationSubring
