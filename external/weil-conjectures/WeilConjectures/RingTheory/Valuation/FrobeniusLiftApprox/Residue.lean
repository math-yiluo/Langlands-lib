/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ResidueSubfield
public import WeilConjectures.RingTheory.Valuation.KummerNormalFormStageOne
public import WeilConjectures.RingTheory.Valuation.FrobeniusLiftApprox.Discrete
public import Mathlib.Algebra.BigOperators.Field

/-!
# Lifts of a Frobenius-closed family of residues

Let `𝒪` be a valuation subring of a field `Ω` and `u i` elements of the residue field whose
monomials `1, u i ^ p ^ n` are linearly independent over the residues `k` of a subfield `K`. Let
`W i ∈ 𝒪` be lifts of the `u i`. We show:

* the lifted monomials are valuation independent over `K`
  (`ValuationSubring.valuation_le_valuation_frobeniusComb`);
* the `p`-th power of a `k`-combination of the monomials has zero coefficients on the `u i`
  (`ValuationSubring.pow_ne_linearCombination`);
* if the monomials span the residues of a subfield `D`, every element of `D ∩ 𝒪` is congruent
  modulo the maximal ideal to a combination of the lifted monomials with coefficients in any
  subfield `K₀` whose residues contain `k` (`ValuationSubring.exists_valuation_sub_lt_one`).
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

lemma valuation_lt_one_iff_residue_eq_zero (a : 𝒪) :
    𝒪.valuation (a : Ω) < 1 ↔ residue 𝒪 a = 0 := by
  rw [residue_eq_zero_iff, valuation_lt_one_iff]

lemma valuation_sub_lt_one_iff (a b : 𝒪) :
    𝒪.valuation ((a : Ω) - b) < 1 ↔ residue 𝒪 a = residue 𝒪 b := by
  rw [← sub_eq_zero, ← map_sub, ← valuation_lt_one_iff_residue_eq_zero]
  rfl

lemma valuation_eq_one_of_residue_ne_zero {a : 𝒪} (h : residue 𝒪 a ≠ 0) :
    𝒪.valuation (a : Ω) = 1 :=
  (valuation_eq_one_iff _ _).1 ((residue_ne_zero_iff_isUnit _).1 h)

lemma residue_ne_zero_of_valuation_eq_one {a : 𝒪} (h : 𝒪.valuation (a : Ω) = 1) :
    residue 𝒪 a ≠ 0 :=
  (residue_ne_zero_iff_isUnit _).2 ((valuation_eq_one_iff _ _).2 h)

variable {p : ℕ} {ι : Type*}

lemma frobeniusMonomial_coe (W : ι → 𝒪) (j : Option (ι × ℕ)) :
    frobeniusMonomial p (fun i ↦ (W i : Ω)) j = ((j.elim 1 fun i ↦ W i.1 ^ p ^ i.2 : 𝒪) : Ω) := by
  cases j <;> simp [frobeniusMonomial]

lemma residue_elim_pow {W : ι → 𝒪} {u : ι → ResidueField 𝒪} (hW : ∀ i, residue 𝒪 (W i) = u i)
    (j : Option (ι × ℕ)) :
    residue 𝒪 (j.elim 1 fun i ↦ W i.1 ^ p ^ i.2) = j.elim 1 fun i ↦ u i.1 ^ p ^ i.2 := by
  cases j <;> simp [hW]

/-- A combination of the lifted monomials with integral coefficients, as an element of `𝒪`. -/
lemma frobeniusComb_eq_coe_sum (W : ι → 𝒪) (c : Option (ι × ℕ) →₀ Ω) (a : Option (ι × ℕ) → 𝒪)
    (ha : ∀ j, (a j : Ω) = c j) :
    frobeniusComb p (fun i ↦ (W i : Ω)) c =
      ((∑ j ∈ c.support, a j * j.elim 1 fun i ↦ W i.1 ^ p ^ i.2 : 𝒪) : Ω) := by
  rw [frobeniusComb, Finsupp.sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ ↦ by rw [frobeniusMonomial_coe, ha]

/-- **Residual independence.** If the residues of the `m j ∈ 𝒪` are linearly independent over the
residues of a subfield `K`, a combination of the `m j` with integral coefficients in `K` has value
`< 1` only if all coefficients do. -/
lemma valuation_lt_one_of_sum_mul_lt_one {K : Subfield Ω} {κ : Type*} {m : κ → 𝒪}
    (hli : LinearIndependent (𝒪.residueSubfield K) fun j ↦ residue 𝒪 (m j)) {s : Finset κ}
    {a : κ → 𝒪} (haK : ∀ j, (a j : Ω) ∈ K)
    (h : 𝒪.valuation ((∑ j ∈ s, a j * m j : 𝒪) : Ω) < 1) {j : κ} (hj : j ∈ s) :
    𝒪.valuation (a j : Ω) < 1 := by
  rw [valuation_lt_one_iff_residue_eq_zero, map_sum] at h
  rw [valuation_lt_one_iff_residue_eq_zero]
  have h0 := linearIndependent_iff'.1 hli s
    (fun j ↦ (⟨residue 𝒪 (a j), a j, haK j, rfl⟩ : 𝒪.residueSubfield K))
    (by simpa [Subfield.smul_def] using h) j hj
  exact congrArg Subtype.val h0

/-- **Valuation independence of the lifted monomials.** If the monomials `1, u i ^ p ^ n` are
linearly independent over the residues of `K` and `W i ∈ 𝒪` lifts `u i`, then the value of a
combination of the lifted monomials with coefficients in `K` is at least that of each
coefficient. -/
theorem valuation_le_valuation_frobeniusComb {K : Subfield Ω} {u : ι → ResidueField 𝒪}
    (hli : LinearIndependent (𝒪.residueSubfield K)
      fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2)
    {W : ι → 𝒪} (hW : ∀ i, residue 𝒪 (W i) = u i) {c : Option (ι × ℕ) →₀ Ω}
    (hc : ∀ j, c j ∈ K) (j : Option (ι × ℕ)) :
    𝒪.valuation (c j) ≤ 𝒪.valuation (frobeniusComb p (fun i ↦ (W i : Ω)) c) := by
  classical
  by_contra! h
  have hj : j ∈ c.support := Finsupp.mem_support_iff.2 fun h0 ↦ by
    rw [h0, map_zero] at h
    exact not_lt_zero h
  obtain ⟨j₀, hj₀, hmax⟩ := c.support.exists_max_image (fun j ↦ 𝒪.valuation (c j)) ⟨j, hj⟩
  have h0 : c j₀ ≠ 0 := Finsupp.mem_support_iff.1 hj₀
  have hpos : 0 < 𝒪.valuation (c j₀) := zero_lt_iff.2 ((𝒪.valuation.ne_zero_iff).2 h0)
  have hle (j' : Option (ι × ℕ)) : 𝒪.valuation (c j' / c j₀) ≤ 1 := by
    rw [map_div₀, div_le_one₀ hpos]
    by_cases hj' : j' ∈ c.support
    · exact hmax j' hj'
    · rw [Finsupp.notMem_support_iff.1 hj', map_zero]
      exact zero_le
  let a : Option (ι × ℕ) → 𝒪 := fun j' ↦ ⟨c j' / c j₀, (valuation_le_one_iff _ _).1 (hle j')⟩
  have hsum : frobeniusComb p (fun i ↦ (W i : Ω)) c / c j₀ =
      ((∑ j' ∈ c.support, a j' * j'.elim 1 fun i ↦ W i.1 ^ p ^ i.2 : 𝒪) : Ω) := by
    rw [frobeniusComb, Finsupp.sum, Finset.sum_div]
    push_cast
    exact Finset.sum_congr rfl fun j' _ ↦ by rw [frobeniusMonomial_coe, div_mul_eq_mul_div]
  have hlt := valuation_lt_one_of_sum_mul_lt_one (m := fun j' ↦ j'.elim 1 fun i ↦ W i.1 ^ p ^ i.2)
    (by simpa only [residue_elim_pow hW] using hli) (a := a) (fun j' ↦ div_mem (hc j') (hc j₀))
    (by rw [← hsum, map_div₀, div_lt_one₀ hpos]; exact h.trans_le (hmax j hj)) hj₀
  simp [a, div_self h0] at hlt

/-- **Approximation modulo the maximal ideal.** If the residues of `D` lie in the span of the
monomials `1, u i ^ p ^ n` over a subfield `k` all of whose elements are residues of integral
elements of `K₀`, then every element of `D ∩ 𝒪` is congruent modulo the maximal ideal to a
combination of the lifted monomials with coefficients in `K₀`. -/
theorem exists_valuation_sub_lt_one {K₀ D : Subfield Ω} {k : Subfield (ResidueField 𝒪)}
    {u : ι → ResidueField 𝒪}
    (hsp : ∀ e ∈ 𝒪.residueSubfield D, e ∈ Submodule.span k
      (Set.range fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2))
    (hlift : ∀ a ∈ k, ∃ z : 𝒪, (z : Ω) ∈ K₀ ∧ residue 𝒪 z = a)
    {W : ι → 𝒪} (hW : ∀ i, residue 𝒪 (W i) = u i) {d : 𝒪} (hd : (d : Ω) ∈ D) :
    ∃ e : Option (ι × ℕ) →₀ Ω, (∀ j, e j ∈ K₀) ∧
      𝒪.valuation ((d : Ω) - frobeniusComb p (fun i ↦ (W i : Ω)) e) < 1 := by
  classical
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hsp _ ⟨d, hd, rfl⟩)
  choose G hGK hGres using fun a : k ↦ hlift a a.2
  let G' : k → 𝒪 := fun a ↦ if a = 0 then 0 else G a
  have hG'K (a : k) : (G' a : Ω) ∈ K₀ := by
    by_cases ha : a = 0
    · simp [G', ha]
    · simpa [G', ha] using hGK a
  have hG'res (a : k) : residue 𝒪 (G' a) = a := by
    by_cases ha : a = 0
    · simp [G', ha]
    · simpa [G', ha] using hGres a
  refine ⟨Finsupp.mapRange (fun a ↦ (G' a : Ω)) (by simp [G']) f, fun j ↦ hG'K (f j), ?_⟩
  have hcomb : frobeniusComb p (fun i ↦ (W i : Ω))
      (Finsupp.mapRange (fun a ↦ (G' a : Ω)) (by simp [G']) f) =
      ((∑ j ∈ f.support, G' (f j) * j.elim 1 fun i ↦ W i.1 ^ p ^ i.2 : 𝒪) : Ω) := by
    rw [frobeniusComb, Finsupp.sum_mapRange_index (fun _ ↦ zero_mul _), Finsupp.sum]
    push_cast
    exact Finset.sum_congr rfl fun j _ ↦ by rw [frobeniusMonomial_coe]
  rw [hcomb, valuation_sub_lt_one_iff, ← hf, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, hG'res, residue_elim_pow hW]
  rfl

/-- **Approximation to arbitrary precision.** In the situation of
`ValuationSubring.exists_valuation_sub_lt_one`, assume moreover that `D` is discretely valued
with uniformizer `ϖ ∈ K₀`, and that the `W i` lie in `D`. Then every element of `D ∩ 𝒪` is
approximated to precision `v ϖ ^ N` by a combination of the lifted monomials with coefficients
in `K₀`. -/
theorem exists_valuation_sub_le_pow {K₀ D : Subfield Ω} (hK₀D : K₀ ≤ D)
    {k : Subfield (ResidueField 𝒪)} {u : ι → ResidueField 𝒪}
    (hsp : ∀ e ∈ 𝒪.residueSubfield D, e ∈ Submodule.span k
      (Set.range fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2))
    (hlift : ∀ a ∈ k, ∃ z : 𝒪, (z : Ω) ∈ K₀ ∧ residue 𝒪 z = a)
    {W : ι → 𝒪} (hW : ∀ i, residue 𝒪 (W i) = u i) (hWD : ∀ i, (W i : Ω) ∈ D)
    {ϖ : Ω} (hϖ : ϖ ∈ K₀) (hϖ0 : ϖ ≠ 0) (hϖ1 : 𝒪.valuation ϖ < 1)
    (hdisc : ∀ z ∈ D, z ≠ 0 → ∃ m : ℤ, 𝒪.valuation z = 𝒪.valuation ϖ ^ m) (N : ℕ) {d : Ω}
    (hd : d ∈ D) (hd1 : 𝒪.valuation d ≤ 1) :
    ∃ e : Option (ι × ℕ) →₀ Ω, (∀ j, e j ∈ K₀) ∧
      𝒪.valuation (d - frobeniusComb p (fun i ↦ (W i : Ω)) e) ≤ 𝒪.valuation ϖ ^ N := by
  induction N generalizing d with
  | zero => exact ⟨0, fun _ ↦ K₀.zero_mem, by rwa [frobeniusComb_zero, sub_zero, pow_zero]⟩
  | succ N ih =>
    obtain ⟨e₀, he₀K, he₀⟩ := exists_valuation_sub_lt_one hsp hlift hW
      (d := ⟨d, (valuation_le_one_iff _ _).1 hd1⟩) hd
    have hcombD : frobeniusComb p (fun i ↦ (W i : Ω)) e₀ ∈ D :=
      D.sum_mem fun j _ ↦ D.mul_mem (hK₀D (he₀K j)) (frobeniusMonomial_mem p D hWD j)
    have hd'D : d - frobeniusComb p (fun i ↦ (W i : Ω)) e₀ ∈ D := sub_mem hd hcombD
    by_cases hd'0 : d - frobeniusComb p (fun i ↦ (W i : Ω)) e₀ = 0
    · exact ⟨e₀, he₀K, by rw [hd'0, map_zero]; exact zero_le⟩
    have hγ : 𝒪.valuation ϖ ≠ 0 := (𝒪.valuation.ne_zero_iff).2 hϖ0
    obtain ⟨m, hm⟩ := hdisc _ hd'D hd'0
    have hle : 𝒪.valuation (d - frobeniusComb p (fun i ↦ (W i : Ω)) e₀) ≤ 𝒪.valuation ϖ := by
      rw [hm] at he₀ ⊢
      exact Valuation.zpow_le_self_of_zpow_lt_one hγ hϖ1 he₀
    obtain ⟨e', he'K, he'⟩ := ih (div_mem hd'D (hK₀D hϖ))
      (by rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hγ)]; exact hle)
    refine ⟨e₀ + ϖ • e', fun j ↦ K₀.add_mem (he₀K j) (K₀.mul_mem hϖ (he'K j)), ?_⟩
    have heq : d - frobeniusComb p (fun i ↦ (W i : Ω)) (e₀ + ϖ • e') =
        ϖ * ((d - frobeniusComb p (fun i ↦ (W i : Ω)) e₀) / ϖ -
          frobeniusComb p (fun i ↦ (W i : Ω)) e') := by
      rw [frobeniusComb_add, frobeniusComb_smul, mul_sub, mul_div_cancel₀ _ hϖ0]
      ring
    rw [heq, map_mul, pow_succ']
    gcongr

end ValuationSubring
