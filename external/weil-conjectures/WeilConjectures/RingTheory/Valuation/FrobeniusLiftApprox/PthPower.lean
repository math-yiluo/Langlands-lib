/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.FrobeniusLiftApprox.Residue
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Residues which are not `p`-th powers

Let `R` be a field of characteristic `p` and `k ≤ R` a subfield such that the monomials
`1, u i ^ p ^ n` are linearly independent over `k`. The `p`-th power of a `k`-combination of the
monomials is a combination of the monomials `1, u i ^ p ^ (n + 1)`, so a combination with a
nonzero coefficient on some `u i` is not such a `p`-th power
(`LinearIndependent.pow_ne_linearCombination`).

As an application, if `x̄` is a polynomial with `p`-th power coefficients in every residue `ρ`
of `D` which is not a `p`-th power, then `x` is congruent to a polynomial with `p`-th power
coefficients in any integral combination `S` of the lifted monomials with a unit coefficient on
some `W i` (`ValuationSubring.exists_valuation_sub_sum_pow_mul_pow_lt_one`).
-/

@[expose] public section

open IsLocalRing

variable {ι : Type*}

/-- If the monomials `1, u i ^ p ^ n` are linearly independent over `k` (in characteristic `p`),
then a `k`-combination of them with a nonzero coefficient on some `u i` is not the `p`-th power
of an element of their span. -/
theorem LinearIndependent.pow_ne_linearCombination {R : Type*} [Field R] {p : ℕ} [Fact p.Prime]
    [CharP R p] {k : Subfield R} {u : ι → R}
    (hli : LinearIndependent k fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2) {z : R}
    (hz : z ∈ Submodule.span k
      (Set.range fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2))
    {f : Option (ι × ℕ) →₀ k} {i : ι} (hf : f (some (i, 0)) ≠ 0) :
    z ^ p ≠ Finsupp.linearCombination k
      (fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2) f := by
  intro h
  obtain ⟨g, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hz
  have hp : p.Prime := Fact.out
  have hpow : (g.sum fun j a ↦ a • (j.elim 1 fun i ↦ u i.1 ^ p ^ i.2 : R)) ^ p =
      Finsupp.linearCombination k (fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2)
        (Finsupp.mapDomain (Option.map fun i : ι × ℕ ↦ (i.1, i.2 + 1))
          (Finsupp.mapRange (· ^ p) (zero_pow hp.ne_zero) g)) := by
    rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum, sum_pow_char]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smul_pow]
    congr 1
    cases j <;> simp [pow_succ, pow_mul]
  have h2 := DFunLike.congr_fun (hli (hpow.symm.trans h)) (some (i, 0))
  rw [Finsupp.mapDomain_of_notMem_range] at h2
  · exact hf h2.symm
  · rintro ⟨j, hj⟩
    cases j <;> simp at hj

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω} {p : ℕ}

/-- **Congruence with a polynomial with `p`-th power coefficients.** Let the monomials
`1, u i ^ p ^ n` be linearly independent over the residues `k` of `K` and span the residues `E`
of `D ⊇ K`, and suppose that the residue of `x` is a polynomial of degree `< p` with `p`-th power
coefficients in `E` in every `ρ ∈ E` which is not a `p`-th power in `E`. Then `x` is congruent to
such a polynomial in every integral combination `S` of the lifted monomials with coefficients in
`K` and with a unit coefficient on some `W i`. -/
theorem exists_valuation_sub_sum_pow_mul_pow_lt_one [Fact p.Prime] [CharP (ResidueField 𝒪) p]
    {K D : Subfield Ω} {u : ι → ResidueField 𝒪}
    (hKD : 𝒪.residueSubfield K ≤ 𝒪.residueSubfield D) (hu : ∀ i, u i ∈ 𝒪.residueSubfield D)
    (hli : LinearIndependent (𝒪.residueSubfield K)
      fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2)
    (hsp : ∀ e ∈ 𝒪.residueSubfield D, e ∈ Submodule.span (𝒪.residueSubfield K)
      (Set.range fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2))
    {x : 𝒪} (hpth : ∀ ρ ∈ 𝒪.residueSubfield D, (∀ z ∈ 𝒪.residueSubfield D, z ^ p ≠ ρ) →
      ∃ y : ℕ → ResidueField 𝒪, (∀ j, y j ∈ 𝒪.residueSubfield D) ∧
        residue 𝒪 x = ∑ j ∈ Finset.range p, y j ^ p * ρ ^ j)
    {W : ι → 𝒪} (hW : ∀ i, residue 𝒪 (W i) = u i) {c : Option (ι × ℕ) →₀ Ω}
    (hcK : ∀ j, c j ∈ K) (hc1 : ∀ j, 𝒪.valuation (c j) ≤ 1) {i : ι}
    (hi : 𝒪.valuation (c (some (i, 0))) = 1) :
    ∃ y : ℕ → Ω, (∀ k, y k ∈ D ∧ 𝒪.valuation (y k) ≤ 1) ∧
      𝒪.valuation ((x : Ω) - ∑ k ∈ Finset.range p,
        y k ^ p * frobeniusComb p (fun i ↦ (W i : Ω)) c ^ k) < 1 := by
  classical
  let a : Option (ι × ℕ) → 𝒪 := fun j ↦ ⟨c j, (valuation_le_one_iff _ _).1 (hc1 j)⟩
  set S : 𝒪 := ∑ j ∈ c.support, a j * j.elim 1 fun i ↦ W i.1 ^ p ^ i.2 with hS
  have hcomb : frobeniusComb p (fun i ↦ (W i : Ω)) c = (S : Ω) :=
    frobeniusComb_eq_coe_sum W c a fun _ ↦ rfl
  let f : Option (ι × ℕ) →₀ 𝒪.residueSubfield K := Finsupp.onFinset c.support
    (fun j ↦ ⟨residue 𝒪 (a j), a j, hcK j, rfl⟩) fun j hj ↦ Finsupp.mem_support_iff.2 fun h0 ↦ by
      have ha : a j = 0 := Subtype.ext h0
      exact hj (Subtype.ext (by simp [ha]))
  have hρ : residue 𝒪 S = Finsupp.linearCombination _
      (fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ u i.1 ^ p ^ i.2) f := by
    rw [Finsupp.linearCombination_onFinset, hS, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, residue_elim_pow hW]
    rfl
  have hρE : residue 𝒪 S ∈ 𝒪.residueSubfield D := by
    rw [hS, map_sum]
    refine Subfield.sum_mem _ fun j _ ↦ ?_
    rw [map_mul]
    refine Subfield.mul_mem _ (hKD ⟨a j, hcK j, rfl⟩) ?_
    rw [residue_elim_pow hW]
    cases j with
    | none => exact Subfield.one_mem _
    | some j => exact Subfield.pow_mem _ (hu j.1) _
  clear_value S
  have hf : f (some (i, 0)) ≠ 0 := fun h0 ↦ by
    rw [Finsupp.onFinset_apply] at h0
    exact residue_ne_zero_of_valuation_eq_one hi (congrArg Subtype.val h0)
  obtain ⟨y, hyD, hy⟩ := hpth _ hρE fun z hz hzp ↦
    hli.pow_ne_linearCombination (hsp z hz) hf (hzp.trans hρ)
  choose Y hYD hYres using hyD
  refine ⟨fun k ↦ (Y k : Ω), fun k ↦ ⟨hYD k, valuation_le_one _ _⟩, ?_⟩
  have hsum : ∑ k ∈ Finset.range p, (Y k : Ω) ^ p * (S : Ω) ^ k =
      ((∑ k ∈ Finset.range p, Y k ^ p * S ^ k : 𝒪) : Ω) := by
    push_cast
    rfl
  rw [hcomb, hsum, valuation_sub_lt_one_iff, hy, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, map_pow, map_pow, hYres]

end ValuationSubring
