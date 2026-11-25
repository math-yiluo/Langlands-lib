/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ValuationIndependence

/-!
# Residual independence from linear independence of residues

* `ValuationSubring.valuation_lt_one_iff_inv_notMem`, `ValuationSubring.valuation_comap_lt_one_iff`,
  `ValuationSubring.valuation_comap_eq_one_iff`: the values `< 1`, `= 1` of the pull-back of a
  valuation subring along a field map.
* `Valuation.ResiduallyIndependent.of_linearIndependent_residue`: a family of integral elements
  whose residues are linearly independent over a field `A` is residually independent over every
  field `K` whose integral elements have residues in (the image of) `A`.
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L]

/-- An element has value `< 1` iff it is zero or its inverse is not integral. -/
lemma valuation_lt_one_iff_inv_notMem (A : ValuationSubring K) (x : K) :
    A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hv : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [← valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hv)]
  simp [hx]

/-- The pull-back of a valuation subring along a field map: values `≤ 1`. -/
lemma valuation_comap_le_one_iff (A : ValuationSubring L) (f : K →+* L) (x : K) :
    (A.comap f).valuation x ≤ 1 ↔ A.valuation (f x) ≤ 1 := by
  rw [valuation_le_one_iff, valuation_le_one_iff, mem_comap]

/-- The pull-back of a valuation subring along a field map: values `< 1`. -/
lemma valuation_comap_lt_one_iff (A : ValuationSubring L) (f : K →+* L) (x : K) :
    (A.comap f).valuation x < 1 ↔ A.valuation (f x) < 1 := by
  rw [valuation_lt_one_iff_inv_notMem, valuation_lt_one_iff_inv_notMem, mem_comap, map_inv₀,
    map_eq_zero]

/-- The pull-back of a valuation subring along a field map: values `= 1`. -/
lemma valuation_comap_eq_one_iff (A : ValuationSubring L) (f : K →+* L) (x : K) :
    (A.comap f).valuation x = 1 ↔ A.valuation (f x) = 1 := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, valuation_comap_le_one_iff,
    valuation_comap_lt_one_iff]

end ValuationSubring

namespace Valuation

variable {F K A : Type*} [Field F] [Field K] [Algebra K F] [Field A] {𝒪 : ValuationSubring F}
  [Algebra A (ResidueField 𝒪)]

/-- **Residual independence from linear independence of residues.** Let `E` be a family of
integral elements whose residues are linearly independent over a field `A`, and `K` a field over
`F` whose integral elements have residues in the image of `A`. Then `E` is residually independent
over `K`. -/
theorem ResiduallyIndependent.of_linearIndependent_residue
    (hA : ∀ c : K, ∀ h : algebraMap K F c ∈ 𝒪,
      residue 𝒪 ⟨algebraMap K F c, h⟩ ∈ (algebraMap A (ResidueField 𝒪)).range)
    {ι : Type*} [Fintype ι] (E : ι → 𝒪) (hE : LinearIndependent A fun j ↦ residue 𝒪 (E j)) :
    𝒪.valuation.ResiduallyIndependent K fun j ↦ (E j : F) := by
  intro c hc hlt j
  have hmem (j : ι) : algebraMap K F (c j) ∈ 𝒪 := (𝒪.valuation_le_one_iff _).1 (hc j)
  choose a ha using fun j ↦ hA (c j) (hmem j)
  let γ (j : ι) : 𝒪 := ⟨algebraMap K F (c j), hmem j⟩
  have hsum : ∑ j, c j • (E j : F) = ((∑ j, γ j * E j : 𝒪) : F) := by
    simp [γ, Algebra.smul_def]
  rw [hsum, ← 𝒪.valuation_lt_one_iff, ← residue_eq_zero_iff, map_sum] at hlt
  have hlin : ∑ j, a j • residue 𝒪 (E j) = 0 := by
    rw [← hlt]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, ha, map_mul]
  have hj := Fintype.linearIndependent_iff.1 hE a hlin j
  have haj := ha j
  rw [hj, map_zero] at haj
  exact (𝒪.valuation_lt_one_iff (γ j)).1 ((residue_eq_zero_iff _).1 haj.symm)

end Valuation
