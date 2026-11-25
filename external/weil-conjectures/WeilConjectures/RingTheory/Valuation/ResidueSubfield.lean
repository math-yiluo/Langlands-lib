/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# The residue field of a subfield

Let `𝒪` be a valuation subring of a field `Ω` and `S ⊆ Ω` a subfield. The residues of the elements
of `S ∩ 𝒪` form a subfield `𝒪.residueSubfield S` of the residue field of `𝒪`: the residue field of
the restriction of the valuation to `S`.
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

/-- The residues of the integral elements of a subfield `S`: the residue field of `S ∩ 𝒪`, as a
subfield of the residue field of `𝒪`. -/
def residueSubfield (S : Subfield Ω) : Subfield (ResidueField 𝒪) where
  carrier := {z | ∃ y : 𝒪, (y : Ω) ∈ S ∧ residue 𝒪 y = z}
  mul_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y * y', S.mul_mem hy hy', map_mul _ _ _⟩
  one_mem' := ⟨1, S.one_mem, map_one _⟩
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', S.add_mem hy hy', map_add _ _ _⟩
  zero_mem' := ⟨0, S.zero_mem, map_zero _⟩
  neg_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨-y, S.neg_mem hy, map_neg _ _⟩
  inv_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    by_cases h : residue 𝒪 y = 0
    · exact ⟨0, S.zero_mem, by rw [h, inv_zero, map_zero]⟩
    · have hu : IsUnit y := (residue_ne_zero_iff_isUnit y).1 h
      have h1 : ((hu.unit⁻¹ : 𝒪ˣ) : 𝒪) * y = 1 := hu.unit.inv_mul
      refine ⟨((hu.unit⁻¹ : 𝒪ˣ) : 𝒪), ?_, ?_⟩
      · have h2 : (((hu.unit⁻¹ : 𝒪ˣ) : 𝒪) : Ω) = (y : Ω)⁻¹ :=
          eq_inv_of_mul_eq_one_left (by exact_mod_cast h1)
        rw [h2]
        exact S.inv_mem hy
      · exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, h1, map_one])

variable {𝒪}

lemma mem_residueSubfield {S : Subfield Ω} {z : ResidueField 𝒪} :
    z ∈ 𝒪.residueSubfield S ↔ ∃ y : 𝒪, (y : Ω) ∈ S ∧ residue 𝒪 y = z :=
  Iff.rfl

lemma residue_mem_residueSubfield {S : Subfield Ω} {y : 𝒪} (hy : (y : Ω) ∈ S) :
    residue 𝒪 y ∈ 𝒪.residueSubfield S :=
  ⟨y, hy, rfl⟩

lemma residueSubfield_mono {S T : Subfield Ω} (h : S ≤ T) :
    𝒪.residueSubfield S ≤ 𝒪.residueSubfield T := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

end ValuationSubring
