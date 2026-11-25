/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import WeilConjectures.Mathlib.Algebra.Ring.Subring.Basic

/-!
# The composite of two valuation rings

Given a valuation subring `A` of a field `K` and a valuation subring `A''` of the residue
field of `A`, the preimage of `A''` under the residue map of `A` is again a valuation
subring of `K`, the *composite* of the two valuation rings:

- `ValuationSubring.comapResidue`: the composite valuation subring `C ⊆ K`;
- `ValuationSubring.mem_comapResidue_of_not_isUnit`: `C` contains the maximal ideal
  `𝔪'` of `A`;
- `ValuationSubring.residueRestrict`: the residue map of `A` restricted to `C` and
  corestricted to `A''`;
- `ValuationSubring.residueRestrictEquiv`: the resulting identification `C/𝔪' ≅ A''`.
-/

@[expose] public section

namespace ValuationSubring

open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K)
  (A'' : ValuationSubring (ResidueField A))

/-- The residue of a non-unit of `A` is `0`, hence lies in every valuation subring of the
residue field. -/
theorem residue_mem_of_not_isUnit {a : A} (h : ¬IsUnit a) : residue A a ∈ A'' := by
  rw [(residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr (_root_.mem_nonunits_iff.mpr h))]
  exact zero_mem _

/-- The underlying subring of the composite of two valuation rings: the preimage in `A` of
`A''` under the residue map, viewed inside `K`. -/
def comapResidueSubring : Subring K :=
  (A''.toSubring.comap (residue A)).map A.subtype

/-- An element of `K` lies in `ValuationSubring.comapResidueSubring` exactly if it lies in
`A` and its residue lies in `A''`. -/
theorem mem_comapResidueSubring {x : K} :
    x ∈ A.comapResidueSubring A'' ↔ ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ A'' where
  mp h := by
    obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp h
    exact ⟨a.2, ha⟩
  mpr := fun ⟨hx, hres⟩ ↦ Subring.mem_map.mpr ⟨⟨x, hx⟩, hres, rfl⟩

/-- The preimage in `A` of a valuation subring of the residue field satisfies the
valuation-subring criterion. -/
theorem mem_or_inv_mem_comapResidueSubring (x : K) :
    x ∈ A.comapResidueSubring A'' ∨ x⁻¹ ∈ A.comapResidueSubring A'' := by
  by_cases hxA : x ∈ A
  · by_cases hres : residue A ⟨x, hxA⟩ ∈ A''
    · exact Or.inl ((A.mem_comapResidueSubring A'').mpr ⟨hxA, hres⟩)
    -- `x` is a unit of `A`, else its residue would be `0 ∈ A''`
    have hunit : IsUnit (⟨x, hxA⟩ : A) := by
      by_contra hnu
      exact hres (A.residue_mem_of_not_isUnit A'' hnu)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hunit.ne_zero rfl
    have hxinvA : x⁻¹ ∈ A := A.toSubring.inv_mem_of_isUnit hxA hunit
    refine Or.inr ((A.mem_comapResidueSubring A'').mpr ⟨hxinvA, ?_⟩)
    have hmulA : (⟨x, hxA⟩ : A) * ⟨x⁻¹, hxinvA⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    have hmul : residue A ⟨x, hxA⟩ * residue A ⟨x⁻¹, hxinvA⟩ = 1 := by
      rw [← map_mul, hmulA, map_one]
    have hinv : residue A ⟨x⁻¹, hxinvA⟩ = (residue A ⟨x, hxA⟩)⁻¹ :=
      (inv_eq_of_mul_eq_one_right hmul).symm
    rcases A''.mem_or_inv_mem (residue A ⟨x, hxA⟩) with h | h
    · exact absurd h hres
    · rwa [hinv]
  -- `x⁻¹` lies in the maximal ideal of `A`, so its residue is `0 ∈ A''`
  have hxinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
  have hnu : ¬IsUnit (⟨x⁻¹, hxinv⟩ : A) := fun hu ↦ by
    have hmem := A.toSubring.inv_mem_of_isUnit hxinv hu
    rw [inv_inv] at hmem
    exact hxA hmem
  exact Or.inr ((A.mem_comapResidueSubring A'').mpr
    ⟨hxinv, A.residue_mem_of_not_isUnit A'' hnu⟩)

/-- **The composite of two valuation rings**: the preimage in a valuation subring
`A ⊆ K` of a valuation subring `A''` of the residue field of `A` is a valuation subring
of `K`. (Blueprint: `lemma:nagata-composite-valuation-ring`.) -/
def comapResidue : ValuationSubring K where
  __ := A.comapResidueSubring A''
  mem_or_inv_mem' := A.mem_or_inv_mem_comapResidueSubring A''

/-- An element of `K` lies in the composite valuation ring exactly if it lies in `A` and
its residue lies in `A''`. -/
@[simp]
theorem mem_comapResidue {x : K} :
    x ∈ A.comapResidue A'' ↔ ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ A'' :=
  A.mem_comapResidueSubring A''

/-- The composite valuation ring is contained in `A`. -/
theorem comapResidue_le : A.comapResidue A'' ≤ A := fun _ hx ↦
  ((A.mem_comapResidue A'').mp hx).1

/-- The composite valuation ring contains the maximal ideal of `A`. -/
theorem mem_comapResidue_of_not_isUnit {x : K} (hx : x ∈ A)
    (h : ¬IsUnit (⟨x, hx⟩ : A)) : x ∈ A.comapResidue A'' :=
  (A.mem_comapResidue A'').mpr ⟨hx, A.residue_mem_of_not_isUnit A'' h⟩


/-- The residue map of `A` sends the composite valuation ring into `A''`. -/
theorem residue_inclusion_mem (c : A.comapResidue A'') :
    residue A (inclusion _ _ (A.comapResidue_le A'') c) ∈ A'' :=
  ((A.mem_comapResidue A'').mp c.2).2

/-- The residue map of the composite valuation ring onto the second factor: the
restriction of the residue map of `A` along the inclusion `C ⊆ A`, corestricted
to `A''`. -/
noncomputable def residueRestrict : A.comapResidue A'' →+* A'' :=
  ((residue A).comp (inclusion _ _ (A.comapResidue_le A''))).codRestrict A''
    (A.residue_inclusion_mem A'')

/-- The residue map of the composite valuation ring onto `A''` is surjective. -/
theorem residueRestrict_surjective : Function.Surjective (A.residueRestrict A'') := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A) b
  exact ⟨⟨(a : K), (A.mem_comapResidue A'').mpr ⟨a.2, by rwa [ha]⟩⟩, Subtype.ext ha⟩

/-- The kernel of the residue map of the composite valuation ring is the trace of the
maximal ideal of `A`. -/
theorem ker_residueRestrict :
    RingHom.ker (A.residueRestrict A'') =
      (maximalIdeal A).comap (inclusion _ _ (A.comapResidue_le A'')) := by
  ext c
  rw [RingHom.mem_ker, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Subtype.ext_iff]
  rfl

/-- **The composite of two valuation rings has second factor `A''`**: the quotient of the
composite `C` by the trace of the maximal ideal of `A` is `A''`. This is the
identification `C/𝔪' ≅ A''` of `lemma:nagata-composite-valuation-ring`. -/
noncomputable def residueRestrictEquiv :
    (A.comapResidue A'' ⧸ (maximalIdeal A).comap
      (inclusion _ _ (A.comapResidue_le A''))) ≃+* A'' :=
  (Ideal.quotEquivOfEq (A.ker_residueRestrict A'').symm).trans
    (RingHom.quotientKerEquivOfSurjective (A.residueRestrict_surjective A''))

end ValuationSubring
