/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.CompletionOfDVR
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!

# The completion of a strictly henselian discrete valuation ring

For a discrete valuation ring `R`, the `𝔪`-adic completion `R̂ = AdicCompletion (maximalIdeal R) R`
is a complete discrete valuation ring (`AdicCompletion.isDiscreteValuationRing`), henselian
(`IsAdicComplete.henselianRing`), with the same residue field
(`AdicCompletion.residueField_map_bijective`). If `R` is strictly henselian, so is `R̂`. The map
`R ⟶ R̂` is injective, local and unramified (`maximalIdeal R̂ = (maximalIdeal R) R̂`).

We record these as instances on the abbreviation `IsDiscreteValuationRing.completion R`, and
give the extension `b̂ : R̂ ⟶ κ` of a map `b : R ⟶ κ` with kernel the maximal ideal.

-/

@[expose] public section

universe u

open IsLocalRing

namespace IsDiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The `𝔪`-adic completion of a discrete valuation ring. -/
abbrev completion : Type u := AdicCompletion (maximalIdeal R) R

noncomputable instance completion.isDomain : IsDomain (completion R) :=
  (AdicCompletion.isDiscreteValuationRing R).choose

instance completion.isDiscreteValuationRing : IsDiscreteValuationRing (completion R) :=
  (AdicCompletion.isDiscreteValuationRing R).choose_spec

instance completion.henselianLocalRing : HenselianLocalRing (completion R) where
  is_henselian f hf a₀ h₁ h₂ := by
    have := (IsAdicComplete.henselianRing (completion R) (maximalIdeal (completion R))).is_henselian
      f hf a₀ h₁ (h₂.map _)
    exact this

/-- The map `R ⟶ R̂` to the completion. -/
noncomputable abbrev toCompletion : R →+* completion R := algebraMap R (completion R)

lemma injective_toCompletion : Function.Injective (toCompletion R) := by
  have : IsHausdorff (maximalIdeal R) R := inferInstance
  intro x y h
  exact AdicCompletion.of_injective (maximalIdeal R) R
    (by simpa [AdicCompletion.algebraMap_apply] using h)

lemma maximalIdeal_completion :
    maximalIdeal (completion R) = (maximalIdeal R).map (toCompletion R) :=
  AdicCompletion.maximalIdeal_eq_map

instance completion.isStrictlyHenselianLocalRing [IsStrictlyHenselianLocalRing R] :
    IsStrictlyHenselianLocalRing (completion R) where
  isSepClosed_residueField :=
    IsSepClosed.of_ringEquiv (RingEquiv.ofBijective _
      (AdicCompletion.residueField_map_bijective R))

/-- A map `b : R ⟶ κ` with kernel the maximal ideal extends to the completion. -/
noncomputable def completionLift {κ : Type u} [Field κ] (b : R →+* κ)
    (hb : RingHom.ker b = maximalIdeal R) : completion R →+* κ :=
  ((Ideal.Quotient.lift (maximalIdeal R) b fun a ha ↦ by rwa [← RingHom.mem_ker, hb]).comp
    (RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective R)).symm.toRingHom).comp
    (residue (completion R))

lemma completionLift_apply {κ : Type u} [Field κ] (b : R →+* κ)
    (hb : RingHom.ker b = maximalIdeal R) (z : completion R) :
    completionLift R b hb z = Ideal.Quotient.lift (maximalIdeal R) b
      (fun a ha ↦ by rwa [← RingHom.mem_ker, hb])
      ((RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective R)).symm
        (residue (completion R) z)) := rfl

lemma completionLift_comp {κ : Type u} [Field κ] (b : R →+* κ)
    (hb : RingHom.ker b = maximalIdeal R) :
    (completionLift R b hb).comp (toCompletion R) = b := by
  ext r
  rw [RingHom.comp_apply, completionLift_apply]
  have : residue (completion R) (toCompletion R r) =
      RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective R) (residue R r) :=
    (ResidueField.map_residue _ r).symm
  rw [this, RingEquiv.symm_apply_apply]
  rfl

lemma ker_completionLift {κ : Type u} [Field κ] (b : R →+* κ)
    (hb : RingHom.ker b = maximalIdeal R) :
    RingHom.ker (completionLift R b hb) = maximalIdeal (completion R) := by
  ext z
  rw [RingHom.mem_ker, completionLift_apply, ← IsLocalRing.residue_eq_zero_iff]
  obtain ⟨r, hr⟩ := (RingEquiv.ofBijective _
    (AdicCompletion.residueField_map_bijective R)).surjective (residue (completion R) z)
  rw [← hr, RingEquiv.symm_apply_apply]
  obtain ⟨s, rfl⟩ := residue_surjective r
  rw [map_eq_zero_iff _ (RingEquiv.injective _)]
  change b s = 0 ↔ residue R s = 0
  rw [← RingHom.mem_ker, hb, IsLocalRing.residue_eq_zero_iff]

end IsDiscreteValuationRing
