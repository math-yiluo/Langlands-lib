/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatExtendScalars
public import WeilConjectures.NumberTheory.Padics.IntegersModPow

/-!

# The inclusion of the ring of integers `𝒪_E` into `ℚ̄_ℓ` is flat

For a subfield `E` of `ℚ̄_ℓ = PadicAlgCl ℓ` with ring of integers `𝒪_E = PadicAlgCl.integers ℓ E`,
this file defines the ring morphism `PadicAlgCl.integersToULift : Shrink 𝒪_E →+* ULift ℚ̄_ℓ`
between the universe `u + 1` copies of `𝒪_E` and `ℚ̄_ℓ` (the coefficient rings of sheaves on a
`u`-site), and proves that it is flat when `𝒪_E` is a Dedekind domain
(`PadicAlgCl.flat_integersToULift`): `ℚ̄_ℓ` is a torsion-free `𝒪_E`-module. It induces the
derived extension of scalars `ℚ̄_ℓ ⊗ᴸ_{𝒪_E} - : D(𝒪_E) ⥤ D(ℚ̄_ℓ)`
(`ModuleCat.derivedExtendScalars`).

-/

@[expose] public section

universe u

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The inclusion `𝒪_E ⟶ ℚ̄_ℓ`, between the universe `u + 1` copies `Shrink 𝒪_E` and
`ULift ℚ̄_ℓ`. -/
noncomputable def integersToULift :
    Shrink.{u + 1} (integers ℓ E) →+* ULift.{u + 1} (PadicAlgCl ℓ) :=
  ULift.ringEquiv.symm.toRingHom.comp ((algebraMap E (PadicAlgCl ℓ)).comp
    ((integers ℓ E).subtype.comp (shrinkRingEquiv ℓ E).symm.toRingHom))

lemma integersToULift_injective : Function.Injective (integersToULift.{u} ℓ E) := by
  intro a b h
  apply (shrinkRingEquiv ℓ E).symm.injective
  apply Subtype.val_injective
  apply (algebraMap E (PadicAlgCl ℓ)).injective
  exact congrArg ULift.down h

/-- The inclusion `𝒪_E ⟶ ℚ̄_ℓ` is flat, `𝒪_E` being a Dedekind domain and `ℚ̄_ℓ` a torsion-free
`𝒪_E`-module. -/
lemma flat_integersToULift [IsDedekindDomain (Shrink.{u + 1} (integers ℓ E))] :
    (integersToULift.{u} ℓ E).Flat := by
  algebraize [integersToULift.{u} ℓ E]
  rw [RingHom.Flat, IsDedekindDomain.flat_iff_torsion_eq_bot]
  refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
  obtain ⟨⟨r, hr⟩, hrx⟩ := (Submodule.mem_torsion_iff x).1 hx
  have hr0 : integersToULift.{u} ℓ E r ≠ 0 := by
    rw [ne_eq, ← map_zero (integersToULift.{u} ℓ E)]
    exact fun h ↦ nonZeroDivisors.ne_zero hr ((integersToULift_injective ℓ E) h)
  have : integersToULift.{u} ℓ E r * x = 0 := hrx
  exact (mul_eq_zero.1 this).resolve_left hr0

end PadicAlgCl

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The prime `ℓ` lies in the maximal ideal of `𝒪_E`: it is not a unit, its image in `ℚ̄_ℓ` having
norm `ℓ⁻¹ < 1`. -/
lemma natCast_mem_maximalIdeal_shrink [IsLocalRing (Shrink.{u + 1} (integers ℓ E))] :
    (ℓ : Shrink.{u + 1} (integers ℓ E)) ∈ IsLocalRing.maximalIdeal _ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨w, hw⟩
  have h1 : integersToULift.{u} ℓ E (w * ↑w⁻¹) = 1 := by rw [Units.mul_inv, map_one]
  rw [hw, map_mul, map_natCast] at h1
  have h2 : ‖(ℓ : PadicAlgCl ℓ)‖ * ‖(integersToULift.{u} ℓ E ↑w⁻¹).down‖ = 1 := by
    rw [← norm_mul]
    simpa using congrArg (fun a ↦ ‖ULift.down a‖) h1
  have hw' : ‖(integersToULift.{u} ℓ E ↑w⁻¹).down‖ ≤ 1 :=
    ((shrinkRingEquiv ℓ E).symm ↑w⁻¹).2
  rw [← map_natCast (algebraMap E (PadicAlgCl ℓ)), norm_algebraMap_natCast_self] at h2
  have hl : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have : (ℓ : ℝ)⁻¹ * ‖(integersToULift.{u} ℓ E ↑w⁻¹).down‖ < 1 :=
    calc _ ≤ (ℓ : ℝ)⁻¹ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hl
  linarith

end PadicAlgCl
