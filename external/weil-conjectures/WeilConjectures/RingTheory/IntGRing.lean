/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.DVRCompletionRegular
import WeilConjectures.RingTheory.IntegerPrimeLocalizations
import WeilConjectures.RingTheory.LocalizationRegular
import Mathlib.Algebra.CharP.Algebra

/-!
# The integers are a G-ring

Source: Stacks Project, More on Algebra, Proposition 07PX, item (3)
(blueprint: lem-weil-pbc-z-g-ring).
-/

@[expose] public section

namespace Int

/-- The ring of integers is a G-ring. Source: Stacks Project, More on Algebra,
Proposition 07PX, item (3) (blueprint: lem-weil-pbc-z-g-ring).

Proof:
1. The integers are Noetherian. Their localization at the zero prime is the field of
   rationals, and at every nonzero prime it is a discrete valuation ring
   (`lem-weil-pbc-z-localizations-dvr`). By `theorem-finite-etale-covers-proper-henselian--2`, it
   suffices to check regularity of the completion map for each of these localizations.
2. At the zero prime the maximal ideal is zero and completion is the field itself.
   Its identity map is flat, and its only fibre is a field, hence geometrically regular:
   after any finite purely inseparable field extension the fibre is again a field
   (`lem-weil-pbc-field-regular-ring`). Thus this completion map is regular.
3. At every nonzero prime the localization is a Noetherian local discrete valuation
   ring with fraction field of characteristic zero. Its completion map is regular by
   `lem-weil-pbc-dvr-completion-regular`: completion is flat (Stacks 00MB) and is a DVR
   (Stacks 0AP1); the generic fibre is its fraction field, geometrically regular over
   the rationals in characteristic zero, and the closed fibre is the residue field.
4. These cases cover every prime of the integers. Hence all completion maps in the
   definition of `IsGRing` are regular, giving the claim. -/
theorem isGRing : IsGRing ℤ := by
  refine ⟨inferInstance, ?_⟩
  intro p hp
  by_cases h : p = ⊥
  · subst p
    obtain ⟨e⟩ := prime_localizations_dvr.2.2.2.2.1
    let A := Localization.AtPrime (⊥ : Ideal ℤ)
    let : Field A := (e.toRingEquiv.toMulEquiv.isField (Field.toIsField ℚ)).toField
    have hm : IsLocalRing.maximalIdeal A = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    have : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
      rw [hm]
      infer_instance
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    have hb : Function.Bijective (algebraMap A C) := by
      exact (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal A)).bijective
    have : IsLocalization (⊥ : Submonoid A) C :=
      IsLocalization.of_le_isUnit_of_bijective (by
        rintro x ⟨y, hy, rfl⟩
        have : y = 1 := hy
        simp [this]) hb
    exact (IsLocalization.isRegular_and_fiber (⊥ : Submonoid A)).1
  · let A := Localization.AtPrime p
    have : IsDiscreteValuationRing A := (prime_localizations_dvr.2.2.2.2.2 p h).2.2.1
    have : CharZero A := charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective ℤ A)
    have : CharZero (FractionRing A) := IsFractionRing.charZero_of_isFractionRing A
    exact AdicCompletion.isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero
      A (FractionRing A)

end Int
