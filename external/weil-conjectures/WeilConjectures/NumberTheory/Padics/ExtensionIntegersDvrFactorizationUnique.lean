/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! Uniqueness for the unit-times-integer-power factorization in a DVR.

Source: Stacks Project, Algebra, Lemma 00PD.
(auxiliary; not a blueprint node)
-/

@[expose] public section

namespace Padic

/-- The unit and integer exponent in a DVR fraction-field factorization are unique.

Source: Stacks Project, Algebra, Lemma 00PD.
Proof: compare two expressions after clearing denominators.  The DVR factorization
of nonzero elements and uniqueness of the exponent in a product of powers of an
irreducible force the two integer exponents to agree; cancellation in the domain then
forces the units to agree.
(auxiliary; not a blueprint node)
-/
theorem extension_integers_dvr_factorization_unique (E : Type*) [Field E] (O : Subring E)
    (m : Ideal O) (hDVR : IsDiscreteValuationRing O) (hmax : m.IsMaximal)
    (hfrac : IsFractionRing O E) :
    ∀ π : O, Ideal.span ({π} : Set O) = m → ∀ x : Eˣ,
      ∀ p q : Oˣ × ℤ,
        (x : E) = ((p.1 : O) : E) * (π : E) ^ p.2 →
        (x : E) = ((q.1 : O) : E) * (π : E) ^ q.2 → p = q := by
  have : IsDiscreteValuationRing O := hDVR
  have : IsFractionRing O E := hfrac
  intro π hπ x p q hp hq
  have hπi : Irreducible π := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
    rw [← IsLocalRing.eq_maximalIdeal hmax, hπ]
  have hπunit : IsUnit (algebraMap O E π) :=
    IsLocalization.map_units E ⟨π, mem_nonZeroDivisors_of_ne_zero hπi.ne_zero⟩
  let πE : Eˣ := hπunit.unit
  have hπE : (πE : E) = algebraMap O E π := hπunit.unit_spec
  have hp_exp : p.2 = q.2 := by
    have hpo := Ring.ordOf_units_eq (R := O) (L := E) hπi p.1 p.2 πE hπE
    have hqo := Ring.ordOf_units_eq (R := O) (L := E) hπi q.1 q.2 πE hπE
    have heq : Ring.ordOf O E (x : E) = p.2 := by
      rw [hp]
      have hpo' := hpo
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hπE] at hpo'
      change Ring.ordOf O E (((p.1 : O) : E) * (π : E) ^ p.2) = p.2 at hpo'
      exact hpo'
    have heq' : Ring.ordOf O E (x : E) = q.2 := by
      rw [hq]
      have hqo' := hqo
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hπE] at hqo'
      change Ring.ordOf O E (((q.1 : O) : E) * (π : E) ^ q.2) = q.2 at hqo'
      exact hqo'
    exact heq.symm.trans heq'
  apply Prod.ext
  · apply Units.ext
    apply Subtype.ext
    apply mul_right_cancel₀ (zpow_ne_zero (a := (π : E)) p.2 (by
      exact_mod_cast hπi.ne_zero))
    calc
      ((p.1 : O) : E) * (π : E) ^ p.2 = (x : E) := hp.symm
      _ = ((q.1 : O) : E) * (π : E) ^ q.2 := hq
      _ = ((q.1 : O) : E) * (π : E) ^ p.2 := by rw [hp_exp]
  · exact hp_exp

end Padic
