/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizations of a polynomial ring at one element

A localization `κ[X][1/q]` of the polynomial ring over an infinite field at a single element is
never a field (`Polynomial.not_isField_localization_away`).
-/

@[expose] public section

universe u

open Polynomial

/-- A localization `κ[X][1/q]` of the polynomial ring over an infinite field at a single element
is never a field: if `q ≠ 0`, pick `a` with `q(a) ≠ 0`; evaluation at `a` extends to
`κ[X][1/q] → κ` and kills the nonzero element `X - a`. -/
theorem Polynomial.not_isField_localization_away {κ : Type u} [Field κ] [Infinite κ]
    (q : κ[X]) : ¬ IsField (Localization.Away q) := by
  classical
  intro hF
  by_cases hq : q = 0
  · subst hq
    have h0 : IsUnit (0 : Localization.Away (0 : κ[X])) := by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (0 : κ[X]))
        (0 : κ[X])
    obtain ⟨a, b, hab⟩ := hF.exists_pair_ne
    exact hab (subsingleton_of_zero_eq_one (isUnit_zero_iff.mp h0) |>.elim a b)
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset q.roots.toFinset
  have hqa : IsUnit (evalRingHom a q) := by
    rw [isUnit_iff_ne_zero, coe_evalRingHom]
    intro h
    exact ha (Multiset.mem_toFinset.mpr ((mem_roots hq).mpr h))
  let φ : Localization.Away q →+* κ := IsLocalization.Away.lift q hqa
  have hne : algebraMap κ[X] (Localization.Away q) (X - C a) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hq))]
    exact X_sub_C_ne_zero a
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
  have h1 := congrArg φ hy
  rw [map_mul, IsLocalization.Away.lift_eq, map_one] at h1
  simp at h1
