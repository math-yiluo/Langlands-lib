/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

/-! # The signs in even-dimensional Poincare pairings

Source: corollary-cup-product-pairing--1, complement (iii), the Koszul-sign calculation.
(blueprint: lem-pd-trace-cup-signs).
-/

@[expose] public section
set_option autoImplicit false
universe u v

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupSigns

/-- In total degree 2d, the Koszul sign is the parity sign of the first degree.
This holds for negative cohomological degrees as well. Source: corollary-cup-product-pairing--1,
complement (iii) (blueprint: lem-pd-trace-cup-signs).
Proof: i(2d-i) is even exactly when i is even, by the parity rules for products
and differences. The power of -1 only depends on this parity. -/
theorem complement (d i : ℤ) :
    (-1 : ℤˣ) ^ (i * (2 * d - i)) = (-1 : ℤˣ) ^ i := by
  have h : Even (i * (2 * d - i)) ↔ Even i := by simp [parity_simps]
  simp only [neg_one_zpow_eq_ite, h]

/-- The middle-degree Koszul sign is (-1)^d, including d=0.
Source: corollary-cup-product-pairing--1, complement (iii) (blueprint: lem-pd-trace-cup-signs).
Proof: specialize the complementary-degree calculation to i=d and use the
agreement of natural and integer powers in the group of integer units. -/
theorem middle (d : ℕ) :
    (((-1 : ℤˣ) ^ ((d : ℤ) * (2 * (d : ℤ) - d)) : ℤˣ) : ℤ) = (-1 : ℤ) ^ d := by
  rw [complement]
  simp

/-- A skew value is zero over a characteristic-zero field. Source: corollary-cup-product-pairing--1,
complement (iii), final sentence (blueprint: lem-pd-trace-cup-signs).
Proof: v=-v implies 2v=0; the nonzero field scalar 2 acts injectively. -/
theorem eq_zero_of_eq_neg {R : Type u} [Field R] [CharZero R]
    {M : Type v} [AddCommGroup M] [Module R M] {v : M} (h : v = -v) : v = 0 := by
  have hv : (2 : R) • v = 0 := by
    simpa only [two_smul] using (eq_neg_iff_add_eq_zero.mp h)
  exact (smul_eq_zero.mp hv).resolve_left (by norm_num)

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupSigns
