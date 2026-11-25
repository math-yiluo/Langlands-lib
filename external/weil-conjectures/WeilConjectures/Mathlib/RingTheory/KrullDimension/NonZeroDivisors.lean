/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Krull dimension of quotients of domains

Quotienting a domain by a nonzero ideal lowers the Krull dimension by at least one.
-/

@[expose] public section

open scoped nonZeroDivisors in
/-- Quotienting a domain by a nonzero ideal lowers the Krull dimension. -/
theorem ringKrullDim_quotient_add_one_le_of_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    {I : Ideal R} (hI : I ≠ ⊥) : ringKrullDim (R ⧸ I) + 1 ≤ ringKrullDim R := by
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_of_ne_zero hx0))
  gcongr
  exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
    ((Ideal.span_singleton_le_iff_mem _).2 hxI))

end
