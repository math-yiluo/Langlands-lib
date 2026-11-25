/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Localization of a reduced ring at a minimal prime

- `Localization.AtPrime.isField_of_mem_minimalPrimes`: the localization of a reduced ring at a
  minimal prime is a field.
-/

@[expose] public section

/-- The localization of a reduced ring at a minimal prime is a field: its maximal ideal is the
radical of zero. -/
lemma Localization.AtPrime.isField_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsReduced A]
    {Q : Ideal A} (hQ : Q ∈ minimalPrimes A) :
    have := hQ.1.1
    IsField (Localization.AtPrime Q) := by
  have := hQ.1.1
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
    ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime Q) Q ⊥ hQ,
    Ideal.map_bot]
  exact nilradical_eq_zero _
