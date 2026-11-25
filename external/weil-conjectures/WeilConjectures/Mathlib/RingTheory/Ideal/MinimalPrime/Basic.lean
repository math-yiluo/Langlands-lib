/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Minimal primes of reduced rings

- `Ideal.eq_zero_of_forall_mem_minimalPrimes`: in a reduced ring, an element lying in every
  minimal prime is zero.
-/

@[expose] public section

/-- In a reduced ring, an element lying in every minimal prime is zero. -/
theorem Ideal.eq_zero_of_forall_mem_minimalPrimes {A : Type*} [CommRing A] [IsReduced A]
    (x : A) (hx : ∀ P ∈ minimalPrimes A, x ∈ P) : x = 0 := by
  have : x ∈ sInf (minimalPrimes A) := Submodule.mem_sInf.2 fun P hP ↦ hx P hP
  rw [minimalPrimes, Ideal.sInf_minimalPrimes] at this
  obtain ⟨n, hn⟩ := this
  exact IsReduced.eq_zero x ⟨n, by simpa using hn⟩
