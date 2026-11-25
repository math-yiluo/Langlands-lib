/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Associated primes as exact annihilators of elements

Mathlib's `associatedPrimes R M` consists of primes which are the *radical* of the annihilator of
an element (weakly associated primes). Over an arbitrary ring, the Stacks project
(Tag 00LA) instead calls a prime `q` associated to `M` if `q` is exactly the annihilator of
some element of `M`. We define this set as `Module.annihilatorAssociatedPrimes R M` and show it
agrees with `associatedPrimes R M` over a Noetherian ring.
-/

@[expose] public section

namespace Module

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The associated primes of an `R`-module `M` in the sense of Stacks Tag 00LA: the prime ideals
`q` of `R` such that `q = {a ∈ R | a • z = 0}` for some `z ∈ M`. No Noetherian hypothesis is
imposed. (blueprint: `def-weil-pbc-annihilator-associated-primes`) -/
def annihilatorAssociatedPrimes : Set (Ideal R) :=
  {q | q.IsPrime ∧ ∃ z : M, q = LinearMap.ker (LinearMap.toSpanSingleton R M z)}

variable {R M}

/-- Characterisation of `annihilatorAssociatedPrimes`: `q` is a prime ideal which is the exact
annihilator of some element `z ∈ M`.
(blueprint: `def-weil-pbc-annihilator-associated-primes`) -/
theorem mem_annihilatorAssociatedPrimes_iff {q : Ideal R} :
    q ∈ annihilatorAssociatedPrimes R M ↔ q.IsPrime ∧ ∃ z : M, ∀ a : R, a ∈ q ↔ a • z = 0 := by
  refine and_congr_right fun _ ↦ exists_congr fun z ↦ ?_
  rw [SetLike.ext_iff]
  simp

/-- Over a Noetherian ring, the associated primes in the sense of Stacks Tag 00LA agree with
Mathlib's `associatedPrimes`. -/
theorem annihilatorAssociatedPrimes_eq_associatedPrimes [IsNoetherianRing R] :
    annihilatorAssociatedPrimes R M = associatedPrimes R M := by
  ext q
  rw [mem_annihilatorAssociatedPrimes_iff, associatedPrimes, Set.mem_ofPred_eq,
    isAssociatedPrime_iff]
  refine and_congr_right fun _ ↦ exists_congr fun z ↦ ?_
  rw [SetLike.ext_iff]
  simp [Submodule.mem_colon_singleton]

end Module
