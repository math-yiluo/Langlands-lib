/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Prime

/-!
# Associated primes defined by element annihilators

Source: Stacks Project, Algebra, Definition 00LA (definition-associated)
(blueprint: def-weil-pbc-annihilator-associated-primes).
-/

@[expose] public section

universe u v

namespace RingTheory

/-- The associated primes in the sense of Stacks Project, Algebra, Definition 00LA:
prime ideals equal to the annihilator of an element, with no radical and no Noetherian
hypothesis. The colon of the zero submodule by `{z}` is `{a | a • z = 0}`.
(blueprint: def-weil-pbc-annihilator-associated-primes). -/
def annihilatorAssociatedPrimes (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Set (Ideal R) :=
  {q | q.IsPrime ∧ ∃ z : M, q = (⊥ : Submodule R M).colon {z}}

end RingTheory
