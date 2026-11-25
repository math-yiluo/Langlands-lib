/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Formal smoothness for an adic topology

Source: Stacks Project, More on Algebra, Definition 15.38.1 (Tag 07EB),
Lemma 15.38.2 (Tag 07EC), and Definition 15.38.3 (Tag 07NI)
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v

namespace Algebra

/-- Let `R → S` be a map of commutative rings and `n` an ideal of `S`. The algebra `S`
is formally smooth over `R` for the `n`-adic topology if every `R`-algebra map
`g : S → D/J` killing some positive power of `n` lifts across each square-zero ideal
`J` of every commutative `R`-algebra `D` (Stacks, Tags 07EB and 07NI).
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

The power condition says that `g` is continuous from the `n`-adic topology to the
discrete topology (Tag 07E9). Any lift `f` kills `n ^ (2 * k)` if `g` kills `n ^ k`:
`f(n ^ k) ⊆ J`, so `f(n ^ (2 * k)) ⊆ J ^ 2 = 0` (Tag 07EC). Thus every lift is
continuous, as required by the topological definition in Tag 07EB. -/
def FormallySmoothAdic (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] (n : Ideal S) : Prop :=
  ∀ ⦃D : Type (max u v)⦄ [CommRing D] [Algebra R D] (J : Ideal D), J ^ 2 = ⊥ →
    ∀ g : S →ₐ[R] D ⧸ J,
      (∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, g x = 0) →
        ∃ f : S →ₐ[R] D, (Ideal.Quotient.mkₐ R J).comp f = g

end Algebra
