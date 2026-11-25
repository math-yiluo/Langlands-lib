/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.MinimalComponentDimensionMaximumData

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, proof of Tag 00P1, the prime-chain argument.
(blueprint: lem-weil-pbc-minimal-component-dimension-maximum).
The maximum dimension of the minimal components through a prime is the sum of the
local-ring dimension and the residue transcendence degree. This is a ring-theoretic
statement, before identifying that maximum with topological dimension at the point.

Proof: The quotient S/p is a finite type domain with fraction field kappa(p).
Tag 00P0 identifies its dimension with r, and Tag 00OS says that every maximal
prime chain in S/p has length r. Fix one such chain; its lift starts at p.
The ring S is Noetherian, so the set J of minimal primes q below p is finite
and nonempty. Localization identifies these with the minimal primes of S_p.
For each q in J choose a saturated chain from q to p of greatest length s(q).
These lengths exist: all such chains have length at most d, by the prime
correspondence and dim S_p = d. Conversely, every chain in S_p can be extended
at its bottom to a minimal prime and at its top to p. The supremum defining d
is attained because its lengths are natural numbers bounded by d; consequently
max s(q) = d. Concatenate each chosen chain with the fixed chain above p.
The resulting chain is maximal in S/q: it starts at its zero prime, ends at a
maximal ideal, and no insertion is possible, including at the joining prime p.
By Tag 00OS its length is dim S/q, hence dim S/q = s(q) + r.
Thus every component dimension is at most d+r, and a q attaining s(q)=d gives
equality. No topological dimension-at-point formula is used in this argument. -/
theorem minimal_component_dimension_maximum
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (d r : ℕ)
    (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞))
    (hr : Algebra.trdeg k p.ResidueField = (r : Cardinal.{v})) :
    (∀ q : Ideal S, q.IsPrime → q ≤ p →
      (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q) →
      ringKrullDim (S ⧸ q) ≤ ((d + r : ℕ) : WithBot ℕ∞)) ∧
    (∃ q : Ideal S, q.IsPrime ∧ q ≤ p ∧
      (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q) ∧
      ringKrullDim (S ⧸ q) = ((d + r : ℕ) : WithBot ℕ∞)) := by
  obtain ⟨qs, hqs, hne, hbound, hattain⟩ :=
    minimal_component_dimension_maximum_data (k := k) p d r hd hr
  constructor
  · intro q hq hqp hmin
    have hqmem : q ∈ qs := (hqs q).mpr ⟨hq, hqp, hmin⟩
    exact hbound q hqmem
  · obtain ⟨q, hq, hqeq⟩ := hattain
    obtain ⟨hprime, hbelow, hminimal⟩ := (hqs q).mp hq
    exact ⟨q, hprime, hbelow, hminimal, hqeq⟩

end AlgebraicGeometry
