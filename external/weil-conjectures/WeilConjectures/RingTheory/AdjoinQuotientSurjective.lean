/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Surjectivity of a quotient killing the generators of an adjoin

Source: Stacks Project, Algebra, Tag 0334, Step 5.
(blueprint: lem-weil-pbc-adjoin-quotient-surjective).
-/

@[expose] public section

universe u v

/-- Killing every generator of an adjoin leaves a quotient of the base ring.

Source: Stacks Project, Algebra, Tag 0334, Step 5, the surjectivity in the
presentation `R[x]/xR[x] = R/J`, generalized to a set of generators.
(blueprint: lem-weil-pbc-adjoin-quotient-surjective).

Proof: Lift a quotient class to the adjoin. Induct on its membership in the
adjoin: a generator maps to zero by hypothesis; a constant lifts to itself;
sums and products lift by taking sums and products of the chosen constants.
The empty generating set gives the same constant case, and the zero quotient
is covered by the same induction. -/
theorem adjoin_quotient_surjective (R : Type u) (K : Type v)
    [CommRing R] [CommRing K] [Algebra R K] (s : Set K)
    (q : Ideal (Algebra.adjoin R s))
    (hs : ∀ x (hx : x ∈ s), (⟨x, Algebra.subset_adjoin hx⟩ :
      Algebra.adjoin R s) ∈ q) :
    Function.Surjective (algebraMap R (Algebra.adjoin R s ⧸ q)) := by
  intro y
  obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    exact ⟨0, by simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr (hs y hy)).symm⟩
  | algebraMap r => exact ⟨r, rfl⟩
  | add y z hy hz iy iz =>
    obtain ⟨a, ha⟩ := iy
    obtain ⟨b, hb⟩ := iz
    refine ⟨a + b, ?_⟩
    change _ = (Ideal.Quotient.mk q) (⟨y, hy⟩ + ⟨z, hz⟩)
    rw [map_add, map_add, ha, hb]
  | mul y z hy hz iy iz =>
    obtain ⟨a, ha⟩ := iy
    obtain ⟨b, hb⟩ := iz
    refine ⟨a * b, ?_⟩
    change _ = (Ideal.Quotient.mk q) (⟨y, hy⟩ * ⟨z, hz⟩)
    rw [map_mul, map_mul, ha, hb]

