/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Krull dimension along an integral extension

An injective integral ring extension `R → S` preserves the Krull dimension: contracting a strict
chain of primes of `S` gives a strict chain of primes of `R` (incomparability), and a chain of
primes of `R` lifts to `S` by lying over and going up.

## Main statements

- `ringKrullDim_le_of_isIntegral`: `dim S ≤ dim R` for an integral extension.
- `ringKrullDim_eq_of_isIntegral`: `dim R = dim S` for an injective integral extension.
-/

@[expose] public section

/-- An integral algebra `S` over `R` has Krull dimension at most that of `R`: contracting a strict
chain of primes of `S` gives a strict chain of primes of `R` (incomparability). -/
theorem ringKrullDim_le_of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    fun _ _ h ↦ Ideal.IsIntegral.under_lt_under (R := R) h

/-- An injective integral extension `R → S` preserves the Krull dimension:
`dim S = dim R` (Stacks `00OK`). Incomparability bounds `dim S ≤ dim R`, and lying over together
with going up lifts every chain of primes of `R` to `S`.
(blueprint: `lem-weil-pbc-integral-injective-dimension-equal`) -/
theorem ringKrullDim_eq_of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R := by
  refine le_antisymm (ringKrullDim_le_of_isIntegral R S) ?_
  refine iSup_le fun l ↦ ?_
  obtain ⟨P, hP⟩ := Ideal.nonempty_primesOver (S := S) l.head.asIdeal
  have := hP.1
  have := hP.2
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact hL ▸ Order.LTSeries.length_le_krullDim L
