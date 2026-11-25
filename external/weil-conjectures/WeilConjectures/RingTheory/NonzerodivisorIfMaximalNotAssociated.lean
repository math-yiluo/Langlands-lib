/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Algebra.Regular.SMul
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# A nonzerodivisor in the maximal ideal

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00LL
(blueprint: lem-weil-pbc-nonzerodivisor-if-maximal-not-associated).
-/

@[expose] public section

universe u v

/-- (blueprint: lem-weil-pbc-nonzerodivisor-if-maximal-not-associated)
Let `R` be a Noetherian local commutative ring and `M` a finite `R`-module.
If the maximal ideal is not an associated prime of `M`, then it contains an
element acting injectively on `M`. "Not an associated prime" is Mathlib's
`associatedPrimes`; "nonzerodivisor on `M`" is `IsSMulRegular M x`.
Source: Algebra, Tag 00LL.

Proof (Stacks, Algebra, Tag 00LL, implication (2) => (1) for `I = m`):
the associated primes of `M` are finite. Every associated prime is proper,
thus is contained in the maximal ideal; the hypothesis excludes equality,
so the maximal ideal is contained in none of them. Prime avoidance supplies
an element of the maximal ideal outside their union (and `0` does so when
the union is empty). The union-of-associated-primes characterization of
zero divisors then shows that this element acts injectively on `M`.
-/
theorem exists_mem_maximalIdeal_smul_injective
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : IsLocalRing.maximalIdeal R ∉ associatedPrimes R M) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ IsSMulRegular M x := by
  classical
  by_contra! hn
  obtain ⟨p, hp, hmp⟩ :=
    (Ideal.subset_union_prime_finite (associatedPrimes.finite R M) (f := id) ⊥ ⊥
      (fun _ hp _ _ ↦ hp.isPrime)).mp (show
        (IsLocalRing.maximalIdeal R : Set R) ⊆ ⋃ p ∈ associatedPrimes R M, (p : Set R) by
      rw [biUnion_associatedPrimes_eq_compl_regular R M]
      exact hn)
  exact h ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hp.isPrime.ne_top hmp ▸ hp)
