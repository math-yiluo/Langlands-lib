/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Regular elements and associated primes

* `exists_mem_maximalIdeal_isSMulRegular`: over a noetherian local ring, a finite module of
  which the maximal ideal is not an associated prime has a regular element in the maximal ideal.
* `Module.injective_pi_localizedModule_associatedPrimes`: over a noetherian ring, a module
  embeds into the product of its localizations at its associated primes.
-/

@[expose] public section

open IsLocalRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherianRing R]

/-- Over a noetherian local ring `R`, if the maximal ideal is not an associated prime of the
finite module `M`, some element of the maximal ideal is `M`-regular (prime avoidance).
(blueprint: `lem-weil-pbc-nonzerodivisor-if-maximal-not-associated`) -/
theorem exists_mem_maximalIdeal_isSMulRegular [IsLocalRing R] [Module.Finite R M]
    (h : maximalIdeal R ∉ associatedPrimes R M) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  cases subsingleton_or_nontrivial M
  · exact ⟨0, zero_mem _, IsSMulRegular.zero⟩
  by_contra! H
  obtain ⟨I, hI⟩ := associatedPrimes.nonempty R M
  have hsub : (maximalIdeal R : Set R) ⊆ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact fun r hr ↦ H r hr
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite R M) I I
    fun J hJ _ _ ↦ hJ.isPrime).mp hsub
  exact h ((IsLocalRing.le_maximalIdeal hp.isPrime.ne_top).antisymm hle ▸ hp)

/-- Over a noetherian ring, an element of a module which vanishes in the localization at every
associated prime is zero. -/
theorem Module.eq_zero_of_forall_associatedPrimes {m : M}
    (h : ∀ p ∈ associatedPrimes R M, ∃ s ∉ p, s • m = 0) : m = 0 := by
  by_contra hm
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R m hm
  obtain ⟨s, hs, hsm⟩ := h P hP
  exact hs (hle (by simpa [Submodule.mem_colon_singleton] using hsm))

/-- Over a noetherian ring, a module embeds into the product of its localizations at its
associated primes. (blueprint: `lem-weil-pbc-module-injects-localizations-associated-primes`) -/
theorem Module.injective_pi_localizedModule_associatedPrimes :
    Function.Injective (LinearMap.pi fun p : associatedPrimes R M ↦
      LocalizedModule.mkLinearMap p.1.primeCompl M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  refine Module.eq_zero_of_forall_associatedPrimes (R := R) fun p hp ↦ ?_
  have := congr_fun hm ⟨p, hp⟩
  simp only [LinearMap.pi_apply, LocalizedModule.mkLinearMap_apply, Pi.zero_apply] at this
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at this
  obtain ⟨⟨s, hs⟩, hsm⟩ := this
  exact ⟨s, hs, by simpa using hsm⟩
