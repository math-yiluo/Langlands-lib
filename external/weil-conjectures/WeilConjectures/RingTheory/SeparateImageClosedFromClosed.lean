/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Separating a closed set from the closure of an image in a prime spectrum

Source: Stacks Project, More on Algebra, Lemma Tag 07M3
(blueprint: lem-weil-pbc-separate-image-closed-from-closed).
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

/-- Stacks Project, More on Algebra, Lemma Tag 07M3
(blueprint: lem-weil-pbc-separate-image-closed-from-closed).
If the closure of the image of `V(J)` is disjoint from `V(I)`, an element of `R`
can be chosen to equal one modulo `I` and to map into `J`.

Proof:
1. Set `I' = J.comap φ`. The closure of the image of `V(J)` is `V(I')`, by
   `lem-weil-pbc-closure-image-spec-zero-locus`
   (`PrimeSpectrum.closure_image_comap_zeroLocus`).
2. Disjointness gives `I + I' = R`, by
   `lem-weil-pbc-spec-zero-loci-disjoint-unit-ideal`
   (the zero-locus identities for a sum of ideals and for the unit ideal). Thus write
   `1 = g + f` with `g ∈ I` and `f ∈ I'`.
3. Since `f = 1 - g`, its image modulo `I` is one; membership in `I'` says
   `φ f ∈ J`. This choice of `I'` avoids the power replacement in the original Stacks proof.
-/
theorem exists_one_mod_mem_of_disjoint_closure_image_zeroLocus
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (h : Disjoint (closure (comap φ '' zeroLocus (J : Set S)))
      (zeroLocus (I : Set R))) :
    ∃ f : R, Ideal.Quotient.mk I f = 1 ∧ φ f ∈ J := by
  rw [closure_image_comap_zeroLocus] at h
  have hc : IsCoprime I (J.comap φ) := by
    apply Ideal.coprime_of_no_prime_ge
    intro P hIP hJP hprime
    apply Set.disjoint_left.1 h
    · exact (mem_zeroLocus ⟨P, hprime⟩ _).mpr hJP
    · exact (mem_zeroLocus ⟨P, hprime⟩ _).mpr hIP
  obtain ⟨g, hg, f, hf, hgf⟩ := hc.exists
  refine ⟨f, ?_, hf⟩
  have eq := congrArg (Ideal.Quotient.mk I) hgf
  simpa [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hg] using eq

end PrimeSpectrum
