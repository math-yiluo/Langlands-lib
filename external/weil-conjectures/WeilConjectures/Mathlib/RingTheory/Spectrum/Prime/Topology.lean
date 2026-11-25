/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Spectral.Hom

/-!
# Complements on the topology of the prime spectrum

`PrimeSpectrum.exists_specializes_of_mem_closure_range_comap`: a prime in the closure of
the range of `PrimeSpectrum.comap f` is a specialization of a prime in that range. This is
the statement about prime spectra underlying Stacks Project Tag 02JQ, whose scheme-theoretic
form is `AlgebraicGeometry.exists_specializes_of_mem_closure_range`.

`PrimeSpectrum.mem_genericPoints_iff`: the generic points of the irreducible components of
`Spec R` are the minimal primes of `R`.

`PrimeSpectrum.isDomain_of_irreducibleSpace`: a reduced ring with irreducible spectrum is a
domain.

`PrimeSpectrum.connectedSpace_of_isIdempotentElem`: the spectrum of a nonzero ring whose only
idempotents are `0` and `1` is connected.

`PrimeSpectrum.vanishingIdeal_preimage_comap_of_isLocalization`: vanishing ideals of closed sets
commute with localization.
-/

@[expose] public section

namespace PrimeSpectrum

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- A prime in the closure of the range of `PrimeSpectrum.comap f` is a specialization of a
prime in the range: the closure of the range is the zero locus of `RingHom.ker f`, and a
prime containing `RingHom.ker f` is the contraction of some prime of `S` up to
specialization (Stacks Project Tag 00FK). -/
@[stacks 02JQ]
theorem exists_specializes_of_mem_closure_range_comap (f : R →+* S) {z : PrimeSpectrum R}
    (hz : z ∈ closure (Set.range (comap f))) : ∃ q : PrimeSpectrum S, comap f q ⤳ z := by
  rw [closure_range_comap, mem_zeroLocus, SetLike.coe_subset_coe] at hz
  obtain ⟨q, -, hq, hle⟩ := z.asIdeal.exists_ideal_comap_le_prime (f := f) ⊥
    (by rwa [← RingHom.ker_eq_comap_bot])
  exact ⟨⟨q, hq⟩, (le_iff_specializes _ z).mp hle⟩

/-- A point of `Spec R` is the generic point of an irreducible component if and only if the
corresponding prime ideal is a minimal prime of `R`. -/
@[stacks 00ES]
theorem mem_genericPoints_iff {p : PrimeSpectrum R} :
    p ∈ genericPoints (PrimeSpectrum R) ↔ p.asIdeal ∈ minimalPrimes R := by
  change closure ({p} : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) ↔ _
  rw [closure_singleton, zeroLocus_ideal_mem_irreducibleComponents, p.2.radical]

/-- A reduced ring whose spectrum is irreducible is a domain: the nilradical `⊥` is prime.
(blueprint: `lem-wf-affine-dimension-drop`, first claim) -/
theorem isDomain_of_irreducibleSpace (R : Type*) [CommRing R] [IsReduced R]
    [IrreducibleSpace (PrimeSpectrum R)] : IsDomain R := by
  have := irreducibleSpace_iff_isPrime_nilradical.mp ‹_›
  rw [nilradical_eq_zero] at this
  exact IsDomain.of_bot_isPrime R

/-- The spectrum of a nonzero ring whose only idempotents are `0` and `1` is connected: a clopen
subset of `Spec R` is `D(e)` for an idempotent `e`. -/
theorem connectedSpace_of_isIdempotentElem (R : Type*) [CommRing R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace (PrimeSpectrum R) := by
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun s hs ↦ ?_⟩
  obtain ⟨e, he, rfl⟩ := isClopen_iff.mp hs
  rcases h e he with rfl | rfl <;> simp

/-- The vanishing ideal of the preimage of a closed set of `Spec R` in the spectrum of a
localization `S` of `R` is the extension of its vanishing ideal. -/
theorem vanishingIdeal_preimage_comap_of_isLocalization {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    {Z : Set (PrimeSpectrum R)} (hZ : IsClosed Z) :
    vanishingIdeal (comap (algebraMap R S) ⁻¹' Z) = (vanishingIdeal Z).map (algebraMap R S) := by
  obtain ⟨I, rfl⟩ := (isClosed_iff_zeroLocus_ideal Z).mp hZ
  rw [preimage_comap_zeroLocus, ← zeroLocus_span, ← Ideal.map,
    vanishingIdeal_zeroLocus_eq_radical, vanishingIdeal_zeroLocus_eq_radical,
    IsLocalization.map_radical M]

/-- A nonempty open subset of the spectrum of a ring contains every point whose prime ideal
is zero, since such a point specializes to every point. -/
theorem mem_of_isOpen_of_asIdeal_eq_bot {R : Type*} [CommRing R]
    {W : Set (PrimeSpectrum R)} (hW : IsOpen W) (hne : W.Nonempty) {P : PrimeSpectrum R}
    (hP : P.asIdeal = ⊥) : P ∈ W := by
  obtain ⟨w, hw⟩ := hne
  refine ((le_iff_specializes P w).mp ?_).mem_open hW hw
  rw [← asIdeal_le_asIdeal, hP]
  exact bot_le

end PrimeSpectrum

/-! ### Ported from the `proetale` package
(`Proetale.Mathlib.RingTheory.Spectrum.Prime.Topology`) -/

-- end of file
theorem PrimeSpectrum.continuous_sigmaToPi {ι : Type*} (R : ι → Type*)
    [(i : ι) → CommSemiring (R i)] :
    Continuous (PrimeSpectrum.sigmaToPi R) :=
  continuous_sigma fun _ ↦ continuous_comap (Pi.evalRingHom R _)


theorem PrimeSpectrum.isSpectralMap_comap {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) : IsSpectralMap (PrimeSpectrum.comap f) where
  toContinuous := PrimeSpectrum.continuous_comap f
  isCompact_preimage_of_isOpen s hs hc := by
    obtain ⟨I, hI_fg, rfl⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hc, hs⟩
    rw [Set.preimage_compl, PrimeSpectrum.preimage_comap_zeroLocus]
    refine (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨_, hI_fg.map f, ?_⟩).1
    rw [← PrimeSpectrum.zeroLocus_span, Ideal.span_eq, ← Ideal.span_eq I, Ideal.map_span,
      PrimeSpectrum.zeroLocus_span, Ideal.span_eq]
