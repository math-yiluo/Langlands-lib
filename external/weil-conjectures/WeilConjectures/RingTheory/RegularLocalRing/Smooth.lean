/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Smooth algebras over a field are regular

The localizations of a smooth algebra over a field at its primes are regular local rings
(`Algebra.Smooth.isRegularLocalRing_localization`), so that the algebra is a regular ring
(`Algebra.Smooth.isRegularRing`): locally the algebra is étale over a polynomial
ring, and étale maps preserve regularity.
-/

@[expose] public section

namespace Algebra

/-- The localizations of a smooth algebra `A` over a field `K` at its primes are regular local
rings: on a neighbourhood `D(x)` of `P`, `A` is étale over a polynomial ring over `K`, which is a
regular ring, and `A_P` is a localization of `A[1/x]` at a prime. -/
theorem Smooth.isRegularLocalRing_localization (K A : Type*) [Field K] [CommRing A]
    [Algebra K A] [Smooth K A] (P : Ideal A) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) := by
  obtain ⟨s, hs, H⟩ := Smooth.exists_span_eq_top_isStandardSmooth K A
  obtain ⟨x, hxs, hxP⟩ : ∃ x ∈ s, x ∉ P := by
    by_contra! h
    exact Ideal.IsPrime.ne_top inferInstance (top_le_iff.mp (hs ▸ Ideal.span_le.mpr h :))
  obtain ⟨ι, σ, _, _, ⟨Q⟩⟩ := (H x hxs).out
  have := Q.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨g, hg⟩ := IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    Q.dimension K (Localization.Away x)
  algebraize [g.toRingHom]
  have hdisj : Disjoint (Submonoid.powers x : Set A) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hxP (Ideal.IsPrime.mem_of_pow_mem inferInstance n hn)
  set P' := P.map (algebraMap A (Localization.Away x))
  have : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) _ P
    inferInstance hdisj
  have hP' : P'.comap (algebraMap A (Localization.Away x)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) (Localization.Away x)
      inferInstance hdisj
  clear_value P'
  have := IsRegularLocalRing.localization_of_etale (R := MvPolynomial (Fin Q.dimension) K) P'
  subst hP'
  exact .of_ringEquiv (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers x) P').toRingEquiv.symm


/-- A smooth algebra over a field is a regular ring. -/
theorem Smooth.isRegularRing (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Smooth K A] :
    IsRegularRing A := by
  have := Algebra.FiniteType.isNoetherianRing K A
  rw [isRegularRing_iff]
  intro P _
  exact Smooth.isRegularLocalRing_localization K A P

end Algebra
