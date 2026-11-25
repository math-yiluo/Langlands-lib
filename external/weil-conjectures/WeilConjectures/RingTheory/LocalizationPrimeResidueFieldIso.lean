/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Prime ideals, local rings and residue fields of a localization

Source: Stacks Project, Algebra, Tags 00E3, 00C9 and 07BH.
-/

@[expose] public section

universe u v

namespace IsLocalization

/-- A localization induces the prime-ideal correspondence and canonical isomorphisms of
local rings and residue fields. Source: Stacks Project, Algebra, Tags 00E3, 00C9 and 07BH.

Proof:
1. The contraction `q` of `q'` is prime: one does not lie in it and primality pulls back
   along the ring map. It is disjoint from `W` because every denominator maps to a unit,
   whereas a proper prime ideal contains no units.
2. For a prime `p` disjoint from `W`, the extension consists of fractions with numerator
   in `p`, by bringing finite sums to a common denominator. If the image of `x` is such
   a fraction `a/w`, the localization kernel condition gives `t * (w*x-a) = 0` for some
   `t` in `W`. Thus `twx` lies in `p`; since `tw` does not, `x` lies in `p`. This proves
   that the contraction of the extension is `p` and that the extension is proper.
3. If a product of two fractions lies in the extension of `p`, its numerator lies in
   `p` by step 2. Primality of `p` puts one numerator in `p`, proving the extension prime.
4. A fraction in `q'` has numerator in `q`, giving extension of contraction equal to
   `q'`. Steps 1-3 and this identity give mutually inverse maps on the indicated primes
   (Tag 00E3).
5. Localize `A'` at the complement of `q'` (def-weil-pbc-localization-at-prime).
   By lem-weil-pbc-localization-of-localization, the composite is a localization at
   the set of `x` with image `n * image(w)`, where `n` is outside `q'` and `w` is in `W`.
   This set is exactly the complement of `q`: use `w = 1` in one direction; in the
   other direction `image(w)` is a unit and primality excludes their product from `q'`.
   Uniqueness of localization gives the `A`-algebra isomorphism `e`, whose ring map is
   `Localization.localRingHom`, hence sends `a/s` to `image(a)/image(s)` (Tag 00C9).
6. These local rings have maximal ideals the extensions of `q` and `q'`
   (def-weil-pbc-localization-at-prime). The isomorphism carries the unique maximal
   ideal onto the unique maximal ideal. Passing to their quotients gives the field
   isomorphism `σ`. It commutes with the residue maps and is an `A`-algebra isomorphism
   because `e` is one (Tag 07BH). -/
theorem prime_localRing_residueField_iso
    (A : Type u) (A' : Type v) [CommRing A] [CommRing A'] [Algebra A A']
    (W : Submonoid A) [IsLocalization W A'] (q' : Ideal A') [q'.IsPrime] :
    let q := q'.comap (algebraMap A A')
    q.IsPrime ∧ Disjoint (W : Set A) (q : Set A) ∧
      (∀ p : Ideal A, p.IsPrime → Disjoint (W : Set A) (p : Set A) →
        (p.map (algebraMap A A')).IsPrime ∧
          (p.map (algebraMap A A')).comap (algebraMap A A') = p) ∧
      q.map (algebraMap A A') = q' ∧
      Set.BijOn (Ideal.comap (algebraMap A A')) {r : Ideal A' | r.IsPrime}
        {p : Ideal A | p.IsPrime ∧ Disjoint (W : Set A) (p : Set A)} ∧
      IsLocalization.AtPrime (Localization.AtPrime q') q ∧
      ∃ e : Localization.AtPrime q ≃ₐ[A] Localization.AtPrime q',
        e.toRingHom = Localization.localRingHom q q' (algebraMap A A') rfl ∧
        (q.map (algebraMap A (Localization.AtPrime q))).map e.toRingHom =
          q'.map (algebraMap A' (Localization.AtPrime q')) ∧
        ∃ σ : q.ResidueField ≃ₐ[A] q'.ResidueField,
          ∀ x : Localization.AtPrime q,
            σ (IsLocalRing.residue (Localization.AtPrime q) x) =
              IsLocalRing.residue (Localization.AtPrime q') (e x) := by
  let q := q'.comap (algebraMap A A')
  have hq := (isPrime_iff_isPrime_disjoint W A' q').mp inferInstance
  let : q.IsPrime := hq.1
  have hp : ∀ p : Ideal A, p.IsPrime → Disjoint (W : Set A) (p : Set A) →
      (p.map (algebraMap A A')).IsPrime ∧
        (p.map (algebraMap A A')).comap (algebraMap A A') = p := by
    intro p hprime hd
    exact ⟨isPrime_of_isPrime_disjoint W A' p hprime hd,
      under_map_of_isPrime_disjoint W A' hprime hd⟩
  have hbij : Set.BijOn (Ideal.comap (algebraMap A A')) {r : Ideal A' | r.IsPrime}
      {p : Ideal A | p.IsPrime ∧ Disjoint (W : Set A) (p : Set A)} := by
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      exact (isPrime_iff_isPrime_disjoint W A' r).mp hr
    · intro r hr s hs hrs
      exact (orderEmbedding W A').injective hrs
    · intro p hp'
      exact ⟨p.map (algebraMap A A'), (hp p hp'.1 hp'.2).1,
        (hp p hp'.1 hp'.2).2⟩
  let : IsLocalization.AtPrime (Localization.AtPrime q') q :=
    isLocalization_isLocalization_atPrime_isLocalization W (Localization.AtPrime q') q'
  refine ⟨hq.1, hq.2, hp, map_under W A' q', hbij, inferInstance, ?_⟩
  let e : Localization.AtPrime q ≃ₐ[A] Localization.AtPrime q' :=
    IsLocalization.algEquiv q.primeCompl _ _
  refine ⟨e, ?_, ?_, IsLocalRing.ResidueField.mapAlgEquiv e, ?_⟩
  · exact (Localization.localRingHom_unique q q' (algebraMap A A') rfl
      (fun x ↦ by
        change e (algebraMap A (Localization.AtPrime q) x) = _
        rw [← IsScalarTower.algebraMap_apply A A' (Localization.AtPrime q')]
        exact e.commutes x)).symm
  · rw [Localization.AtPrime.map_eq_maximalIdeal,
      Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  · intro x
    exact IsLocalRing.ResidueField.mapAlgEquiv_residue e x

end IsLocalization
