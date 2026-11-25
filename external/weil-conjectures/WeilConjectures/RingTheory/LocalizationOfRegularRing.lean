/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# A localization of a regular ring is regular

Source: Stacks Project, Algebra, proof of Lemma Tag 0381, Step 3
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v

namespace RingTheory

/-- A localization of a regular ring is regular.

Source: Stacks Project, Algebra, proof of Lemma Tag 0381, Step 3
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Give `R'` the algebra structure induced by `φ`. The three hypotheses imply
`IsLocalization M R'`: the fraction presentation gives surjectivity after multiplying by the
denominator, and applying `hzero` to `x - y` gives the equality criterion. First prove that the
canonical localization `Localization M` is regular. It is Noetherian by localization, and
Mathlib's `IsLocalization.localizationLocalizationAtPrimeIsoLocalization` identifies its
localization at any prime with the localization of `R` at the contracted prime. Transport
regular localness along this isomorphism. Finally, uniqueness of localization gives
`Localization M ≃ₐ[R] R'`, and `IsRegularRing.of_ringEquiv` transports regularity to `R'`.
This uses `lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-localization-of-localization`, and the Mathlib ring-equivalence transport lemmas.
-/
theorem isRegularRing_of_localization
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [IsRegularRing R]
    (M : Submonoid R) (φ : R →+* R')
    (hunit : ∀ s : M, IsUnit (φ s.1))
    (hsurj : ∀ y : R', ∃ r : R, ∃ s : M, ∃ u : R',
      IsUnit u ∧ φ s.1 * u = 1 ∧ y = φ r * u)
    (hzero : ∀ r : R, φ r = 0 → ∃ s : M, s.1 * r = 0) :
    IsRegularRing R' := by
  let : Algebra R R' := φ.toAlgebra
  have : IsLocalization M R' := by
    refine (isLocalization_iff M R').mpr ⟨hunit, ?_, ?_⟩
    · intro y
      obtain ⟨r, s, u, _, hu, hy⟩ := hsurj y
      refine ⟨(r, s), ?_⟩
      change y * φ s.1 = φ r
      rw [hy, mul_assoc, mul_comm u, hu, mul_one]
    · intro x y hxy
      change φ x = φ y at hxy
      obtain ⟨s, hs⟩ := hzero (x - y) (by simpa using sub_eq_zero.mpr hxy)
      exact ⟨s, sub_eq_zero.mp (by simpa only [mul_sub] using hs)⟩
  have : IsRegularRing (Localization M) := by
    apply isRegularRing_iff.mpr
    intro p hp
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p).toRingEquiv
  exact IsRegularRing.of_ringEquiv (IsLocalization.algEquiv M (Localization M) R').toRingEquiv

end RingTheory
