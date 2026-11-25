/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionPartialLocalFlat

/-!
# Flatness of relative global complete intersections

Source: Stacks Project, Algebra, Lemma Tag 00SW
(blueprint: lem-weil-pbc-relative-global-complete-intersection-flat).
-/

@[expose] public section

universe u

namespace Algebra

/-- A polynomial quotient that is a relative global complete intersection is flat over
its coefficient ring. Source: Stacks Project, Algebra, Lemma Tag 00SW.
(blueprint: lem-weil-pbc-relative-global-complete-intersection-flat)

Proof:
1. For a prime `q` of the quotient, let `q'` be its inverse image in the polynomial ring.
   Part (2) of `lem-weil-pbc-relative-global-complete-intersection-partial-local-flat`,
   with `i = c` in a complete-intersection presentation, makes the localized polynomial
   quotient flat over `R`. The isomorphism of
   `lem-weil-pbc-localization-at-prime-of-quotient` identifies it with the quotient
   localized at `q`. The hypothesis applies to the displayed equations themselves.
2. It suffices to take maximal ideals `q`. Apply Mathlib's
   `Module.flat_of_isLocalized_maximal` with the quotient as both the intermediate
   algebra and the module. This version of the local flatness criterion checks each
   localization over `R` directly, so there is no need to localize `R` separately.
   Convert module flatness to ring-map flatness with `RingHom.flat_algebraMap_iff`.
   If the quotient is zero, there are no maximal ideals and the criterion is vacuous. -/
theorem flat_of_isRelativeGlobalCompleteIntersection_quotient
    (R : Type u) [CommRing R] (n c : ℕ) (relations : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation relations) :
    RingHom.Flat
      (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations))) := by
  let P := MvPolynomial (Fin n) R
  let I : Ideal P := Ideal.span (Set.range relations)
  let S := P ⧸ I
  rw [RingHom.flat_algebraMap_iff]
  apply Module.flat_of_isLocalized_maximal S S
    (fun q ↦ Localization.AtPrime q) (fun q ↦ Algebra.linearMap S _)
  intro q hq
  let q' : PrimeSpectrum P := PrimeSpectrum.comap (Ideal.Quotient.mk I) ⟨q, inferInstance⟩
  let L := Localization.AtPrime q'.asIdeal
  let Q := L ⧸ I.map (algebraMap P L)
  have hfull : relations '' {j : Fin c | j.val < c} = Set.range relations := by
    simp
  have hflat : Module.Flat R Q := by
    have ht := relativeGlobalCompleteIntersection_partial_local_flat R n c relations h
      ⟨q, inferInstance⟩ c le_rfl
    change Module.Flat R
      (L ⧸ Ideal.map (algebraMap P L) (Ideal.span (relations '' {j : Fin c | j.val < c})))
      at ht
    rw [hfull] at ht
    exact ht
  have hmon : Algebra.algebraMapSubmonoid S q'.asIdeal.primeCompl = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q
  have : IsLocalization q.primeCompl Q := by
    rw [← hmon]
    infer_instance
  have : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R P Q, IsScalarTower.algebraMap_apply R P S,
      ← IsScalarTower.algebraMap_apply P S Q]
  let e := IsLocalization.algEquiv q.primeCompl Q (Localization.AtPrime q)
  exact Module.Flat.of_linearEquiv (e.symm.restrictScalars R).toLinearEquiv

end Algebra
