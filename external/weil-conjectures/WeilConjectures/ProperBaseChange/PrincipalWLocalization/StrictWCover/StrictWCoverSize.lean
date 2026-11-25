/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.StrictWCover.ThmPeIndetaleRefinementPart3Supplement
public import Mathlib.SetTheory.Cardinal.Arithmetic
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.PrincipalWLocalizationSize
import WeilConjectures.RingTheory.EtaleContraction.EtaleContractionSize
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.RetainedLocalizationSize

/-!
# Cardinality of the strict w-local cover

Source: Stacks Project, Tags 0976, 097S, 0984 (first three stages), and the first
paragraph of the proof of Tag 097X (blueprint: lem-weil-pbc-strict-w-cover-size).
-/

@[expose] public section

universe u v

namespace PrincipalWLocalization.StrictWCover

/-- The strict w-local cover has cardinality at most any infinite cardinal bounding the base.
Source: Stacks Project, Tags 0976, 097S, 0984 (first three stages), and the first
paragraph of the proof of Tag 097X (blueprint: lem-weil-pbc-strict-w-cover-size).

Proof plan:
1. Use `lem-weil-pbc-finite-list-cardinality` to encode finite lists, finite nested lists,
   natural numbers, finite tuples, images, and indexed unions of size at most `κ`.
2. For any ring `R` of size at most `κ`, encode constructible subsets by finite Boolean
   expressions in principal opens and closed sets. Encode finite partitions and their chosen
   denominators this way; there are at most `κ` indices in
   `theorem-existence-contractible-covers--1`. Common refinement makes these indices directed
   (`definition-w-local-w-strictly-local--2`).
3. Elements of each finite product of principal localizations are finite tuples of fractions.
   Their codes and the index codes have size at most `κ`. Every colimit element has a stage
   representative by `lem-pc-filtered-colimit-commrings-elementwise`, so `|R^w| ≤ κ`.
   In particular `|W| ≤ κ`.
4. By `def-weil-pbc-finitely-presented-algebra`, finite polynomial generators and relations
   encode all finitely presented algebras up to isomorphism, and encode their elements.
   Both sets have size at most `κ`; restrict to the faithfully flat étale representatives
   used by `theorem-existence-contractible-covers--1`, with just one per isomorphism class.
5. Finite subsets of these representatives form at most `κ` indices. A finite tensor product
   has the presentation obtained by concatenating variables and relations, so has size at
   most `κ`, including the empty tensor product `R`. Stage representatives bound their
   filtered colimit, using `lem-pc-filtered-colimit-commrings-elementwise`.
6. Induct over the successive rings starting at `W`. Each has size at most `κ` by steps 3
   and 5. The countable colimit `E = W^e` has size at most `κ`, by encoding a natural-number
   stage and its element and using `lem-pc-filtered-colimit-commrings-elementwise` again.
7. The zero locus `T = V(IE)` is closed. Apply step 3 to `E` to bound `E^w`. Constructible
   neighbourhoods of `T` form at most `κ` indices, directed by reverse inclusion and inhabited
   by the whole spectrum. Each localization at its selector has size at most `κ`, by fraction
   codes. Stage representatives bound their colimit from `theorem-existence-contractible-covers--1`.
   By `theorem-existence-contractible-covers--1`, that colimit is precisely `C_A`.
-/
theorem cardinalMk_le (A : Type u) [CommRing A] (κ : Cardinal.{v})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hA : Cardinal.lift.{v} (Cardinal.mk A) ≤ Cardinal.lift.{u} κ) :
    Cardinal.lift.{v} (Cardinal.mk (algebra A)) ≤ Cardinal.lift.{u} κ := by
  let μ : Cardinal.{u} := max (Cardinal.mk A) Cardinal.aleph0
  have hμ : Cardinal.aleph0 ≤ μ := le_max_right _ _
  have hW := PrincipalWLocalization.cardinalMk_le A μ hμ (le_max_left _ _)
  have hE : Cardinal.mk (contraction A) ≤ μ :=
    CommRingCat.EtaleContraction.cardinalMk_le
      (CommRingCat.of (PrincipalWLocalization.algebra A)) μ hμ hW
  have hEw := PrincipalWLocalization.cardinalMk_le (contraction A) μ hμ hE
  have hC : Cardinal.mk (algebra A) ≤ μ :=
    (PrincipalWLocalization.Retained.cardinalMk_le (contraction A)
      (PrimeSpectrum.zeroLocus (extendedIdeal A : Set (contraction A)))
      (PrimeSpectrum.isClosed_zeroLocus _)).trans hEw
  apply (Cardinal.lift_le.mpr hC).trans
  simpa [μ] using max_le hA (Cardinal.lift_le.mpr hκ)

end PrincipalWLocalization.StrictWCover
