/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PairHenselization
import WeilConjectures.RingTheory.HenselizationPairGRingCore

/-!
# G-rings and henselizations of pairs

Source: Stacks Project, More on Algebra, Lemma Tag 0AH3 (blueprint:
lem-weil-pbc-henselization-pair-g-ring).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- If `A` is a G-ring, then the ring in a henselization of the pair `(A, I)` is a
G-ring. Here a henselization is represented by its colimit cocone, together with
the colimit, henselian-pair, and quotient-isomorphism properties of
`pair_henselization`.

Source: Stacks Project, More on Algebra, Lemma Tag 0AH3 (the assertion that the
henselization of a pair with G-ring underlying ring is a G-ring); the displayed
hypotheses spell out the henselization supplied by Tag 0A02
(blueprint: lem-weil-pbc-henselization-pair-g-ring).

Proof (the five steps of the node):
1. The G-ring hypothesis includes Noetherianity. Apply
   lem-weil-pbc-henselization-noetherian-completion (Tag 0AGV): the henselization
   is Noetherian, the structure map is flat, and the ideal-adic completions agree.
2. Fix a maximal ideal of the henselization and take its inverse image in `A`.
   Henselianness puts the extended ideal inside this maximal ideal; the quotient
   isomorphism identifies the corresponding residue fields and extended maximal
   ideals. Localize the flat structure map and apply
   lem-weil-pbc-flat-local-completion-iso (Tag 0AGX) to identify the maximal-adic
   completions of these two local rings. Use lem-weil-pbc-pair-henselization for
   the quotient property.
3. For a prime of the base local ring and a prime above it, apply
   lem-weil-pbc-henselization-finite-separable-fibres (Tag 0AH1) to the Noetherian
   filtered colimit of etale algebras from lem-weil-pbc-pair-henselization.
   Its fibre is a finite product of residue fields, each separable algebraic
   over the base residue field; localizing retains the relevant factors.
4. The completion isomorphism and finite product decomposition identify the
   chosen completed fibre as a direct factor of the base completed fibre.
   By theorem-finite-etale-covers-proper-henselian--2 the latter is geometrically regular over the
   base residue field, hence so is its direct factor. Apply
   lem-weil-pbc-geometric-regularity-separable-extension (Algebra Tag 07QH) to
   transfer this regularity to the chosen separable algebraic residue field.
5. All maximal local completion maps thus have geometrically regular fibres.
   Noetherianity from step 1 and lem-weil-pbc-g-ring-maximal-ideal-criterion
   (Tag 07PT) imply that the henselization is a G-ring.
-/
theorem isGRing_of_pair_henselization
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : Nonempty (IsColimit c) ∧
      HenselianRing c.pt.right (I.map c.pt.hom.hom) ∧
      Function.Bijective (Ideal.quotientMap (I.map c.pt.hom.hom) c.pt.hom.hom
        (Ideal.le_comap_map)))
    (hA : IsGRing A) : IsGRing c.pt.right := by
  obtain ⟨hn, hm⟩ := henselization_pair_noetherian_and_maximal_regular A I c hc hA
  let _ : IsNoetherianRing c.pt.right := hn
  exact (isGRing_iff_maximalIdeal c.pt.right).2 hm

end RingTheory
