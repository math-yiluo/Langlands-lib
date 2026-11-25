/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import WeilConjectures.RingTheory.BijectiveQuotientMapPowOfFlat

/-!
# Flatness and ideal-power quotients of a pair henselization

Source: Stacks Project, More on Algebra, Lemma 15.12.2, Tag 0AGU
(blueprint: lem-weil-pbc-henselization-flat-quotients).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The structure map of the pair henselization is flat and induces isomorphisms on
quotients by every positive power of the ideal. The cocone and its colimit condition
are exactly those in `pair_henselization`; its vertex is `Aʰ`, and its map is `η`.
The extended ideal is `I.map η`, and `Ideal.map_pow` identifies the extension of
`I ^ n` with `(I.map η) ^ n`.
Source: Stacks Project, More on Algebra, Lemma 15.12.2, Tag 0AGU
(blueprint: lem-weil-pbc-henselization-flat-quotients).

Proof:
1. `pair_henselization` supplies essential smallness and filteredness of the diagram.
2. Its stages are flat because they are etale. The existing source-library theorem
   `RingHom.Flat.iff_ind_flat`, together with `ObjectProperty.of_essentiallySmall_index`,
   gives flatness of the colimit structure map.
3. `pair_henselization` also supplies a colimit whose quotient map modulo I is bijective.
   The unique isomorphism between colimits is an A-algebra isomorphism, hence identifies
   the extended ideals. Its induced quotient equivalence transports this bijectivity
   to the given colimit.
4. Apply `RingHom.bijective_quotientMap_pow_of_flat` directly to this flat structure map
   and its bijective quotient map modulo I. This avoids taking colimits of the quotients
   separately for each power. -/
theorem pair_henselization_flat_quotients (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun B : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map B.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map B.hom.hom) B.hom.hom
            Ideal.le_comap_map))))
    (hc : IsColimit c) :
    RingHom.Flat c.pt.hom.hom ∧
      ∀ n : ℕ, 1 ≤ n →
        Function.Bijective (Ideal.quotientMap ((I ^ n).map c.pt.hom.hom) c.pt.hom.hom
          Ideal.le_comap_map) := by
  let P : ObjectProperty (Under (CommRingCat.of A)) := fun B ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map B.hom) ∧
      Function.Bijective (Ideal.quotientMap (I.map B.hom.hom) B.hom.hom
        Ideal.le_comap_map)
  obtain ⟨hsmall, hfiltered, d, ⟨hd⟩, _, hq⟩ := pair_henselization A I
  let : EssentiallySmall.{u} P.FullSubcategory := hsmall
  let : IsFiltered P.FullSubcategory := hfiltered
  have hflat : RingHom.Flat c.pt.hom.hom := by
    rw [RingHom.Flat.iff_ind_flat, CategoryTheory.MorphismProperty.ind_iff_ind_underMk]
    change ObjectProperty.ind.{u} CommRingCat.flat.underObj c.pt
    apply ObjectProperty.of_essentiallySmall_index
      (pres := { diag := P.ι, ι := c.ι, isColimit := hc })
    intro j
    change RingHom.Flat j.obj.hom.hom
    let := j.property.1
    exact AlgebraicGeometry.Flat.SpecMap_iff.mp inferInstance
  refine ⟨hflat, RingHom.bijective_quotientMap_pow_of_flat c.pt.hom.hom hflat I ?_⟩
  let e := (Under.forget (CommRingCat.of A)).mapIso (hd.coconePointUniqueUpToIso hc)
  let er := e.commRingCatIsoToRingEquiv
  have hw : er.toRingHom.comp d.pt.hom.hom = c.pt.hom.hom :=
    congrArg CommRingCat.Hom.hom (Under.w (hd.coconePointUniqueUpToIso hc).hom)
  have hmap : I.map c.pt.hom.hom = (I.map d.pt.hom.hom).map er.toRingHom := by
    rw [Ideal.map_map, hw]
  let eq := Ideal.quotientEquiv (I.map d.pt.hom.hom) (I.map c.pt.hom.hom) er hmap
  have heq : Ideal.quotientMap (I.map c.pt.hom.hom) c.pt.hom.hom
      Ideal.le_comap_map = eq.toRingHom.comp
        (Ideal.quotientMap (I.map d.pt.hom.hom) d.pt.hom.hom Ideal.le_comap_map) := by
    ext a
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk, RingEquiv.toRingHom_eq_coe]
    exact congrArg (Ideal.Quotient.mk (I.map c.pt.hom.hom))
      (congrArg (fun f : A →+* c.pt.right ↦ f a) hw).symm
  rw [heq]
  exact eq.bijective.comp hq

end RingTheory
