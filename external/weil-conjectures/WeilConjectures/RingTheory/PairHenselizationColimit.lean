/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian

import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

import WeilConjectures.RingTheory.PairHenselizationEssentiallySmall
import WeilConjectures.RingTheory.PairHenselizationFiltered
import WeilConjectures.RingTheory.HenselianOfEtaleSectionLifting
import WeilConjectures.RingTheory.PairHenselizationSections

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

set_option backward.isDefEq.respectTransparency false in
/-- A henselian colimit with unchanged quotient for the etale neighbourhood category.
Source: Stacks Project, Tag 0A02, colimit and section-lifting paragraphs.
(blueprint: lem-weil-pbc-pair-henselization-colimit).

Proof: Use essential smallness and filteredness to pass to a small equivalent category.
Form its filtered colimit H of B-algebras and transport the cocone and its universal
property back to the full category. The vertex is an object of the under category.
For each object C there is a unique B-algebra map pi_C : C to R = B/J: factor through
C/JC and invert the given quotient isomorphism. Uniqueness makes these maps compatible.
They induce pi : H to R, killing JH. On quotients this is a left inverse of R to H/JH.
Every element of H comes from some C, and modulo JC is the image of an element of B;
therefore R to H/JH is also surjective and is an isomorphism.
To prove henselianness, take an etale H-algebra A and an H-algebra section A to H/JH.
Etale filtered-colimit descent gives a stage C and an etale C-algebra D with
A isomorphic to H tensor_C D. The section and H/JH isomorphic to R give s : D to R.
Over R the etale algebra D/JD has this section. Idempotent splitting gives an idempotent
e in D/JD whose localization is R and whose image under s is 1. Lift e to g in D.
Then D localized at g is etale over B and has quotient R, hence is an object of the
original category. Its coprojection to H agrees on C with the original coprojection.
The tensor universal property now gives an H-algebra map A to H. Its reduction is the
chosen section: s extends to the localization since s(g)=1, and this extension equals
the unique map pi for that object. Thus all etale sections lift. Apply
`henselianRing_of_etale_section_lifting` (Stacks 09XI) to get HenselianRing H (JH).
The colimit and quotient arguments above supply the other asserted conjuncts. -/
theorem pair_henselization_colimit (B : Type u) [CommRing B] (J : Ideal B) :
    ∃ c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))),
      Nonempty (IsColimit c) ∧
        HenselianRing c.pt.right (J.map c.pt.hom.hom) ∧
        Function.Bijective (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom
          (Ideal.le_comap_map)) := by
  let P : ObjectProperty (Under (CommRingCat.of B)) := fun C ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
      Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
        (Ideal.le_comap_map))
  let : EssentiallySmall.{u} P.FullSubcategory := pair_henselization_essentiallySmall B J
  let : IsFiltered P.FullSubcategory := pair_henselization_filtered B J
  let : IsConnected P.FullSubcategory := IsFiltered.isConnected _
  let : IsFiltered (SmallModel.{u} P.FullSubcategory) :=
    IsFiltered.of_equivalence (equivSmallModel P.FullSubcategory)
  let : PreservesColimitsOfShape P.FullSubcategory (forget CommRingCat.{u}) :=
    preservesColimitsOfShape_of_equiv (equivSmallModel P.FullSubcategory).symm _
  let : HasColimitsOfShape P.FullSubcategory CommRingCat.{u} :=
    hasColimitsOfShape_of_essentiallySmall _ _
  let c := colimit.cocone P.ι
  have hc : IsColimit c := colimit.isColimit P.ι
  have hq : Function.Bijective (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom
      (Ideal.le_comap_map)) := by
    let F := P.ι
    have hF : ∀ i : P.FullSubcategory, Function.Bijective
        (Ideal.quotientMap (J.map (F.obj i).hom.hom) (F.obj i).hom.hom
          (Ideal.le_comap_map)) := fun C ↦ C.property.2
    classical
    let q (i : P.FullSubcategory) := Ideal.quotientMap (J.map (F.obj i).hom.hom) (F.obj i).hom.hom
      (Ideal.le_comap_map)
    let e (i : P.FullSubcategory) := RingEquiv.ofBijective (q i) (hF i)
    let p (i : P.FullSubcategory) : (F.obj i).right →+* B ⧸ J :=
      (e i).symm.toRingHom.comp (Ideal.Quotient.mk (J.map (F.obj i).hom.hom))
    have hp (i : P.FullSubcategory) : (p i).comp (F.obj i).hom.hom = Ideal.Quotient.mk J := by
      ext b
      exact (e i).symm_apply_apply (Ideal.Quotient.mk J b)
    have huniq (i : P.FullSubcategory) (f g : (F.obj i).right →+* B ⧸ J)
        (hf : f.comp (F.obj i).hom.hom = Ideal.Quotient.mk J)
        (hg : g.comp (F.obj i).hom.hom = Ideal.Quotient.mk J) : f = g := by
      have hfJ : J.map (F.obj i).hom.hom ≤ RingHom.ker f := by
        rw [Ideal.map_le_iff_le_comap]
        intro b hb
        change f ((F.obj i).hom.hom b) = 0
        rw [← RingHom.comp_apply, hf]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
      have hgJ : J.map (F.obj i).hom.hom ≤ RingHom.ker g := by
        rw [Ideal.map_le_iff_le_comap]
        intro b hb
        change g ((F.obj i).hom.hom b) = 0
        rw [← RingHom.comp_apply, hg]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
      let f' := Ideal.Quotient.lift _ f hfJ
      let g' := Ideal.Quotient.lift _ g hgJ
      have heq : f'.comp (q i) = g'.comp (q i) := by
        refine RingHom.ext fun x ↦ ?_
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        simpa [f', g', q] using congrArg (fun k : B →+* B ⧸ J ↦ k b) (hf.trans hg.symm)
      have heq' : f' = g' := RingHom.ext fun x ↦ by
        obtain ⟨y, rfl⟩ := (hF i).2 x
        exact congrArg (fun k : B ⧸ J →+* B ⧸ J ↦ k y) heq
      ext x
      exact congrArg (fun k ↦ k (Ideal.Quotient.mk (J.map (F.obj i).hom.hom) x)) heq'
    let d : Cocone F :=
      { pt := Under.mk (CommRingCat.ofHom (Ideal.Quotient.mk J))
        ι :=
          { app := fun i ↦ Under.homMk (CommRingCat.ofHom (p i)) (by
              apply CommRingCat.hom_ext
              exact hp i)
            naturality := by
              intro i j f
              apply Under.UnderMorphism.ext
              apply CommRingCat.hom_ext
              apply huniq i
              · change ((p j).comp (F.map f).right.hom).comp (F.obj i).hom.hom = _
                rw [RingHom.comp_assoc]
                have hw : (F.map f).right.hom.comp (F.obj i).hom.hom =
                    (F.obj j).hom.hom := by
                  exact congrArg CommRingCat.Hom.hom (Under.w (F.map f))
                rw [hw]
                exact hp j
              · exact hp i } }
    let pi := (hc.desc d).right.hom
    have hpi : pi.comp c.pt.hom.hom = Ideal.Quotient.mk J :=
      congrArg CommRingCat.Hom.hom (Under.w (hc.desc d))
    have hpiJ : J.map c.pt.hom.hom ≤ RingHom.ker pi := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      change pi (c.pt.hom.hom b) = 0
      rw [← RingHom.comp_apply, hpi]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
    let pi' := Ideal.Quotient.lift _ pi hpiJ
    constructor
    · have hleft : Function.LeftInverse pi'
          (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom (Ideal.le_comap_map)) := by
        intro x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        change pi (c.pt.hom.hom b) = Ideal.Quotient.mk J b
        exact congrArg (fun k : B →+* B ⧸ J ↦ k b) hpi
      exact hleft.injective
    · intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨i, b, hb⟩ := Concrete.isColimit_exists_rep (F ⋙ Under.forget _)
        (isColimitOfPreserves (Under.forget _) hc) a
      obtain ⟨y, hy⟩ := (hF i).2 (Ideal.Quotient.mk (J.map (F.obj i).hom.hom) b)
      refine ⟨y, ?_⟩
      obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective y
      let k := (c.ι.app i).right.hom
      have hk : (J.map (F.obj i).hom.hom).map k ≤ J.map c.pt.hom.hom := by
        rw [Ideal.map_map]
        have hw : k.comp (F.obj i).hom.hom = c.pt.hom.hom :=
          congrArg CommRingCat.Hom.hom (Under.w (c.ι.app i))
        rw [hw]
      have hh := congrArg (Ideal.quotientMap (J.map c.pt.hom.hom) k
        (Ideal.le_comap_of_map_le hk)) hy
      simp only [Ideal.quotientMap_mk] at hh
      have hw : k.comp (F.obj i).hom.hom = c.pt.hom.hom :=
        congrArg CommRingCat.Hom.hom (Under.w (c.ι.app i))
      change Ideal.Quotient.mk (J.map c.pt.hom.hom) (c.pt.hom.hom b₀) = _
      rw [← hb]
      change Ideal.Quotient.mk (J.map c.pt.hom.hom) (c.pt.hom.hom b₀) =
        Ideal.Quotient.mk (J.map c.pt.hom.hom) (k b)
      have hwb := congrArg (fun f : B →+* c.pt.right ↦ f b₀) hw
      change k ((F.obj i).hom.hom b₀) = c.pt.hom.hom b₀ at hwb
      exact (congrArg (Ideal.Quotient.mk (J.map c.pt.hom.hom)) hwb).symm.trans hh
  have hs := pair_henselization_sections B J c hc hq
  exact ⟨c, ⟨hc⟩,
    (henselianRing_of_etale_section_lifting.{u, u} c.pt.right (J.map c.pt.hom.hom) hs).2.1,
    hq⟩

end RingTheory
