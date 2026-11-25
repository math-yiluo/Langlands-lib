/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Order.Directed
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Recognition and functoriality of directed ring colimit cocones

Source: Stacks Project, Categories, Tags 04AX and 002F; the algebraic verification
for `equation-sections-of-intersection` in `more-groupoids.tex`.
(blueprint: lem-a1-directed-ring-cocone-recognition)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

private noncomputable def recognizeRingCocone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F)
    (hrep : ∀ r : c.pt, ∃ (i : I) (a : F.obj i), c.ι.app i a = r)
    (heq : ∀ (i : I) (a b : F.obj i), c.ι.app i a = c.ι.app i b →
      ∃ (k : I) (hik : i ≤ k), F.map (homOfLE hik) a = F.map (homOfLE hik) b) :
    IsColimit c := by
  let : HasColimit F :=
    ⟨_, FilteredColimits.colimitCoconeIsColimit F⟩
  let : ReflectsColimit F (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms F (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro r
    obtain ⟨i, a, ha⟩ := hrep r
    exact ⟨i, a, ha.symm⟩
  · intro i a b hab
    obtain ⟨k, hik, hk⟩ := heq i a b hab
    exact ⟨k, homOfLE hik, hk⟩

private theorem comparison_naturality
    {J : Type*} [Category J] {C : Type*} [Category C]
    {F F' : J ⥤ C} {c : Cocone F} {c' : Cocone F'}
    (hc : IsColimit c) (hc' : IsColimit c')
    (τ : F' ⟶ F) (u : c'.pt ⟶ c.pt)
    (hu : ∀ i, c'.ι.app i ≫ u = τ.app i ≫ c.ι.app i)
    (d : Cocone F) (d' : Cocone F') (hd : IsColimit d) (hd' : IsColimit d') :
    (hd'.coconePointUniqueUpToIso hc').hom ≫ u =
      hd'.map d τ ≫ (hd.coconePointUniqueUpToIso hc).hom := by
  apply hd'.hom_ext
  intro i
  simpa only [Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
    IsColimit.ι_map_assoc, IsColimit.comp_coconePointUniqueUpToIso_hom] using hu i

/-- A directed ring cocone is a colimit in rings, additive groups and sets when
its elements have representatives and equality at a stage holds eventually.
The canonical identifications with any other colimit cocones are natural for
compatible maps of ring diagrams and their cocones, in all three categories.
Here `IsColimit.desc`, `fac`, and `uniq` express exactly the existence and
uniqueness of the maps to every compatible ring, additive, or set cocone.

Source: Stacks Project, Categories, Tags 04AX (`section-directed-colimits`)
and 002F (`definition-colimit`); algebraic verification for
`equation-sections-of-intersection` in `more-groupoids.tex`.
(blueprint: lem-a1-directed-ring-cocone-recognition)

Proof:
1. If two representatives from different stages have equal images, move them
   to a common upper bound. The same-stage equality assumption then makes
   their images equal at a further stage, using the functor composition law.
2. For any set cocone, define the descended map on an element by choosing a
   representative. Step 1 and compatibility make this independent of the
   representative. Every descended map must have these values, giving uniqueness.
3. For an additive cocone, represent two elements at a common stage to check
   additivity. Nonemptiness supplies a stage at which to check zero; negatives
   are checked on a representative. The descended function is an additive map.
4. For a ring cocone, the same common-stage calculation checks multiplication;
   checking the unit at any stage gives a unital ring map. Thus Steps 2--4 give
   the three universal properties of `def-weil-pbc-category-colimit`. Neither
   nontriviality nor injectivity is used.
5. By `def-weil-pbc-category-colimit`, comparisons between colimit cocones are
   isomorphisms: both composites fix every coprojection. For a map of diagrams,
   the two composites in each asserted naturality square agree on every source
   coprojection by the equation relating the cocone maps. Uniqueness makes the
   square commute, in rings, additive groups and sets alike.
-/
theorem directed_cocone_recognition
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F)
    (hrep : ∀ r : c.pt, ∃ (i : I) (a : F.obj i), c.ι.app i a = r)
    (heq : ∀ (i : I) (a b : F.obj i), c.ι.app i a = c.ι.app i b →
      ∃ (k : I) (hik : i ≤ k), F.map (homOfLE hik) a = F.map (homOfLE hik) b) :
    ∃ hR : IsColimit c,
    ∃ hA : IsColimit
      ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapCocone c),
    ∃ hS : IsColimit ((forget CommRingCat).mapCocone c),
      ∀ (F' : I ⥤ CommRingCat.{u}) (c' : Cocone F'),
        (∀ r : c'.pt, ∃ (i : I) (a : F'.obj i), c'.ι.app i a = r) →
        (∀ (i : I) (a b : F'.obj i), c'.ι.app i a = c'.ι.app i b →
          ∃ (k : I) (hik : i ≤ k),
            F'.map (homOfLE hik) a = F'.map (homOfLE hik) b) →
        ∀ (τ : F' ⟶ F) (u : c'.pt ⟶ c.pt),
          (∀ i : I, c'.ι.app i ≫ u = τ.app i ≫ c.ι.app i) →
          ∃ hR' : IsColimit c',
          ∃ hA' : IsColimit
            ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapCocone c'),
          ∃ hS' : IsColimit ((forget CommRingCat).mapCocone c'),
            (∀ (d : Cocone F) (d' : Cocone F') (hd : IsColimit d) (hd' : IsColimit d'),
              (hd'.coconePointUniqueUpToIso hR').hom ≫ u =
                hd'.map d τ ≫ (hd.coconePointUniqueUpToIso hR).hom) ∧
            (∀ (d : Cocone (F ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
                (d' : Cocone (F' ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
                (hd : IsColimit d) (hd' : IsColimit d'),
              (hd'.coconePointUniqueUpToIso hA').hom ≫
                  (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map u =
                hd'.map d
                    (Functor.whiskerRight τ
                      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) ≫
                  (hd.coconePointUniqueUpToIso hA).hom) ∧
            (∀ (d : Cocone (F ⋙ forget CommRingCat))
                (d' : Cocone (F' ⋙ forget CommRingCat))
                (hd : IsColimit d) (hd' : IsColimit d'),
              (hd'.coconePointUniqueUpToIso hS').hom ≫ (forget CommRingCat).map u =
                hd'.map d (Functor.whiskerRight τ (forget CommRingCat)) ≫
                  (hd.coconePointUniqueUpToIso hS).hom) := by
  let hR := recognizeRingCocone F c hrep heq
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let hA := isColimitOfPreserves U hR
  let hS := isColimitOfPreserves (forget CommRingCat) hR
  refine ⟨hR, hA, hS, ?_⟩
  intro F' c' hrep' heq' τ u hu
  let hR' := recognizeRingCocone F' c' hrep' heq'
  let hA' := isColimitOfPreserves U hR'
  let hS' := isColimitOfPreserves (forget CommRingCat) hR'
  refine ⟨hR', hA', hS', ?_, ?_, ?_⟩
  · exact comparison_naturality hR hR' τ u hu
  · apply comparison_naturality hA hA' (Functor.whiskerRight τ U) (U.map u)
    intro i
    simpa only [Functor.map_comp] using! congrArg U.map (hu i)
  · apply comparison_naturality hS hS' (Functor.whiskerRight τ (forget CommRingCat))
      ((forget CommRingCat).map u)
    intro i
    simpa only [Functor.map_comp] using! congrArg (forget CommRingCat).map (hu i)

end CommRingCat
