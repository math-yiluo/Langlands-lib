/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!

# The canonical comparison `f_! ⟶ f_*`

For a morphism `f : X ⟶ Y` admitting a compactification `X --i--> Z --g--> Y`, this file
constructs the canonical natural transformation

`ι_f : f_! ⟶ f_*`

from the lower shriek to the pushforward on étale sheaves.

The construction proceeds through the adjoint triple `i_! ⊣ i^* ⊣ i_*` of the open
immersion `i`:

- Since `i` is a monomorphism, the localization functor `MorphismProperty.Over.map` of
  the small étale sites along `i` is fully faithful
  (`CategoryTheory.MorphismProperty.Over.full_map`), so the unit of the site-level
  adjunction `MorphismProperty.Over.mapPullbackAdj` is an isomorphism, and hence so is
  the counit of the induced sheaf-level adjunction `i^* ⊣ i_*`
  (`CategoryTheory.Adjunction.isIso_sheafPushforwardContinuous_counit`); this expresses
  that the restriction of a pushforward along an open immersion is the original sheaf.
- Inverting this counit and contracting with the counit of `i_! ⊣ i^*` yields the
  canonical map `i_! ⟶ i_*` (`Etale.openImmersionLowerShriekToLowerStar`).
- Pushing forward along `g` and composing with the composition isomorphism
  `Etale.lowerStarComp` gives `ι_f : f_! = g_* ∘ i_! ⟶ g_* ∘ i_* ≅ f_*`
  (`Etale.lowerShriekToLowerStar`).

For a proper morphism `f`, the comparison `ι_f` is an isomorphism; that statement needs the
vanishing of both sides off the range of `i`, which is where closedness of that range and
`HasZeroObject A` enter, and is proved downstream in
`WeilConjectures.SixFunctors.Etale.LowerShriek.Proper`.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStar`: the canonical map
  `i_! ⟶ i_*` for an open immersion `i`.
- `AlgebraicGeometry.Etale.lowerShriekToLowerStar`: the canonical comparison
  `ι_f : f_! ⟶ f_*` for `f` admitting a compactification.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar`: the
  restriction `i^*` of the comparison is an isomorphism, for *any* open immersion `i`.
- `AlgebraicGeometry.Etale.unit_map_openImmersionLowerShriekToLowerStar_app_counit` and
  `AlgebraicGeometry.Etale.openImmersionLowerShriek_lowerStar_hom_ext`: the transpose of the
  comparison under `i_! ⊣ i^*` and `i^* ⊣ i_*` is the identity, and maps `i_! F ⟶ i_* G` are
  determined by such transposes.
- `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar_of_isIso`: the formal reduction of
  the comparison for `f` to the comparison for the open immersion of its compactification.

-/

@[expose] public section

universe w u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The canonical natural transformation `i_! ⟶ i_*` from the extension by zero to the
pushforward along an open immersion, obtained from the adjoint triple `i_! ⊣ i^* ⊣ i_*`:
insert the inverse of the counit of `i^* ⊣ i_*` and contract with the counit of
`i_! ⊣ i^*`. -/
noncomputable def Etale.openImmersionLowerShriekToLowerStar :
    (j)_!open[A] ⟶ (j)_*[A] :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (inv (Etale.openImmersionRestrictionLowerStarAdjunction A j).counit)
      (j)_!open[A] ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (j)_*[A]
      (Etale.openImmersionLowerShriekAdjunction A j).counit ≫
    (Functor.rightUnitor _).hom

set_option backward.isDefEq.respectTransparency false in
omit [HasSmallSiteSheafify A] in
/-- The components of the comparison `j_! ⟶ j_*`: the unitors and the associator in its
definition are identities, so at `F` it is `j_!` of the inverted counit of `j^* ⊣ j_*`,
followed by the counit of `j_! ⊣ j^*` at `j_* F`. -/
lemma Etale.openImmersionLowerShriekToLowerStar_app (F : Sheaf U.smallEtaleTopology A) :
    (Etale.openImmersionLowerShriekToLowerStar A j).app F =
      (j)_!open[A].map
          ((inv (Etale.openImmersionRestrictionLowerStarAdjunction A j).counit).app F) ≫
        (Etale.openImmersionLowerShriekAdjunction A j).counit.app ((j)_*[A].obj F) := by
  simp only [Etale.openImmersionLowerShriekToLowerStar, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.id_obj,
    NatIso.isIso_inv_app, Functor.map_inv, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, id_comp, IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- **`j^*` of the comparison `j_! ⟶ j_*` is an isomorphism**, for any open immersion `j`
and with no hypothesis on the range of `j`.

Both factors of `Etale.openImmersionLowerShriekToLowerStar_app` become invertible after
applying `j^*`: the first is `j_!` of an isomorphism, and the second is
`Etale.isIso_openImmersionRestriction_map_lowerShriekAdjunction_counit`, which holds because
`j_!` is fully faithful along an open immersion. -/
instance Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar
    (F : Sheaf U.smallEtaleTopology A) :
    IsIso ((Etale.openImmersionRestriction A j).map
      ((Etale.openImmersionLowerShriekToLowerStar A j).app F)) := by
  rw [Etale.openImmersionLowerShriekToLowerStar_app, Functor.map_comp]
  infer_instance


omit [HasSmallSiteSheafify A] in
/-- The unit of `j_! ⊣ j^*` is the unit of `j_! ⊣ j^*_{res}` followed by the identification
`j^*_{res} ≅ j^*`. -/
lemma Etale.openImmersionLowerShriekUpperStarAdjunction_unit_app
    (F : Sheaf U.smallEtaleTopology A) :
    (Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit.app F =
      (Etale.openImmersionLowerShriekAdjunction A j).unit.app F ≫
        (Etale.upperStarIsoOpenImmersionRestriction A j).inv.app _ :=
  rfl

omit [HasSmallSiteSheafify A] in
/-- For an open immersion `j`, the counit of `j^* ⊣ j_*` is the identification
`j^* ≅ j^*_{res}` followed by the counit of `j^*_{res} ⊣ j_*`. -/
lemma Etale.upperStarLowerStarAdjunction_counit_app_of_isOpenImmersion
    (F : Sheaf U.smallEtaleTopology A) :
    (Etale.upperStarLowerStarAdjunction A j).counit.app F =
      (Etale.upperStarIsoOpenImmersionRestriction A j).hom.app _ ≫
        (Etale.openImmersionRestrictionLowerStarAdjunction A j).counit.app F :=
  (Adjunction.leftAdjointUniq_hom_app_counit _ _ F).symm

/-- For an open immersion `j`, the counit of `j^* ⊣ j_*` is an isomorphism. -/
instance Etale.isIso_upperStarLowerStarAdjunction_counit_app_of_isOpenImmersion
    (F : Sheaf U.smallEtaleTopology A) :
    IsIso ((Etale.upperStarLowerStarAdjunction A j).counit.app F) := by
  rw [Etale.upperStarLowerStarAdjunction_counit_app_of_isOpenImmersion]
  infer_instance

omit [HasSmallSiteSheafify A] in
/-- The comparison `j_! ⟶ j_*` is characterized by its transpose under `j_! ⊣ j^*` and
`j^* ⊣ j_*` being the identity. -/
@[reassoc (attr := simp)]
lemma Etale.unit_map_openImmersionLowerShriekToLowerStar_app_counit
    (F : Sheaf U.smallEtaleTopology A) :
    (Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit.app F ≫
        (j)^*[A].map ((Etale.openImmersionLowerShriekToLowerStar A j).app F) ≫
          (Etale.upperStarLowerStarAdjunction A j).counit.app F = 𝟙 F := by
  rw [Etale.openImmersionLowerShriekUpperStarAdjunction_unit_app,
    Etale.upperStarLowerStarAdjunction_counit_app_of_isOpenImmersion, assoc,
    NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc,
    Etale.openImmersionLowerShriekToLowerStar_app, Functor.map_comp, assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.unit_naturality_assoc, Adjunction.right_triangle_components_assoc]
  simp

omit [HasSmallSiteSheafify A] in
/-- Two maps `j_! X ⟶ j_* Y` agree as soon as their transposes `X ⟶ Y` under `j_! ⊣ j^*` and
`j^* ⊣ j_*` agree. -/
lemma Etale.openImmersionLowerShriek_lowerStar_hom_ext {X Y : Sheaf U.smallEtaleTopology A}
    {f₁ f₂ : (j)_!open[A].obj X ⟶ (j)_*[A].obj Y}
    (h : (Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit.app X ≫
        (j)^*[A].map f₁ ≫ (Etale.upperStarLowerStarAdjunction A j).counit.app Y =
      (Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit.app X ≫
        (j)^*[A].map f₂ ≫ (Etale.upperStarLowerStarAdjunction A j).counit.app Y) :
    f₁ = f₂ := by
  apply ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).homEquiv _ _).injective
  rw [← cancel_mono ((Etale.upperStarLowerStarAdjunction A j).counit.app Y)]
  simpa [Adjunction.homEquiv_unit] using h

end OpenImmersion

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The canonical comparison `ι_f : f_! ⟶ f_*` from the lower shriek to the pushforward
along a morphism `f` admitting a compactification `X --i--> Z --g--> Y`: it is induced by
the canonical map `i_! ⟶ i_*` for the open immersion `i`, using `f_! = g_* ∘ i_!` and the
composition isomorphism `g_* ∘ i_* ≅ (i ≫ g)_* = f_*`. -/
noncomputable def Etale.lowerShriekToLowerStar :
    Etale.lowerShriek A f ⟶ (f)_*[A] :=
  Functor.whiskerRight
      (Etale.openImmersionLowerShriekToLowerStar A (HasCompactification.compactification f).i)
      ((HasCompactification.compactification f).g)_*[A] ≫
    (Etale.lowerStarComp A (HasCompactification.compactification f).i
      (HasCompactification.compactification f).g).hom ≫
    eqToHom (by rw [← (HasCompactification.compactification f).comm])

omit [HasSmallSiteSheafify A] in
/-- The comparison `ι_f` is an isomorphism as soon as the comparison for the open immersion
`i` of the chosen compactification is: the remaining two factors of `ι_f` are an isomorphism
and an `eqToHom` by construction, and whiskering preserves isomorphisms.

This step is purely formal; it uses nothing about `f`. -/
lemma Etale.isIso_lowerShriekToLowerStar_of_isIso
    (h : IsIso (Etale.openImmersionLowerShriekToLowerStar A
      (HasCompactification.compactification f).i)) :
    IsIso (Etale.lowerShriekToLowerStar A f) := by
  rw [Etale.lowerShriekToLowerStar]
  infer_instance

end Comparison

end AlgebraicGeometry
