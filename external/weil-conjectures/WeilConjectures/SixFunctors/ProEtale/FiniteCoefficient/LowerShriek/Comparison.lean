/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!

# The canonical comparison `f_! ⟶ f_*`

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison`.

For a morphism `f : X ⟶ Y` admitting a compactification `X --i--> Z --g--> Y`, this file
constructs the canonical natural transformation

`ι_f : f_! ⟶ f_*`

from the lower shriek to the pushforward on pro-étale sheaves.

The construction proceeds through the adjoint triple `i_! ⊣ i^* ⊣ i_*` of the open
immersion `i`:

- Since `i` is a monomorphism, the localization functor `MorphismProperty.Over.map` of
  the small pro-étale sites along `i` is fully faithful
  (`CategoryTheory.MorphismProperty.Over.full_map`), so the unit of the site-level
  adjunction `MorphismProperty.Over.mapPullbackAdj` is an isomorphism, and hence so is
  the counit of the induced sheaf-level adjunction `i^* ⊣ i_*`
  (`CategoryTheory.Adjunction.isIso_sheafPushforwardContinuous_counit`); this expresses
  that the restriction of a pushforward along an open immersion is the original sheaf.
- Inverting this counit and contracting with the counit of `i_! ⊣ i^*` yields the
  canonical map `i_! ⟶ i_*` (`ProEtale.openImmersionLowerShriekToLowerStar`).
- Pushing forward along `g` and composing with the composition isomorphism
  `ProEtale.lowerStarComp` gives `ι_f : f_! = g_* ∘ i_! ⟶ g_* ∘ i_* ≅ f_*`
  (`ProEtale.lowerShriekToLowerStar`).

For a proper morphism `f`, the comparison `ι_f` is an isomorphism; that statement needs the
vanishing of both sides off the range of `i`, which is where closedness of that range and
`HasZeroObject A` enter, and is proved downstream in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper`.

## Main definitions

- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekToLowerStar`: the canonical map
  `i_! ⟶ i_*` for an open immersion `i`.
- `AlgebraicGeometry.ProEtale.lowerShriekToLowerStar`: the canonical comparison
  `ι_f : f_! ⟶ f_*` for `f` admitting a compactification.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar`:
  the restriction `i^*` of the comparison is an isomorphism, for *any* open immersion `i`.
- `AlgebraicGeometry.ProEtale.isIso_lowerShriekToLowerStar_of_isIso`: the formal reduction
  of the comparison for `f` to the comparison for the open immersion of its
  compactification.

-/

@[expose] public section

universe w u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open ProEtale

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The canonical natural transformation `i_! ⟶ i_*` from the extension by zero to the
pushforward along an open immersion, obtained from the adjoint triple `i_! ⊣ i^* ⊣ i_*`:
insert the inverse of the counit of `i^* ⊣ i_*` and contract with the counit of
`i_! ⊣ i^*`. -/
noncomputable def ProEtale.openImmersionLowerShriekToLowerStar :
    (j)_!open[A] ⟶ (j)_*[A] :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (inv (ProEtale.openImmersionRestrictionLowerStarAdjunction A j).counit)
      (j)_!open[A] ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (j)_*[A]
      (ProEtale.openImmersionLowerShriekAdjunction A j).counit ≫
    (Functor.rightUnitor _).hom

set_option backward.isDefEq.respectTransparency false in
/-- The components of the comparison `j_! ⟶ j_*`: the unitors and the associator in its
definition are identities, so at `F` it is `j_!` of the inverted counit of `j^* ⊣ j_*`,
followed by the counit of `j_! ⊣ j^*` at `j_* F`. -/
lemma ProEtale.openImmersionLowerShriekToLowerStar_app
    (F : Sheaf (Scheme.ProEt.topology U) A) :
    (ProEtale.openImmersionLowerShriekToLowerStar A j).app F =
      (j)_!open[A].map
          ((inv (ProEtale.openImmersionRestrictionLowerStarAdjunction A j).counit).app F) ≫
        (ProEtale.openImmersionLowerShriekAdjunction A j).counit.app ((j)_*[A].obj F) := by
  simp only [ProEtale.openImmersionLowerShriekToLowerStar, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.id_obj,
    NatIso.isIso_inv_app, Functor.map_inv, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, id_comp, IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- **`j^*` of the comparison `j_! ⟶ j_*` is an isomorphism**, for any open immersion `j`
and with no hypothesis on the range of `j`.

Both factors of `ProEtale.openImmersionLowerShriekToLowerStar_app` become invertible after
applying `j^*`: the first is `j_!` of an isomorphism, and the second is
`ProEtale.isIso_openImmersionRestriction_map_lowerShriekAdjunction_counit`, which holds
because `j_!` is fully faithful along an open immersion. -/
instance ProEtale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar
    (F : Sheaf (Scheme.ProEt.topology U) A) :
    IsIso ((ProEtale.openImmersionRestriction A j).map
      ((ProEtale.openImmersionLowerShriekToLowerStar A j).app F)) := by
  rw [ProEtale.openImmersionLowerShriekToLowerStar_app, Functor.map_comp]
  infer_instance

end OpenImmersion

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The canonical comparison `ι_f : f_! ⟶ f_*` from the lower shriek to the pushforward
along a morphism `f` admitting a compactification `X --i--> Z --g--> Y`: it is induced by
the canonical map `i_! ⟶ i_*` for the open immersion `i`, using `f_! = g_* ∘ i_!` and the
composition isomorphism `g_* ∘ i_* ≅ (i ≫ g)_* = f_*`. -/
noncomputable def ProEtale.lowerShriekToLowerStar :
    ProEtale.lowerShriek A f ⟶ (f)_*[A] :=
  Functor.whiskerRight
      (ProEtale.openImmersionLowerShriekToLowerStar A
        (HasCompactification.compactification f).i)
      ((HasCompactification.compactification f).g)_*[A] ≫
    (ProEtale.lowerStarComp A (HasCompactification.compactification f).i
      (HasCompactification.compactification f).g).hom ≫
    eqToHom (by rw [← (HasCompactification.compactification f).comm])

/-- The comparison `ι_f` is an isomorphism as soon as the comparison for the open immersion
`i` of the chosen compactification is: the remaining two factors of `ι_f` are an isomorphism
and an `eqToHom` by construction, and whiskering preserves isomorphisms.

This step is purely formal; it uses nothing about `f`. -/
lemma ProEtale.isIso_lowerShriekToLowerStar_of_isIso
    (h : IsIso (ProEtale.openImmersionLowerShriekToLowerStar A
      (HasCompactification.compactification f).i)) :
    IsIso (ProEtale.lowerShriekToLowerStar A f) := by
  rw [ProEtale.lowerShriekToLowerStar]
  infer_instance

end Comparison

end AlgebraicGeometry
