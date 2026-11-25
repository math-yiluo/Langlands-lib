/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerAction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceLowerStar

/-!
# Unit transports under a change of left adjoints

Towards the identity of `ProEtale.CondensedRing.galoisAction_eq_unitTransport_of_counit`, this
file shows that the unit transport `Fg(η_s) ≫ r ≫ Fsg(c⁻¹)` along a composition isomorphism
`r : Fs ⋙ Fg ⟶ Fsg` of right adjoints does not depend on the choice of left adjoints, up to the
comparisons `Adjunction.leftAdjointUniq`
(`CategoryTheory.unitTransport_app_leftAdjointUniq`), using that the conjugate `c` of `r`
transforms accordingly (`CategoryTheory.conjugateEquiv_symm_leftAdjointUniq`). For pro-étale
sheaves along weakly étale morphisms this replaces the pullbacks `g^*` by the restrictions
`j_g^*` along the localization functors, on which the unit transport is computed on sections.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

/-- **Conjugates of a composition isomorphism under a change of left adjoints**: the inverse
conjugate of `r : Fs ⋙ Fg ⟶ Fsg` for the left adjoints `Gg', Gs', Gsg'` is that for `Gg, Gs, Gsg`
composed with the comparisons `leftAdjointUniq`. -/
lemma conjugateEquiv_symm_leftAdjointUniq {X Y Y' : Type*} [Category X] [Category Y]
    [Category Y'] {Gg Gg' : X ⥤ Y} {Fg : Y ⥤ X} {Gs Gs' : Y ⥤ Y'} {Fs : Y' ⥤ Y}
    {Gsg Gsg' : X ⥤ Y'} {Fsg : Y' ⥤ X} (ag : Gg ⊣ Fg) (ag' : Gg' ⊣ Fg) (as : Gs ⊣ Fs)
    (as' : Gs' ⊣ Fs) (asg : Gsg ⊣ Fsg) (asg' : Gsg' ⊣ Fsg) (r : Fs ⋙ Fg ⟶ Fsg) :
    (conjugateEquiv (ag'.comp as') asg').symm r =
      (asg.leftAdjointUniq asg').inv ≫ (conjugateEquiv (ag.comp as) asg).symm r ≫
        Functor.whiskerRight (ag.leftAdjointUniq ag').hom Gs ≫
        Functor.whiskerLeft Gg' (as.leftAdjointUniq as').hom := by
  rw [Equiv.symm_apply_eq, ← conjugateEquiv_comp (ag'.comp as') asg asg',
    conjugateEquiv_leftAdjointUniq_inv, Category.comp_id,
    ← conjugateEquiv_comp (ag'.comp as') (ag.comp as) asg, Equiv.apply_symm_apply,
    ← conjugateEquiv_comp (ag'.comp as') (ag'.comp as) (ag.comp as),
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, conjugateEquiv_leftAdjointUniq_hom,
    conjugateEquiv_leftAdjointUniq_hom]
  simp

/-- **The unit transport does not depend on the choice of left adjoints**: computed with left
adjoints `Gg', Gs', Gsg'` of `Fg, Fs, Fsg` and the conjugate `c'` of the composition isomorphism
`r`, it is the one computed with `Gg, Gs, Gsg` and `c`, up to the comparisons
`leftAdjointUniq`. -/
lemma unitTransport_app_leftAdjointUniq {X Y Y' : Type*} [Category X] [Category Y]
    [Category Y'] {Gg Gg' : X ⥤ Y} {Fg : Y ⥤ X} {Gs Gs' : Y ⥤ Y'} {Fs : Y' ⥤ Y}
    {Gsg Gsg' : X ⥤ Y'} {Fsg : Y' ⥤ X} (ag : Gg ⊣ Fg) (ag' : Gg' ⊣ Fg) (as : Gs ⊣ Fs)
    (as' : Gs' ⊣ Fs) (asg : Gsg ⊣ Fsg) (asg' : Gsg' ⊣ Fsg) (r : Fs ⋙ Fg ⟶ Fsg)
    (c : Gsg ≅ Gg ⋙ Gs) (c' : Gsg' ≅ Gg' ⋙ Gs')
    (hc : c.hom = (conjugateEquiv (ag.comp as) asg).symm r)
    (hc' : c'.hom = (conjugateEquiv (ag'.comp as') asg').symm r) (H : X) :
    Fg.map (as.unit.app (Gg.obj H)) ≫ r.app (Gs.obj (Gg.obj H)) ≫ Fsg.map (c.inv.app H) =
      Fg.map ((ag.leftAdjointUniq ag').hom.app H) ≫ Fg.map (as'.unit.app (Gg'.obj H)) ≫
        r.app (Gs'.obj (Gg'.obj H)) ≫ Fsg.map (c'.inv.app H) ≫
        Fsg.map ((asg.leftAdjointUniq asg').inv.app H) := by
  rw [conjugateEquiv_symm_leftAdjointUniq ag ag' as as' asg asg', ← hc] at hc'
  have hci : c.inv.app H = Gs.map ((ag.leftAdjointUniq ag').hom.app H) ≫
      (as.leftAdjointUniq as').hom.app (Gg'.obj H) ≫ c'.inv.app H ≫
      (asg.leftAdjointUniq asg').inv.app H := by
    rw [← cancel_epi (c.hom.app H), Iso.hom_inv_id_app]
    have h := congr_app hc' H
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
    have h2 : c.hom.app H ≫ Gs.map ((ag.leftAdjointUniq ag').hom.app H) ≫
        (as.leftAdjointUniq as').hom.app (Gg'.obj H) =
        (asg.leftAdjointUniq asg').hom.app H ≫ c'.hom.app H := by
      rw [h, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% h2]
    simp
  have hr := r.naturality (Gs.map ((ag.leftAdjointUniq ag').hom.app H) ≫
    (as.leftAdjointUniq as').hom.app (Gg'.obj H))
  have hη := as.unit.naturality ((ag.leftAdjointUniq ag').hom.app H)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Functor.map_comp, Category.assoc] at hr hη
  rw [hci]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hr, ← Fg.map_comp_assoc, ← hη, Fg.map_comp_assoc,
    ← Fg.map_comp_assoc (as.unit.app (Gg'.obj H)), Adjunction.unit_leftAdjointUniq_hom_app]

end CategoryTheory

