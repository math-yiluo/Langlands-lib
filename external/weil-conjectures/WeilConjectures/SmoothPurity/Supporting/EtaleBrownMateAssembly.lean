/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Generic inverse mate assembly -/
@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory

/-- The inverse mate assembly used by the Brown scalar square.
Source: Zheng, Lemma 5.16; categorical mate-pasting.
(blueprint: lem-pur-etale-brown-mate-assembly).
Proof: apply injectivity of the right mate equivalence to the pasted horizontal
and vertical squares, use mate composition and whiskering identities, and
evaluate the resulting equality at the required object. -/
theorem etaleBrownMatePasting
    {CA DA CB DB EA FA EB FB : Type*}
    [Category CA] [Category DA] [Category CB] [Category DB]
    [Category EA] [Category FA] [Category EB] [Category FB]
    {LA : CA ⥤ DA} {RA : DA ⥤ CA} {LB : CB ⥤ DB} {RB : DB ⥤ CB}
    {LA' : EA ⥤ FA} {RA' : FA ⥤ EA} {LB' : EB ⥤ FB} {RB' : FB ⥤ EB}
    (aA : LA ⊣ RA) (aB : LB ⊣ RB) (bA : LA' ⊣ RA') (bB : LB' ⊣ RB')
    {U : CB ⥤ CA} {V : DB ⥤ DA} {U' : EB ⥤ EA} {V' : FB ⥤ FA}
    {GA : CA ⥤ EA} {HA : DA ⥤ FA} {GB : CB ⥤ EB} {HB : DB ⥤ FB}
    (aa : TwoSquare GA LA LA' HA) (ab : TwoSquare GB LB LB' HB)
    (k : TwoSquare U LB LA V) (i : TwoSquare U' LB' LA' V')
    (t : U ⋙ GA ⟶ GB ⋙ U') (s : V ⋙ HA ⟶ HB ⋙ V')
    (h : ∀ M : DB,
      t.app (RB.obj M) ≫ U'.map ((mateEquiv aB bB ab).app M) ≫
          (mateEquiv bB bA i).app (HB.obj M) =
        GA.map ((mateEquiv aB aA k).app M) ≫
          (mateEquiv aA bA aa).app (V.obj M) ≫ RA'.map (s.app M))
    : (ab.hComp i).whiskerTop t = (k.hComp aa).whiskerBottom s := by
  apply (mateEquiv aB bA).injective
  rw [show mateEquiv aB bA ((ab.hComp i).whiskerTop t) =
      (mateEquiv aB bA (ab.hComp i)).whiskerRight t from by
        simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
          mateEquiv_whiskerTop_whiskerBottom aB bA (ab.hComp i) t (𝟙 _),
    mateEquiv_whiskerBottom, mateEquiv_vcomp aB bB bA, mateEquiv_vcomp aB aA bA]
  ext M
  simpa only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using h M

end
