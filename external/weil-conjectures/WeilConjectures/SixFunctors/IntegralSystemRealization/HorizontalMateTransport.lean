/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! Horizontal composition is invariant under compatible natural isomorphisms. -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace WeilConjectures.IntegralSystemRealization

/-- Naturality and inverse cancellation transport a horizontal pasting equation.
Source: the naturality axiom and the inverse laws for natural isomorphisms.
(blueprint: lem-sf-horizontal-mate-transport).
Proof: cancel the isomorphism at the common target, commute the two compositor
comparisons and the three square comparisons, and use naturality to move the
remaining comparison maps to the ends. The remaining middle equality is hp₀. -/
theorem horizontalMateTransport
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {K K' : A ⥤ B} {L L' : B ⥤ E} {I I' : C ⥤ D} {J J' : D ⥤ F}
    {R R' : A ⥤ C} {P P' : B ⥤ D} {Q Q' : E ⥤ F}
    {Kc Kc' : A ⥤ E} {Ic Ic' : C ⥤ F}
    {ck' : K' ⋙ L' ≅ Kc'} {ci' : I' ⋙ J' ≅ Ic'}
    {g₁' : R' ⋙ I' ⟶ K' ⋙ P'} {g₂' : P' ⋙ J' ⟶ L' ⋙ Q'}
    {g₀' : R' ⋙ Ic' ⟶ Kc' ⋙ Q'}
    (eK : K ≅ K') (eL : L ≅ L') (eI : I ≅ I') (eJ : J ≅ J')
    (eR : R ≅ R') (eP : P ≅ P') (eQ : Q ≅ Q')
    (eKc : Kc ≅ Kc') (eIc : Ic ≅ Ic')
    (ck : K ⋙ L ≅ Kc) (ci : I ⋙ J ≅ Ic)
    (g₁ : R ⋙ I ⟶ K ⋙ P) (g₂ : P ⋙ J ⟶ L ⋙ Q)
    (g₀ : R ⋙ Ic ⟶ Kc ⋙ Q)
    (hk : ∀ M, ck.hom.app M ≫ eKc.hom.app M =
      eL.hom.app (K.obj M) ≫ L'.map (eK.hom.app M) ≫ ck'.hom.app M)
    (hi : ∀ M, ci.hom.app M ≫ eIc.hom.app M =
      eJ.hom.app (I.obj M) ≫ J'.map (eI.hom.app M) ≫ ci'.hom.app M)
    (h₁ : ∀ M, g₁.app M ≫ eP.hom.app (K.obj M) ≫ P'.map (eK.hom.app M) =
      eI.hom.app (R.obj M) ≫ I'.map (eR.hom.app M) ≫ g₁'.app M)
    (h₂ : ∀ M, g₂.app M ≫ eQ.hom.app (L.obj M) ≫ Q'.map (eL.hom.app M) =
      eJ.hom.app (P.obj M) ≫ J'.map (eP.hom.app M) ≫ g₂'.app M)
    (h₀ : ∀ M, g₀.app M ≫ eQ.hom.app (Kc.obj M) ≫ Q'.map (eKc.hom.app M) =
      eIc.hom.app (R.obj M) ≫ Ic'.map (eR.hom.app M) ≫ g₀'.app M)
    (M : A) :
    (ci'.hom.app (R'.obj M) ≫ g₀'.app M ≫ Q'.map (ck'.inv.app M) =
      J'.map (g₁'.app M) ≫ g₂'.app (K'.obj M)) →
    ci.hom.app (R.obj M) ≫ g₀.app M ≫ Q.map (ck.inv.app M) =
      J.map (g₁.app M) ≫ g₂.app (K.obj M) := by
  intro hp₀
  have hp : ci'.hom.app (R'.obj M) ≫ g₀'.app M =
      (J'.map (g₁'.app M) ≫ g₂'.app (K'.obj M)) ≫ Q'.map (ck'.hom.app M) := by
    have h := hp₀
    rw [← Category.assoc] at h
    exact (Iso.comp_inv_eq (Q'.mapIso (ck'.app M))).1 h
  rw [← Category.assoc]
  apply (Iso.comp_inv_eq (Q.mapIso (ck.app M))).2
  change ci.hom.app (R.obj M) ≫ g₀.app M =
    (J.map (g₁.app M) ≫ g₂.app (K.obj M)) ≫ Q.map (ck.hom.app M)
  apply (cancel_mono (eQ.hom.app (Kc.obj M) ≫ Q'.map (eKc.hom.app M))).1
  simp only [Category.assoc]
  rw [h₀, ← Category.assoc (ci.hom.app (R.obj M)), hi]
  simp only [Category.assoc]
  rw [← ci'.hom.naturality_assoc (eR.hom.app M)]
  rw [hp]
  simp only [Functor.comp_map, Category.assoc]
  rw [eQ.hom.naturality_assoc (ck.hom.app M)]
  rw [← Q'.map_comp, hk]
  simp only [Functor.map_comp, Functor.comp_obj]
  rw [reassoc_of% (h₂ (K.obj M))]
  have hn := g₂'.naturality (eK.hom.app M)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have hj := eJ.hom.naturality (g₁.app M)
  simp only [Functor.comp_obj] at hj
  rw [reassoc_of% hj]
  simp only [← J'.map_comp_assoc]
  rw [h₁]

end WeilConjectures.IntegralSystemRealization
