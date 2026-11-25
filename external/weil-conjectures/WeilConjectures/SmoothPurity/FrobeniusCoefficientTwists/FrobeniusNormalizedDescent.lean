/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-! # Normalized isomorphism descent along a localization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory
namespace WeilConjectures.FrobeniusCoefficientTwists

/-- A normalized inverse descends uniquely across a localization on an iso-closed property.
Source: coefficient-twist clause 4; Mathlib Localization.fullyFaithfulWhiskeringLeft.
(blueprint: lem-weil-frobenius-normalized-localization-descent).
Proof: descend the specified natural transformation through full faithfulness of
whiskering. On every representative its component has the prescribed inverse.
Essential surjectivity transports invertibility to every object satisfying the
property, giving the natural inverse there. Naturality and essential surjectivity
also force uniqueness from the representative normalization. -/
theorem normalized_descent
    {A B C : Type*} [Category A] [Category B] [Category C]
    (L : A ⥤ B) (W : MorphismProperty A) [L.IsLocalization W]
    (P : ObjectProperty B) [P.IsClosedUnderIsomorphisms]
    (F G : B ⥤ C) (H I : A ⥤ C) (b : L ⋙ F ≅ H) (c : L ⋙ G ≅ I)
    (a : H ⟶ I) (n : ∀ X, P (L.obj X) → (G.obj (L.obj X) ≅ F.obj (L.obj X)))
    (hn : ∀ X (hX : P (L.obj X)),
      (b.hom.app X ≫ a.app X ≫ c.inv.app X) ≫ (n X hX).hom = 𝟙 _) :
    ∃! e : P.ι ⋙ G ≅ P.ι ⋙ F, ∀ X (hX : P (L.obj X)),
      e.hom.app ⟨L.obj X, hX⟩ = (n X hX).hom := by
  let : L.EssSurj := Localization.essSurj L W
  let ff := Localization.fullyFaithfulWhiskeringLeft L W C
  let beta := b.hom ≫ a ≫ c.inv
  let t : F ⟶ G := ff.preimage beta
  have ht (X : A) : t.app (L.obj X) = b.hom.app X ≫ a.app X ≫ c.inv.app X :=
    NatTrans.congr_app (ff.map_preimage beta) X
  have hi (K : P.FullSubcategory) : IsIso (t.app K.obj) := by
    let X := L.objPreimage K.obj
    let d := L.objObjPreimageIso K.obj
    have hX : P (L.obj X) := P.prop_of_iso d.symm K.property
    have hx : t.app (L.obj X) = (n X hX).inv := by
      apply (cancel_mono (n X hX).hom).1
      rw [ht]
      exact (hn X hX).trans (n X hX).inv_hom_id.symm
    have h : IsIso (t.app (L.obj X)) := by
      rw [hx]
      exact (n X hX).isIso_inv
    rw [← NatTrans.isIso_app_iff_of_iso t d]
    exact h
  let : ∀ K : P.FullSubcategory, IsIso ((Functor.whiskerLeft P.ι t).app K) := hi
  let : IsIso (Functor.whiskerLeft P.ι t) := NatIso.isIso_of_isIso_app _
  let e := (asIso (Functor.whiskerLeft P.ι t)).symm
  have he (X : A) (hX : P (L.obj X)) :
      e.hom.app ⟨L.obj X, hX⟩ = (n X hX).hom := by
    have : IsIso (t.app (L.obj X)) := hi ⟨_, hX⟩
    change (inv (Functor.whiskerLeft P.ι t)).app _ = _
    rw [NatIso.isIso_inv_app]
    change inv (t.app (L.obj X)) = _
    apply IsIso.inv_eq_of_hom_inv_id
    rw [ht]
    exact hn X hX
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  let X := L.objPreimage K.obj
  let d := L.objObjPreimageIso K.obj
  have hX : P (L.obj X) := P.prop_of_iso d.symm K.property
  let d' : (⟨L.obj X, hX⟩ : P.FullSubcategory) ≅ K := P.isoMk d
  have hc : e'.hom.app ⟨L.obj X, hX⟩ = e.hom.app ⟨L.obj X, hX⟩ :=
    (he' X hX).trans (he X hX).symm
  apply (cancel_epi ((P.ι ⋙ G).map d'.hom)).1
  rw [e'.hom.naturality, e.hom.naturality, hc]

end WeilConjectures.FrobeniusCoefficientTwists
