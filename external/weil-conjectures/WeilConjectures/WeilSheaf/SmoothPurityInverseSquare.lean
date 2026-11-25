/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Inverting the horizontal maps of a comparison square -/

@[expose] public section

namespace CategoryTheory

lemma purity_inverse_square {C : Type*} [Category C]
    {A B A' B' : C} (i : A ≅ B) (j : A' ≅ B')
    (u : A ⟶ A') (v : B ⟶ B') (h : u ≫ j.hom = i.hom ≫ v) :
    i.inv ≫ u = v ≫ j.inv := by
  apply (cancel_mono j.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h,
    Iso.inv_hom_id_assoc]

/-- Cancel a leading compositor without expanding a concrete category instance. -/
lemma purity_factor_from_compositor {C : Type*} [Category C]
    {A B T : C} (i : A ≅ B) (v : B ⟶ T) (w : A ⟶ T)
    (h : i.hom ≫ v = w) : v = i.inv ≫ w := by
  rw [← h, Iso.inv_hom_id_assoc]

/-- A factorization equation with all compositor components left functor-indexed. -/
lemma purity_factor_component
    {C₀ C : Type*} [Category C₀] [Category C]
    (P : C₀ ⥤ C) (Q : C ⥤ C) (R : C₀ ⥤ C)
    (i : R ≅ P ⋙ Q) (j : R ≅ P) (b : P ⋙ Q ≅ P) (hb : b = i.symm ≪≫ j)
    (M : C₀) {T : C} (u : Q.obj (P.obj M) ⟶ T) (v : P.obj M ⟶ T)
    (w : R.obj M ⟶ T)
    (hi : i.hom.app M ≫ u = w) (hj : j.hom.app M ≫ v = w) :
    u = b.hom.app M ≫ v := by
  subst b
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hj, ← hi, Iso.inv_hom_id_app_assoc]

/-- Coefficient change preserves a factorization through compatible compositors. -/
lemma purity_coefficient_factor_component
    {C₀ C D₀ D : Type*} [Category C₀] [Category C] [Category D₀] [Category D]
    (P : C₀ ⥤ C) (Q : C ⥤ C) (R : C₀ ⥤ C)
    (P' : D₀ ⥤ D) (Q' : D ⥤ D) (R' : D₀ ⥤ D)
    (F₀ : C₀ ⥤ D₀) (F : C ⥤ D)
    (α : P ⋙ F ≅ F₀ ⋙ P') (β : Q ⋙ F ≅ F ⋙ Q') (γ : R ⋙ F ≅ F₀ ⋙ R')
    (i : R ≅ P ⋙ Q) (j : R' ≅ P' ⋙ Q') (k : R ≅ P) (k' : R' ≅ P')
    (b : P ⋙ Q ≅ P) (b' : P' ⋙ Q' ≅ P')
    (hb : b = i.symm ≪≫ k) (hb' : b' = j.symm ≪≫ k') (M : C₀)
    (hcomp : γ.hom.app M ≫ j.hom.app (F₀.obj M) =
      F.map (i.hom.app M) ≫ β.hom.app (P.obj M) ≫ Q'.map (α.hom.app M))
    (hcongr : γ.hom.app M ≫ k'.hom.app (F₀.obj M) =
      F.map (k.hom.app M) ≫ α.hom.app M) :
    F.map (b.hom.app M) ≫ α.hom.app M =
      β.hom.app (P.obj M) ≫ Q'.map (α.hom.app M) ≫
        b'.hom.app (F₀.obj M) := by
  subst b
  subst b'
  have hi : F.map (i.inv.app M) ≫ γ.hom.app M =
      (β.hom.app (P.obj M) ≫ Q'.map (α.hom.app M)) ≫ j.inv.app (F₀.obj M) := by
    simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] using
      purity_inverse_square (F.mapIso (i.app M)) (j.app (F₀.obj M))
        (γ.hom.app M) (β.hom.app (P.obj M) ≫ Q'.map (α.hom.app M)) hcomp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  rw [← hcongr, ← Category.assoc, hi, Category.assoc, Category.assoc]

end CategoryTheory
