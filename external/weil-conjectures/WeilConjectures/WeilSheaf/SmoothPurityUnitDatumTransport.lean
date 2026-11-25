/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Functor.TwoSquare

/-! # Transporting a unit datum from pullback to inverse pushforward -/

@[expose] public section

namespace CategoryTheory

/-- A comparison that preserves a specified unit map continues to do so after
replacing either endofunctor by an isomorphic one. -/
lemma purity_unitDatum_transport
    {C D : Type*} [Category C] [Category D]
    (E : C ⥤ D) (A B : C ⥤ C) (A' B' : D ⥤ D)
    (cA : E ⋙ A' ⟶ A ⋙ E) (cB : E ⋙ B' ⟶ B ⋙ E)
    (i : A ≅ B) (j : A' ≅ B') {M : C} {U : D} (e : E.obj M ≅ U)
    (a : A.obj M ⟶ M) (b : B.obj M ⟶ M) (u : A'.obj U ⟶ U)
    (hc : cA.app M = j.hom.app (E.obj M) ≫ cB.app M ≫ E.map (i.inv.app M))
    (hab : i.hom.app M ≫ b = a)
    (hu : A'.map e.inv ≫ cA.app M ≫ E.map a ≫ e.hom = u) :
    B'.map e.inv ≫ cB.app M ≫ E.map b ≫ e.hom = j.inv.app U ≫ u := by
  rw [hc, ← hab, E.map_comp] at hu
  simp only [Category.assoc] at hu
  rw [← E.map_comp_assoc, Iso.inv_hom_id_app, E.map_id, Category.id_comp] at hu
  apply (cancel_epi (j.hom.app U)).mp
  rw [Iso.hom_inv_id_app_assoc, ← j.hom.naturality_assoc]
  exact hu

/-- The natural-square version performs component normalization before any
concrete categories or equivalences are substituted. -/
lemma purity_unitDatum_transport_of_square
    {C D : Type*} [Category C] [Category D]
    (E : C ⥤ D) (A B : C ⥤ C) (A' B' : D ⥤ D)
    (cA : E ⋙ A' ⟶ A ⋙ E) (cB : E ⋙ B' ⟶ B ⋙ E)
    (i : A ≅ B) (j : A' ≅ B') {M : C} {U : D} (e : E.obj M ≅ U)
    (a : A.obj M ⟶ M) (b : B.obj M ⟶ M) (u : A'.obj U ⟶ U)
    (hc : TwoSquare.mk E A A' E cA =
      ((TwoSquare.mk E B B' E cB).whiskerRight j.hom).whiskerLeft i.inv)
    (hab : i.hom.app M ≫ b = a)
    (hu : A'.map e.inv ≫ cA.app M ≫ E.map a ≫ e.hom = u) :
    B'.map e.inv ≫ cB.app M ≫ E.map b ≫ e.hom = j.inv.app U ≫ u := by
  apply purity_unitDatum_transport E A B A' B' cA cB i j e a b u _ hab hu
  have h := NatTrans.congr_app hc M
  simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using h

end CategoryTheory
