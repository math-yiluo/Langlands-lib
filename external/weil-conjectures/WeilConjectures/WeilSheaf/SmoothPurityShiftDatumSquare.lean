/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-! # Shifting a compatible coefficient and geometric datum square -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- A square for four functors commuting with shifts remains a square after a common shift. -/
lemma purity_shift_datum_square
    {C A D B : Type*} [Category C] [Category A] [Category D] [Category B]
    [HasShift C ℤ] [HasShift A ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (F : C ⥤ A) (G : A ⥤ B) (H : C ⥤ D) (I : D ⥤ B)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [I.CommShift ℤ]
    (α : H ⋙ I ⟶ F ⋙ G) [α.CommShift ℤ]
    {M : C} {M' : A} {N : D} {N' : B}
    (u : F.obj M ⟶ M') (v : I.obj N ⟶ N')
    (r : H.obj M ⟶ N) (s : G.obj M' ⟶ N')
    (h : α.app M ≫ G.map u ≫ s = I.map r ≫ v) (n : ℤ) :
    α.app (M⟦n⟧) ≫ G.map ((F.commShiftIso n).hom.app M ≫ u⟦n⟧') ≫
        (G.commShiftIso n).hom.app M' ≫ s⟦n⟧' =
      I.map ((H.commShiftIso n).hom.app M ≫ r⟦n⟧') ≫
        (I.commShiftIso n).hom.app N ≫ v⟦n⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc,
    Functor.commShiftIso_hom_naturality_assoc]
  have hα := NatTrans.shift_app_comm α n M
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at hα
  rw [← reassoc_of% hα]
  simp only [← Functor.map_comp, h]

end CategoryTheory
