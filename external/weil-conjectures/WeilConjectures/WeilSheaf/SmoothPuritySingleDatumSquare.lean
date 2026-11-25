/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySingleComparisonSquare

/-! # Transporting an ordinary datum square to complexes in degree zero -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
  [Abelian C] [Abelian D] [Abelian A] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- A comparison square for single complexes transports any compatible ordinary
geometric datum and its coefficient comparison. -/
lemma purity_single_datum_square
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ A) (I : A ⥤ B)
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory B)
    (LH : DerivedCategory C ⥤ DerivedCategory A)
    (LI : DerivedCategory A ⥤ DerivedCategory B)
    (ηF : DerivedCategory.singleFunctor C 0 ⋙ LF ⟶ F ⋙ DerivedCategory.singleFunctor D 0)
    (ηG : DerivedCategory.singleFunctor D 0 ⋙ LG ⟶ G ⋙ DerivedCategory.singleFunctor B 0)
    (ηH : DerivedCategory.singleFunctor C 0 ⋙ LH ⟶ H ⋙ DerivedCategory.singleFunctor A 0)
    (ηI : DerivedCategory.singleFunctor A 0 ⋙ LI ⟶ I ⋙ DerivedCategory.singleFunctor B 0)
    (α : LF ⋙ LG ⟶ LH ⋙ LI) (e : F ⋙ G ⟶ H ⋙ I)
    {M : C} {M' : A} {N : D} {N' : B}
    (u : H.obj M ⟶ M') (v : G.obj N ⟶ N')
    (r : F.obj M ⟶ N) (s : I.obj M' ⟶ N')
    (hcomp : α.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        LI.map (ηH.app M) ≫ ηI.app (H.obj M) =
      LG.map (ηF.app M) ≫ ηG.app (F.obj M) ≫
        (DerivedCategory.singleFunctor B 0).map (e.app M))
    (h : e.app M ≫ I.map u ≫ s = G.map r ≫ v) :
    α.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        LI.map (ηH.app M ≫ (DerivedCategory.singleFunctor A 0).map u) ≫
        ηI.app M' ≫ (DerivedCategory.singleFunctor B 0).map s =
      LG.map (ηF.app M ≫ (DerivedCategory.singleFunctor D 0).map r) ≫
        ηG.app N ≫ (DerivedCategory.singleFunctor B 0).map v := by
  simp only [Functor.map_comp, Category.assoc]
  have hu := ηI.naturality u
  have hr := ηG.naturality r
  dsimp only [Functor.comp_map] at hu hr
  rw [reassoc_of% hu, reassoc_of% hr, reassoc_of% hcomp]
  simp only [← Functor.map_comp, h]

end CategoryTheory
