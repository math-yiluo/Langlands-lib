/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCochainComparison

/-! # Restricting a homotopy comparison square to degree zero -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
  [Abelian C] [Abelian D] [Abelian A] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- The homotopy comparison square implies its degree-zero counterpart. -/
lemma puritySingleComparisonOfHomotopy_square
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ A) (I : A ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory B)
    (LH : DerivedCategory C ⥤ DerivedCategory A)
    (LI : DerivedCategory A ⥤ DerivedCategory B)
    (ηF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ηG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ηH : DerivedCategory.Qh ⋙ LH ⟶ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ηI : DerivedCategory.Qh ⋙ LI ⟶ I.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (α : LF ⋙ LG ⟶ LH ⋙ LI) (e : F ⋙ G ⟶ H ⋙ I)
    (h : ∀ K : HomotopyCategory C (.up ℤ),
      α.app (DerivedCategory.Qh.obj K) ≫ LI.map (ηH.app K) ≫
          ηI.app ((H.mapHomotopyCategory (.up ℤ)).obj K) =
        LG.map (ηF.app K) ≫ ηG.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e (.up ℤ)).app K))
    (P : C) :
    α.app ((DerivedCategory.singleFunctor C 0).obj P) ≫
        LI.map ((puritySingleComparisonOfCochain H LH
          (purityCochainComparisonOfHomotopy H LH ηH)).app P) ≫
        (puritySingleComparisonOfCochain I LI
          (purityCochainComparisonOfHomotopy I LI ηI)).app (H.obj P) =
      LG.map ((puritySingleComparisonOfCochain F LF
        (purityCochainComparisonOfHomotopy F LF ηF)).app P) ≫
        (puritySingleComparisonOfCochain G LG
          (purityCochainComparisonOfHomotopy G LG ηG)).app (F.obj P) ≫
        (DerivedCategory.singleFunctor B 0).map (e.app P) :=
  puritySingleComparisonOfCochain_square F G H I LF LG LH LI _ _ _ _ α e
    (purityCochainComparisonOfHomotopy_square F G H I LF LG LH LI ηF ηG ηH ηI α e h) P

end CategoryTheory.Functor
