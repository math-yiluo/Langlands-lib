/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySingleComparisonSquare
import all Mathlib.Algebra.Homology.Localization

/-! # Passing a comparison from homotopy categories to cochain complexes -/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- Read a comparison through the quotient functor on cochain complexes. -/
noncomputable def purityCochainComparisonOfHomotopy
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (η : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso C).inv LF ≫
    whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) η ≫
    whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (DerivedCategory.quotientCompQhIso D).hom

/-- On a complex, all the quotient comparisons are identity maps. -/
private lemma purityCochainComparisonOfHomotopy_app
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (η : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex C ℤ) :
    (purityCochainComparisonOfHomotopy F LF η).app K =
      η.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) := by
  simp only [purityCochainComparisonOfHomotopy, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app]
  change LF.map (𝟙 _) ≫ η.app _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  simp only [Functor.map_id, Category.id_comp, Category.comp_id]
  erw [Category.comp_id]
  rfl

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- A square compatible with the homotopy comparisons is compatible with the
corresponding comparisons on complexes. -/
lemma purityCochainComparisonOfHomotopy_square
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
    (K : CochainComplex C ℤ) :
    α.app (DerivedCategory.Q.obj K) ≫
        LI.map ((purityCochainComparisonOfHomotopy H LH ηH).app K) ≫
        (purityCochainComparisonOfHomotopy I LI ηI).app
          ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      LG.map ((purityCochainComparisonOfHomotopy F LF ηF).app K) ≫
        (purityCochainComparisonOfHomotopy G LG ηG).app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app K) := by
  simp only [purityCochainComparisonOfHomotopy_app]
  exact h ((HomotopyCategory.quotient C (.up ℤ)).obj K)

end CategoryTheory.Functor
