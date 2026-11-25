/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Restricting a comparison square to complexes in degree zero -/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- Restrict a comparison on complexes to the embedding in degree zero. -/
noncomputable def puritySingleComparisonOfCochain
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (η : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.singleFunctor C 0 ⋙ LF ⟶ F ⋙ DerivedCategory.singleFunctor D 0 :=
  whiskerRight (DerivedCategory.singleFunctorIsoCompQ C 0).hom LF ≫
    whiskerLeft (HomologicalComplex.single C (.up ℤ) 0) η ≫
    whiskerRight (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom
      DerivedCategory.Q ≫
    whiskerLeft F (DerivedCategory.singleFunctorIsoCompQ D 0).inv

lemma puritySingleComparisonOfCochain_app
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (η : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : C) :
    (puritySingleComparisonOfCochain F LF η).app P =
      η.app ((HomologicalComplex.single C (.up ℤ) 0).obj P) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app P) := by
  simp [puritySingleComparisonOfCochain, DerivedCategory.singleFunctorIsoCompQ]

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- A comparison square on cochain complexes gives the same square in degree zero.
No exactness of the four ordinary functors is required. -/
lemma puritySingleComparisonOfCochain_square
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ A) (I : A ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory B)
    (LH : DerivedCategory C ⥤ DerivedCategory A)
    (LI : DerivedCategory A ⥤ DerivedCategory B)
    (ηF : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ηG : DerivedCategory.Q ⋙ LG ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ηH : DerivedCategory.Q ⋙ LH ⟶ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ηI : DerivedCategory.Q ⋙ LI ⟶ I.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α : LF ⋙ LG ⟶ LH ⋙ LI) (e : F ⋙ G ⟶ H ⋙ I)
    (h : ∀ K : CochainComplex C ℤ,
      α.app (DerivedCategory.Q.obj K) ≫ LI.map (ηH.app K) ≫
          ηI.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        LG.map (ηF.app K) ≫ ηG.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app K))
    (P : C) :
    α.app ((DerivedCategory.singleFunctor C 0).obj P) ≫
        LI.map ((puritySingleComparisonOfCochain H LH ηH).app P) ≫
        (puritySingleComparisonOfCochain I LI ηI).app (H.obj P) =
      LG.map ((puritySingleComparisonOfCochain F LF ηF).app P) ≫
        (puritySingleComparisonOfCochain G LG ηG).app (F.obj P) ≫
        (DerivedCategory.singleFunctor B 0).map (e.app P) := by
  simp only [puritySingleComparisonOfCochain_app, Functor.map_comp, Category.assoc]
  have hI := ηI.naturality
    ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app P)
  have hG := ηG.naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app P)
  dsimp only [Functor.comp_map] at hI hG
  rw [reassoc_of% hI, reassoc_of% hG]
  erw [reassoc_of% (h ((HomologicalComplex.single C (.up ℤ) 0).obj P))]
  congr 2
  change _ = DerivedCategory.Q.map
    ((G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app P)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj P)) ≫
      DerivedCategory.Q.map ((HomologicalComplex.single B (.up ℤ) 0).map (e.app P))
  simp only [← Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Functor.map_id, Functor.comp_obj, Category.id_comp]
  change e.app P ≫ I.map (𝟙 (H.obj P)) ≫ 𝟙 (I.obj (H.obj P)) =
    G.map (𝟙 (F.obj P)) ≫ 𝟙 (G.obj (F.obj P)) ≫ e.app P ≫ 𝟙 (I.obj (H.obj P))
  simp only [Functor.map_id, Category.id_comp, Category.comp_id]

end CategoryTheory.Functor
