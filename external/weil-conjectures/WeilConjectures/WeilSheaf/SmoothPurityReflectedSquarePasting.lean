/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityReflectedSquareComponents
public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp

/-! # Restriction commutes with pasting of compact-support exchange squares -/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  {PA : ObjectProperty A} {PB : ObjectProperty B} {PC : ObjectProperty C}
  {PA' : ObjectProperty A'} {PB' : ObjectProperty B'} {PC' : ObjectProperty C'}
  {F : A ⥤ B} {G : B ⥤ C} {F' : A' ⥤ B'} {G' : B' ⥤ C'}
  {TA : A ⥤ A'} {TB : B ⥤ B'} {TC : C ⥤ C'}
  {FR : PA.FullSubcategory ⥤ PB.FullSubcategory}
  {GR : PB.FullSubcategory ⥤ PC.FullSubcategory}
  {FR' : PA'.FullSubcategory ⥤ PB'.FullSubcategory}
  {GR' : PB'.FullSubcategory ⥤ PC'.FullSubcategory}
  (cF : FR ⋙ PB.ι ≅ PA.ι ⋙ F) (cG : GR ⋙ PC.ι ≅ PB.ι ⋙ G)
  (cF' : FR' ⋙ PB'.ι ≅ PA'.ι ⋙ F') (cG' : GR' ⋙ PC'.ι ≅ PB'.ι ⋙ G')
  (hA : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ TA).obj K))
  (hB : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ TB).obj K))
  (hC : ∀ K : PC.FullSubcategory, PC' ((PC.ι ⋙ TC).obj K))
  (eF : F ⋙ TB ≅ TA ⋙ F') (eG : G ⋙ TC ≅ TB ⋙ G')

/-- Restricting a pasted square gives the paste of the two restricted squares, using
exactly the pasted inclusion comparisons for the composite direct images. -/
lemma preimageIso_liftSquareWithComparisons_comp :
    preimageIso_liftSquareWithComparisons
        (Adjunction.compForgetIso cF cG) (Adjunction.compForgetIso cF' cG')
        hA hC (Adjunction.compForgetIso eF eG) =
      Adjunction.compForgetIso
        (preimageIso_liftSquareWithComparisons cF cF' hA hB eF)
        (preimageIso_liftSquareWithComparisons cG cG' hB hC eG) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply PC'.ι.map_injective
  simp only [ObjectProperty.ι_map]
  rw [preimageIso_liftSquareWithComparisons_hom_app_hom]
  simp only [Adjunction.compForgetIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp,
    Functor.comp_obj, Category.assoc, FullSubcategory.comp_hom]
  rw [preimageIso_liftSquareWithComparisons_hom_app_hom]
  simp only [Category.assoc]
  have hn := cG'.inv.naturality
    ((preimageIso_liftSquareWithComparisons cF cF' hA hB eF).hom.app K)
  dsimp only [Functor.comp_map, ObjectProperty.ι_map] at hn
  have hh := congrArg
    (fun t ↦ TC.map (cG.hom.app (FR.obj K)) ≫ eG.hom.app (FR.obj K).obj ≫ t) hn
  simp only [preimageIso_liftSquareWithComparisons_hom_app_hom,
    Functor.map_comp, Category.assoc] at hh
  have he := eG.hom.naturality (cF.hom.app K)
  dsimp +instances only [Functor.comp_map, Functor.comp_obj,
    ObjectProperty.ι_obj] at he hh ⊢
  rw [← reassoc_of% he] at hh
  exact hh


end CategoryTheory.ObjectProperty

namespace CategoryTheory.Adjunction

variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  {F : A ⥤ B} {G : B ⥤ C} {F' : A' ⥤ B'} {G' : B' ⥤ C'}
  {TA SA : A ⥤ A'} {TB SB : B ⥤ B'} {TC SC : C ⥤ C'}
  (aA : SA ≅ TA) (aB : SB ≅ TB) (aC : SC ≅ TC)
  (eF : F ⋙ TB ≅ TA ⋙ F') (eG : G ⋙ TC ≅ TB ⋙ G')

/-- Changing the vertical coordinates of a pasted square cancels the comparison at
its middle vertex. -/
lemma compForgetIso_conjugate :
    compForgetIso
        (Functor.isoWhiskerLeft F aB ≪≫ eF ≪≫ Functor.isoWhiskerRight aA.symm F')
        (Functor.isoWhiskerLeft G aC ≪≫ eG ≪≫ Functor.isoWhiskerRight aB.symm G') =
      Functor.isoWhiskerLeft (F ⋙ G) aC ≪≫ compForgetIso eF eG ≪≫
        Functor.isoWhiskerRight aA.symm (F' ⋙ G') := by
  ext K
  simp only [compForgetIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp,
    Functor.comp_obj, Functor.comp_map, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {F : A ⥤ B} {F' : A' ⥤ B'} {T S : A ⥤ A'} {U V : B ⥤ B'}

/-- Changing vertical coordinates and changing back leaves a square unchanged. -/
lemma isoWhisker_conjugate_cancel (a : U ≅ V) (b : T ≅ S) (e : F ⋙ U ≅ T ⋙ F') :
    isoWhiskerLeft F a ≪≫
        (isoWhiskerLeft F a.symm ≪≫ e ≪≫ isoWhiskerRight b F') ≪≫
        isoWhiskerRight b.symm F' = e := by
  ext K
  simp [← F'.map_comp]

end CategoryTheory.Functor
