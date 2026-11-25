/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp

/-!
# Composition of normalized derived squares

The usual composition proof for derived exact squares uses their unit equations.
It therefore applies when an exact pullback is acyclic for a particular pushforward,
even if it does not preserve all K-injective complexes. This is the situation for
pullback to the geometric fibre with its Weil datum.
-/

@[expose] public section

open CategoryTheory Abelian Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₁] [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₂] [HasKInjectiveResolutions C₃]
  {P₁ : C₁ ⥤ D₁} {P₂ : C₂ ⥤ D₂} {P₃ : C₃ ⥤ D₃} [P₁.Additive] [P₂.Additive] [P₃.Additive]
  {rX₁₂ : C₂ ⥤ C₁} {rX₂₃ : C₃ ⥤ C₂} {rX₁₃ : C₃ ⥤ C₁}
  [rX₁₂.Additive] [PreservesFiniteLimits rX₁₂] [PreservesFiniteColimits rX₁₂]
  [rX₂₃.Additive] [PreservesFiniteLimits rX₂₃] [PreservesFiniteColimits rX₂₃]
  [rX₁₃.Additive] [PreservesFiniteLimits rX₁₃] [PreservesFiniteColimits rX₁₃]
  {rY₁₂ : D₂ ⥤ D₁} {rY₂₃ : D₃ ⥤ D₂} {rY₁₃ : D₃ ⥤ D₁}
  [rY₁₂.Additive] [PreservesFiniteLimits rY₁₂] [PreservesFiniteColimits rY₁₂]
  [rY₂₃.Additive] [PreservesFiniteLimits rY₂₃] [PreservesFiniteColimits rY₂₃]
  [rY₁₃.Additive] [PreservesFiniteLimits rY₁₃] [PreservesFiniteColimits rY₁₃]


/-- Normalized right-derived comparisons compose whenever their ordinary squares compose. -/
theorem traceDerivedSquare_comp (e₁₂ : P₂ ⋙ rY₁₂ ≅ rX₁₂ ⋙ P₁)
    (e₂₃ : P₃ ⋙ rY₂₃ ≅ rX₂₃ ⋙ P₂) (e₁₃ : P₃ ⋙ rY₁₃ ≅ rX₁₃ ⋙ P₁)
    (b₁₂ : P₂.rightDerivedFunctor ⋙ rY₁₂.mapDerivedCategory ≅
      rX₁₂.mapDerivedCategory ⋙ P₁.rightDerivedFunctor)
    (b₂₃ : P₃.rightDerivedFunctor ⋙ rY₂₃.mapDerivedCategory ≅
      rX₂₃.mapDerivedCategory ⋙ P₂.rightDerivedFunctor)
    (b₁₃ : P₃.rightDerivedFunctor ⋙ rY₁₃.mapDerivedCategory ≅
      rX₁₃.mapDerivedCategory ⋙ P₁.rightDerivedFunctor)
    (h₁₂ : ∀ K : HomotopyCategory C₂ (.up ℤ),
      rY₁₂.mapDerivedCategoryFactorsh.inv.app ((P₂.mapHomotopyCategory (.up ℤ)).obj K) ≫
        rY₁₂.mapDerivedCategory.map (P₂.rightDerivedFunctorUnit.app K) ≫
        b₁₂.hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₁₂.hom (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (rX₁₂ ⋙ P₁)) (.up ℤ)).inv.app K) ≫
        P₁.rightDerivedFunctorUnit.app ((rX₁₂.mapHomotopyCategory (.up ℤ)).obj K) ≫
        P₁.rightDerivedFunctor.map (rX₁₂.mapDerivedCategoryFactorsh.inv.app K))
    (h₂₃ : ∀ K : HomotopyCategory C₃ (.up ℤ),
      rY₂₃.mapDerivedCategoryFactorsh.inv.app ((P₃.mapHomotopyCategory (.up ℤ)).obj K) ≫
        rY₂₃.mapDerivedCategory.map (P₃.rightDerivedFunctorUnit.app K) ≫
        b₂₃.hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₂₃.hom (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (rX₂₃ ⋙ P₂)) (.up ℤ)).inv.app K) ≫
        P₂.rightDerivedFunctorUnit.app ((rX₂₃.mapHomotopyCategory (.up ℤ)).obj K) ≫
        P₂.rightDerivedFunctor.map (rX₂₃.mapDerivedCategoryFactorsh.inv.app K))
    (h₁₃ : ∀ K : HomotopyCategory C₃ (.up ℤ),
      (rightDerivedFunctorCompMapDerivedCategoryUnit P₃ rY₁₃).app K ≫
        b₁₃.hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₁₃.hom (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (rX₁₃ ⋙ P₁)) (.up ℤ)).inv.app K) ≫
        P₁.rightDerivedFunctorUnit.app ((rX₁₃.mapHomotopyCategory (.up ℤ)).obj K) ≫
        P₁.rightDerivedFunctor.map (rX₁₃.mapDerivedCategoryFactorsh.inv.app K))
    (cX : rX₂₃ ⋙ rX₁₂ ≅ rX₁₃) (cY : rY₂₃ ⋙ rY₁₂ ≅ rY₁₃)
    (h : ∀ K, e₁₃.hom.app K = cY.inv.app (P₃.obj K) ≫ rY₁₂.map (e₂₃.hom.app K) ≫
      e₁₂.hom.app (rX₂₃.obj K) ≫ P₁.map (cX.hom.app K))
    (K : DerivedCategory C₃) :
    b₁₃.hom.app K =
      ((mapDerivedCategoryCompIso rY₂₃ rY₁₂) ≪≫ mapDerivedCategoryNatIso cY).inv.app
          (P₃.rightDerivedFunctor.obj K) ≫
        rY₁₂.mapDerivedCategory.map (b₂₃.hom.app K) ≫
        b₁₂.hom.app (rX₂₃.mapDerivedCategory.obj K) ≫
        P₁.rightDerivedFunctor.map
          (((mapDerivedCategoryCompIso rX₂₃ rX₁₂) ≪≫
            mapDerivedCategoryNatIso cX).hom.app K) := by
  let τ : P₃.rightDerivedFunctor ⋙ rY₁₃.mapDerivedCategory ⟶
      rX₁₃.mapDerivedCategory ⋙ P₁.rightDerivedFunctor :=
    whiskerLeft P₃.rightDerivedFunctor
        ((mapDerivedCategoryCompIso rY₂₃ rY₁₂) ≪≫ mapDerivedCategoryNatIso cY).inv ≫
      (associator _ _ _).inv ≫ whiskerRight b₂₃.hom _ ≫
      (associator _ _ _).hom ≫ whiskerLeft _ b₁₂.hom ≫
      (associator _ _ _).inv ≫
      whiskerRight ((mapDerivedCategoryCompIso rX₂₃ rX₁₂) ≪≫ mapDerivedCategoryNatIso cX).hom _
  suffices H : b₁₃.hom = τ by
    simpa [τ] using NatTrans.congr_app H K
  refine rightDerived_ext _ (rightDerivedFunctorCompMapDerivedCategoryUnit P₃ rY₁₃)
    (HomotopyCategory.quasiIso C₃ (ComplexShape.up ℤ)) _ _ _ ?_
  ext X
  simp only [NatTrans.comp_app, whiskerLeft_app, τ, Iso.trans_inv, Iso.trans_hom,
    associator_inv_app, associator_hom_app, whiskerRight_app, Category.id_comp,
    Functor.map_comp, Category.assoc]
  rw [h₁₃, rightDerivedFunctorCompMapDerivedCategoryUnit_app_eq,
    mapHomotopyCategoryCompIso_refl_inv_app, mapHomotopyCategoryCompIso_refl_inv_app,
    DerivedCategory.Qh.map_id, DerivedCategory.Qh.map_id, Category.id_comp, Category.id_comp,
    Category.assoc]
  erw [(mapDerivedCategoryNatIso cY).inv.naturality_assoc,
    (mapDerivedCategoryCompIso rY₂₃ rY₁₂).inv.naturality_assoc]
  rw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_inv_app_assoc]
  erw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_hom_app_assoc]
  rw [mapHomotopyCategoryCompIso_refl_inv_app, DerivedCategory.Qh.map_id, Category.id_comp,
    Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    h₂₃, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Category.assoc]
  simp only [Category.assoc]
  erw [← NatTrans.naturality_assoc rY₁₂.mapDerivedCategoryFactorsh.inv,
    ← NatTrans.naturality_assoc rY₁₂.mapDerivedCategoryFactorsh.inv]
  rw [← Functor.comp_map R(P₂) D(rY₁₂)]
  have hn := b₁₂.hom.naturality
    (rX₂₃.mapDerivedCategoryFactorsh.inv.app X)
  erw [reassoc_of% hn]
  erw [reassoc_of% h₁₂]
  simp only [← Functor.map_comp]
  erw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_inv_app_assoc]
  rw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app, Functor.map_comp,
    Functor.map_comp]
  erw [← P₁.rightDerivedFunctorUnit.naturality_assoc,
    ← P₁.rightDerivedFunctorUnit.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  congr 2
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [mapHomotopyCategoryCompIso_refl_inv_app, mapHomotopyCategoryCompIso_refl_hom_app,
    Category.comp_id, Category.id_comp]
  erw [Functor.map_id, Category.id_comp]
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, h]
  rfl


end CategoryTheory.Functor
