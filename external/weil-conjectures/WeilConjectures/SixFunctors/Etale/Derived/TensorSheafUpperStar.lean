/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorSheaf

/-!
# The derived tensor product with an étale sheaf and the derived pullback

For `g : Z ⟶ Y`, étale sheaves `c_Y` on `Y` and `c_Z` on `Z` and a morphism
`κ : g^* c_Y ⟶ c_Z`, the comparison `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` of left derived functors
(`AlgebraicGeometry.Etale.leftDerivedTensorRightUpperStarMap`) is, through
`L(- ⊗ c) ≅ - ⊗ᴸ c`, the comparison `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ Lg^* c_Y` of the derived
pullback with the derived tensor product
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`) followed by
`Lg^* c_Y ⟶ c_Z`.

This is the étale counterpart of the second half of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorSheaf`. The pro-étale
lemma `leftDerivedUpperStarTensorComparison_app_app_fac` already has an étale counterpart in
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift`; it is not imported here
(its imports exceed the memory budget of this file) and is reproved inline where needed.

## Main results

- `AlgebraicGeometry.Etale.leftDerivedTensorRightUpperStarMap_app_comp`: the identification of
  `leftDerivedTensorRightUpperStarMap` with the comparison of the derived pullback with the
  derived tensor product.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory HomologicalComplex Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Pullback

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y) [(g)^*[A].PreservesFlat]
  {c_Y : Sheaf Y.smallEtaleTopology A} {c_Z : Sheaf Z.smallEtaleTopology A}
  (κ : (g)^*[A].obj c_Y ⟶ c_Z)

omit [Abelian.HasFunctorialFlatResolution A] [(g)^*[A].PreservesFlat] in
/-- The comparison `g^*(K ⊗ c_Y) ⟶ g^* K ⊗ c_Z` of complexes, computed through the
identifications `K ⊗ c[0] ≅ K ⊗ c` (`CochainComplex.mapBifunctorSingle₂Iso`). -/
lemma mapHomologicalComplex_map_mapBifunctorSingle₂Iso_hom_comp
    (K : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ) :
    ((g)^*[A].mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Y K).hom ≫
      (NatTrans.mapHomologicalComplex (tensorRightUpperStarMap g κ) (.up ℤ)).app K =
    mapBifunctorComparison (δNatTrans (g)^*[A]) (.up ℤ) K ((single _ (.up ℤ) 0).obj c_Y) ≫
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁
        ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
          (single _ (.up ℤ) 0).map κ)) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Z
        (((g)^*[A].mapHomologicalComplex _).obj K)).hom := by
  have h₁ : ((g)^*[A].mapHomologicalComplex _).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Y K).inv ≫
      mapBifunctorComparison (δNatTrans (g)^*[A]) (.up ℤ) K ((single _ (.up ℤ) 0).obj c_Y) ≫
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁
        (singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) ((g)^*[A].obj c_Y)
        (((g)^*[A].mapHomologicalComplex _).obj K)).hom =
      (NatTrans.mapHomologicalComplex (δRightNatTrans (g)^*[A] c_Y) (.up ℤ)).app K :=
    CochainComplex.mapBifunctorComparison_δNatTrans_single₂ (g)^*[A] K c_Y
  have h₂ : (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map κ) (.up ℤ)).app
        (((g)^*[A].mapHomologicalComplex _).obj K) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Z
        (((g)^*[A].mapHomologicalComplex _).obj K)).inv =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) ((g)^*[A].obj c_Y)
        (((g)^*[A].mapHomologicalComplex _).obj K)).inv ≫
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁ (single _ (.up ℤ) 0).map κ) :=
    CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂ (curriedTensor _) κ _
  have h₂' : (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁ (single _ (.up ℤ) 0).map κ) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Z
        (((g)^*[A].mapHomologicalComplex _).obj K)).hom =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) ((g)^*[A].obj c_Y)
        (((g)^*[A].mapHomologicalComplex _).obj K)).hom ≫
      (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map κ) (.up ℤ)).app
        (((g)^*[A].mapHomologicalComplex _).obj K) := by
    rw [← cancel_epi (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) ((g)^*[A].obj c_Y)
        (((g)^*[A].mapHomologicalComplex _).obj K)).inv, ← reassoc_of% h₂, Iso.inv_hom_id,
      Category.comp_id, Iso.inv_hom_id_assoc]
  have h₃ : (NatTrans.mapHomologicalComplex (tensorRightUpperStarMap g κ) (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex (δRightNatTrans (g)^*[A] c_Y) (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map κ) (.up ℤ)).app
          (((g)^*[A].mapHomologicalComplex _).obj K) := by
    rfl
  refine (cancel_epi (((g)^*[A].mapHomologicalComplex (.up ℤ)).map
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Y K).inv)).1 ?_
  erw [Iso.inv_hom_id_map_assoc]
  rw [h₃, MonoidalCategory.whiskerLeft_comp, Category.assoc, h₂']
  erw [reassoc_of% h₁]

omit [Abelian.HasFunctorialFlatResolution A] [(g)^*[A].PreservesFlat] in
/-- The comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ c_Z` on homotopy categories, computed through
`AlgebraicGeometry.Etale.tensorSingleIso`. -/
lemma mapHomotopyCategory_map_tensorSingleIso_hom_app_comp
    (P : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((g)^*[A].mapHomotopyCategory (.up ℤ)).map ((tensorSingleIso c_Y).hom.app P) ≫
        (mapHomotopyCategoryTensorRightUpperStarMap g κ).app P =
      ((mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]).app P).app
          ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c_Y)) ≫
        (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P ◁
          (HomotopyCategory.quotient _ _).map
            ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
              (single _ (.up ℤ) 0).map κ)) ≫
        (tensorSingleIso c_Z).hom.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have hinv (K' : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
      (Functor.mapHomotopyCategoryCompIso (Iso.refl ((g)^*[A] ⋙ tensorRight c_Z))
      (.up ℤ)).inv.app K' = 𝟙 _ := by
    refine (cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K')).1 ?_
    erw [Iso.hom_inv_id_app]
  have hw : ((g)^*[A].mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K) ◁
      (HomotopyCategory.quotient _ _).map
        ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
          (single _ (.up ℤ) 0).map κ) =
      (HomotopyCategory.quotient _ _).map (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁
        ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
          (single _ (.up ℤ) 0).map κ)) := rfl
  have hZ : (tensorSingleIso c_Z).hom.app
      (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) =
      (HomotopyCategory.quotient _ _).map (CochainComplex.mapBifunctorSingle₂Iso
        (curriedTensor _) c_Z (((g)^*[A].mapHomologicalComplex _).obj K)).hom :=
    tensorSingleIso_hom_app_quotient_obj c_Z _
  rw [tensorSingleIso_hom_app_quotient_obj, mapHomotopyCategoryTensorRightUpperStarMap,
    NatTrans.comp_app, NatTrans.comp_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app, hinv]
  erw [Category.id_comp, Category.comp_id]
  erw [hw]
  rw [mapHomotopyCategoryδNatTrans_app_app, hZ, NatTrans.mapHomotopyCategory_app]
  have h := congrArg (HomotopyCategory.quotient (Sheaf Z.smallEtaleTopology A) (.up ℤ)).map
    (mapHomologicalComplex_map_mapBifunctorSingle₂Iso_hom_comp g κ K)
  refine Eq.trans ?_ (h.trans ((Functor.map_comp _ _ _).trans ?_))
  · exact ((HomotopyCategory.quotient (Sheaf Z.smallEtaleTopology A) (.up ℤ)).map_comp _ _).symm
  · exact congrArg (_ ≫ ·) (Functor.map_comp _ _ _)

omit [(g)^*[A].PreservesFlat] in
/-- The counit `AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensorCounit` on objects:
`Lg^*(μ Qh)` followed by the counit of `Lg^*`. -/
@[reassoc]
lemma leftDerivedUpperStarDerivedTensorCounit_app_app
    (X M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarDerivedTensorCounit A g).app X).app M =
      L((g)^*[A]).map (Functor.LaxMonoidal.μ DerivedCategory.Qh X M) ≫
        (g)^*[A].leftDerivedFunctorCounit.app (X ⊗ M) :=
  rfl

omit [(g)^*[A].PreservesFlat] in
/-- The counit `AlgebraicGeometry.Etale.derivedTensorLeftDerivedUpperStarCounit` on objects:
the counits of `Lg^*` on both factors followed by `μ Qh`. -/
lemma derivedTensorLeftDerivedUpperStarCounit_app_app
    (X M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((derivedTensorLeftDerivedUpperStarCounit A g).app X).app M =
      ((g)^*[A].leftDerivedFunctorCounit.app X ▷ L((g)^*[A]).obj (DerivedCategory.Qh.obj M)) ≫
        (DerivedCategory.Qh.obj (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj X) ◁
          (g)^*[A].leftDerivedFunctorCounit.app M) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ :=
  rfl

/-- **The comparison `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` is induced by the comparison of the derived
pullback with the derived tensor product**: through `L(- ⊗ c) ≅ - ⊗ᴸ c`, the comparison
`AlgebraicGeometry.Etale.leftDerivedTensorRightUpperStarMap` is
`Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ Lg^* c_Y ⟶ Lg^* K ⊗ᴸ c_Z`. -/
lemma leftDerivedTensorRightUpperStarMap_app_comp
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedTensorRightUpperStarMap g κ).app K ≫
        (leftDerivedTensorRightIso c_Z).hom.app (L((g)^*[A]).obj K) =
      L((g)^*[A]).map ((leftDerivedTensorRightIso c_Y).hom.app K) ≫
        ((leftDerivedUpperStarTensorComparison A g).app K).app (derivedSingle c_Y) ≫
        ((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).map (leftDerivedUpperStarDerivedSingleMap g κ) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_iso_Qh_obj_kFlatUpperStar g K
  have key {F G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology A)} (τ₁ τ₂ : F ⟶ G)
      (h : τ₁.app (DerivedCategory.Qh.obj P) = τ₂.app (DerivedCategory.Qh.obj P)) :
      τ₁.app K = τ₂.app K := by
    rw [← cancel_epi (F.map e.hom), τ₁.naturality, τ₂.naturality, h]
  refine key (leftDerivedTensorRightUpperStarMap g κ ≫
    Functor.whiskerLeft L((g)^*[A]) (leftDerivedTensorRightIso c_Z).hom)
    (Functor.whiskerRight (leftDerivedTensorRightIso c_Y).hom L((g)^*[A]) ≫
      (leftDerivedUpperStarTensorComparison A g).flipApp (derivedSingle c_Y) ≫
      Functor.whiskerLeft L((g)^*[A])
        ((-⊗ᴸ-(Z)[A]).flip.map (leftDerivedUpperStarDerivedSingleMap g κ))) ?_
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.flipApp, flipFunctor_map_app_app, Functor.flip_map_app]
  have := isIso_derivedTensorSingleCounit_app c_Z hP
  have : IsIso ((g)^*[A].leftDerivedFunctorCounit.app P) := NatIso.isIso_app_of_isIso _ _
  have hL : (leftDerivedTensorRightUpperStarMap g κ).app (DerivedCategory.Qh.obj P) ≫
      (leftDerivedTensorRightIso c_Z).hom.app (L((g)^*[A]).obj (DerivedCategory.Qh.obj P)) ≫
      ((-⊗ᴸ-(Z)[A]).flip.obj (derivedSingle c_Z)).map
        ((g)^*[A].leftDerivedFunctorCounit.app P) ≫
      (derivedTensorSingleCounit c_Z).app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P) =
      L((g)^*[A]).map ((tensorRight c_Y).leftDerivedFunctorCounit.app P) ≫
        (g)^*[A].leftDerivedFunctorCounit.app
          (((tensorRight c_Y).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryTensorRightUpperStarMap g κ).app P) := by
    have h := leftDerivedTensorRightUpperStarMap_app_comp_counit g κ P
    rw [leftDerivedUpperStarTensorRightCounit, leftDerivedTensorRightUpperStarCounit,
      NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] at h
    rw [← (leftDerivedTensorRightIso c_Z).hom.naturality_assoc]
    dsimp only [Functor.comp_obj]
    rw [leftDerivedTensorRightIso_hom_app_comp]
    exact h
  rw [← cancel_mono (((-⊗ᴸ-(Z)[A]).flip.obj (derivedSingle c_Z)).map
      ((g)^*[A].leftDerivedFunctorCounit.app P) ≫
        (derivedTensorSingleCounit c_Z).app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P)),
    Category.assoc, hL, ← leftDerivedTensorRightIso_hom_app_comp, Functor.map_comp,
    Category.assoc, Category.assoc, cancel_epi]
  have hε := (g)^*[A].leftDerivedFunctorCounit.naturality ((tensorSingleIso c_Y).hom.app P)
  simp only [Functor.comp_map] at hε
  rw [derivedTensorSingleCounit_app, derivedTensorSingleCounit_app, Functor.map_comp,
    Category.assoc, reassoc_of% hε, ← Functor.map_comp]
  erw [mapHomotopyCategory_map_tensorSingleIso_hom_app_comp]
  dsimp only [Functor.flip_obj_obj, curriedTensor_obj_obj]
  -- The defining property of `leftDerivedUpperStarTensorComparison` at `(P, c_Y)`; this is
  -- `leftDerivedUpperStarTensorComparison_app_app_fac` (in
  -- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift`, whose imports are too
  -- large to be imported here), with `Qh.map δ` in place of `postcompose₂MapWhiskeringLeft₂`.
  have := isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar A g
  have := isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor A g
  -- Compare the comparison with its definition as natural transformations, not componentwise:
  -- the componentwise comparison is very slow for the kernel.
  have e : leftDerivedUpperStarTensorComparison A g =
      Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
        (leftDerivedUpperStarDerivedTensorCounit A g)
        (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A])
          DerivedCategory.Qh) :=
    rfl
  have hfac : ((leftDerivedUpperStarTensorComparison A g).app (DerivedCategory.Qh.obj P)).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
          ((single _ (.up ℤ) 0).obj c_Y))) ≫
        ((derivedTensorLeftDerivedUpperStarCounit A g).app P).app
          ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c_Y)) =
      ((leftDerivedUpperStarDerivedTensorCounit A g).app P).app
          ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c_Y)) ≫
        DerivedCategory.Qh.map (((mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]).app P).app
          ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c_Y))) :=
    by
      rw [e]
      exact Functor.leftDerived₂NatTrans_app_app _ (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
        (leftDerivedUpperStarDerivedTensorCounit A g)
        (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A])
          DerivedCategory.Qh) _ _
  rw [Functor.map_comp, Functor.map_comp, ← leftDerivedUpperStarDerivedTensorCounit_app_app_assoc,
    ← reassoc_of% hfac,
    derivedTensorLeftDerivedUpperStarCounit_app_app]
  simp only [Category.assoc, leftDerivedUpperStarDerivedSingleMap, derivedTensor,
    curriedTensor_obj_map, Functor.flip_obj_map, curriedTensor_map_app]
  exact congrArg (_ ≫ ·)
    (Functor.LaxMonoidal.whiskerRight_whiskerLeft_μ_map_whiskerLeft_assoc DerivedCategory.Qh
      _ _ _ _)

end Pullback

end AlgebraicGeometry.Etale
