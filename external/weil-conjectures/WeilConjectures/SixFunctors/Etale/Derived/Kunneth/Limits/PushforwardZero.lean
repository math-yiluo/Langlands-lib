/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageTransition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingleZero

/-!
# Transition maps of stages in degree zero

For a stage `α = (T, S, g, π, w)` (`AlgebraicGeometry.Etale.LimitStage`) and a sheaf `G` on `W`,
`H⁰(π^* Rg_* w^*(G[0]))` is identified with the underived `π^* g_* w^* G`
(`AlgebraicGeometry.Etale.LimitStage.homologyZeroIso`), and under these identifications `H⁰` of
the transition map of a morphism of stages is the underived transition map
`π_β^* g_{β*} w_β^* G ≅ π_α^* s^* g_{β*} w_β^* G ⟶ π_α^* g_{α*} t^* w_β^* G ≅ π_α^* g_{α*} w_α^* G`
built from the underived base-change map
(`AlgebraicGeometry.Etale.LimitStage.homology_map_transition_homologyZeroIso`).

The comparison is made on complexes: the derived transition map, precomposed with the units
`Qh(π^* g_* w^* K) ⟶ π^* Rg_* w^*(Qh K)`, is the image of the levelwise underived transition
map (`AlgebraicGeometry.Etale.LimitStage.homotopyUnit_comp_transition`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- `H⁰` of the image of a sheaf placed in degree `0` under an additive functor. -/
noncomputable def singleHomologyZeroIso (F : C ⥤ D) [F.Additive] (X : C) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj X)).homology 0 ≅ F.obj X :=
  HomologicalComplex.homologyMapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj X)

set_option linter.flexible false in
/-- `H⁰` of the map of single complexes induced by a natural transformation `τ` is `τ`. -/
lemma homologyMap_mapHomologicalComplex_single_singleHomologyZeroIso (G G' : C ⥤ D)
    [G.Additive] [G'.Additive] (τ : G ⟶ G') (X : C) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj X)) 0 ≫ (singleHomologyZeroIso G' X).hom =
      (singleHomologyZeroIso G X).hom ≫ τ.app X := by
  let e := (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).app X
  let e' := (HomologicalComplex.singleMapHomologicalComplex G' (.up ℤ) 0).app X
  have hw : (NatTrans.mapHomologicalComplex τ (.up ℤ)).app
      ((HomologicalComplex.single C (.up ℤ) 0).obj X) ≫ e'.hom =
      e.hom ≫ (HomologicalComplex.single D (.up ℤ) 0).map (τ.app X) := by
    ext i
    by_cases hi : i = 0
    · subst hi
      simp [e, e', HomologicalComplex.singleMapHomologicalComplex,
        HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq]
      erw [Category.comp_id]
      rfl
    · exact (G.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)).eq_of_src _ _
  simp only [singleHomologyZeroIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  rw [← HomologicalComplex.homologyMap_comp_assoc]
  erw [hw]
  rw [HomologicalComplex.homologyMap_comp, Category.assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_naturality]
  simp only [Category.assoc]
  rfl


lemma inv_comp_comp_eq_of_comp_eq {E : Type*} [Category* E] {A B C D F : E} (x : A ⟶ B)
    (y : B ⟶ C) (e₂ : C ≅ D) (e₁ : A ≅ F) (z : F ⟶ D) (h : x ≫ y ≫ e₂.hom = e₁.hom ≫ z) :
    e₁.inv ≫ x ≫ y = z ≫ e₂.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc e₁.hom, Iso.eq_comp_inv, Category.assoc, h]
end CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace LimitStage

variable {B W : Scheme.{u}}

/-- The complex `π^* g_* w^* K` of the underived functors of a stage, on the bounded below
homotopy category. -/
noncomputable abbrev homotopyObj (α : LimitStage B W)
    (K : HomotopyCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HomotopyCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ((α.π)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
    (((α.g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
      (((α.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K))

/-- The comparison map `Qh(π^* g_* w^* K) ⟶ π^* Rg_* w^*(Qh K)`, built from the unit of the
right derived functor of `g_*`. -/
noncomputable def homotopyUnit (α : LimitStage B W)
    (K : HomotopyCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.Qh.obj (homotopyObj Λ α K) ⟶
      (functor Λ α).obj (DerivedCategory.Plus.Qh.obj K) :=
  ((α.π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app
      (((α.g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
        (((α.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K)) ≫
    D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
      (((α.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.app
          (((α.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K) ≫
        R+((α.g)_*[ModuleCat.{u + 1} Λ]).map
          (((α.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app K))

/-- The underived functor `G ↦ π^* g_* w^* G` of a stage. -/
noncomputable abbrev sheafFunctor (α : LimitStage B W) :
    Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (α.w)^*[ModuleCat.{u + 1} Λ] ⋙ (α.g)_*[ModuleCat.{u + 1} Λ] ⋙ (α.π)^*[ModuleCat.{u + 1} Λ]

/-- The underived transition map of a morphism of stages `φ : α ⟶ β`:
`π_β^* g_{β*} w_β^* G ≅ π_α^* s^* g_{β*} w_β^* G ⟶ π_α^* g_{α*} t^* w_β^* G ≅
π_α^* g_{α*} w_α^* G`, the middle map being the base-change map of the square `(t, s)`. -/
noncomputable def sheafTransition {α β : LimitStage B W} (φ : Hom α β) :
    sheafFunctor Λ β ⟶ sheafFunctor Λ α :=
  Functor.whiskerLeft ((β.w)^*[ModuleCat.{u + 1} Λ] ⋙ (β.g)_*[ModuleCat.{u + 1} Λ])
      (Etale.upperStarComp (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (β.w)^*[ModuleCat.{u + 1} Λ]
          (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩) ≫
        Functor.whiskerRight
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv
          (α.g)_*[ModuleCat.{u + 1} Λ])
      (α.π)^*[ModuleCat.{u + 1} Λ]

lemma sheafTransition_app {α β : LimitStage B W} (φ : Hom α β)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sheafTransition Λ φ).app G =
      (Etale.upperStarComp (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom.app
          (((β.g)_*[ModuleCat.{u + 1} Λ]).obj (((β.w)^*[ModuleCat.{u + 1} Λ]).obj G)) ≫
        ((α.π)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).app
              (((β.w)^*[ModuleCat.{u + 1} Λ]).obj G) ≫
            ((α.g)_*[ModuleCat.{u + 1} Λ]).map
              ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv.app G)) := by
  rfl

/-- The levelwise underived transition map on the bounded below homotopy categories. -/
noncomputable def homotopyTransition {α β : LimitStage B W} (φ : Hom α β)
    (K : HomotopyCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    homotopyObj Λ β K ⟶ homotopyObj Λ α K :=
  (NatTrans.mapHomotopyCategoryPlus
      (Etale.upperStarComp (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom).app
      (((β.g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
        (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K)) ≫
    ((α.π)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.map
      ((NatTrans.mapHomotopyCategoryPlus
          (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩)).app
          (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K) ≫
        ((α.g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus
            (Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv).app K))

/-- The derived transition map, precomposed with the comparison maps
`AlgebraicGeometry.Etale.LimitStage.homotopyUnit`, is the image of the levelwise underived
transition map. -/
lemma homotopyUnit_comp_transition {α β : LimitStage B W} (φ : Hom α β)
    (K : HomotopyCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    homotopyUnit Λ β K ≫ (transition Λ φ).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map (homotopyTransition Λ φ K) ≫ homotopyUnit Λ α K := by
  -- the coefficient side: the composition isomorphism on complexes
  have hw0 := Etale.upperStarCompDerivedPlus_hom_app_factorsh (ModuleCat.{u + 1} Λ) φ.t β.w α.w
    φ.ww.symm K
  have hQ : DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).hom).app K) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv).app K) = 𝟙 _ := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp,
      Iso.hom_inv_id, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
  have hw : (((φ.t)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app
        (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K) ≫
      D+((φ.t)^*[ModuleCat.{u + 1} Λ]).map
        (((β.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app K)) ≫
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv.app
        (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv).app K) ≫
      ((α.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app K := by
    rw [← cancel_epi ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t β.w α.w
      φ.ww.symm).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      D+((φ.t)^*[ModuleCat.{u + 1} Λ]).map
        (((β.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      ((φ.t)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.hom.app
        (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K))]
    conv_rhs => rw [hw0]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, reassoc_of% hQ, Iso.hom_inv_id_app]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp
  -- the base side: the composition isomorphism on complexes
  have hπ0 := Etale.upperStarCompDerivedPlus_hom_app_factorsh (ModuleCat.{u + 1} Λ) α.π φ.s β.π
    φ.wπ.symm (((β.g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
      (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K))
  have hπ := inv_comp_comp_eq_of_comp_eq _ _
    (((α.π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.app
      (((φ.s)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
        (((β.g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
          (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K))))
    (((β.π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.app
      (((β.g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
        (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K))) _ hπ0
  simp only [Iso.app_inv] at hπ
  -- naturality of the composition isomorphism of the bases
  have n1 := (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom.naturality
    (((β.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.app
        (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K) ≫
      R+((β.g)_*[ModuleCat.{u + 1} Λ]).map
        (((β.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app K))
  -- naturality of the derived base change map
  have n2 := congrArg D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).naturality
      (((β.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.app K))
  -- the derived base change map on complexes
  have hf := congrArg D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
    (Etale.derivedBaseChangeMapPlus_fac_app (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩
      (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K))
  -- naturality of the unit of `R+(α.g)_*`
  have n3 := congrArg D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
    (((α.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.naturality
      ((NatTrans.mapHomotopyCategoryPlus
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv).app K))
  have hw' := congrArg (fun x ↦ D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
    (R+((α.g)_*[ModuleCat.{u + 1} Λ]).map x)) hw
  -- naturality of the factorization of `D+(α.π)^*`
  have n4 := (((α.π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.naturality
    ((NatTrans.mapHomotopyCategoryPlus
      (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩)).app
      (((β.w)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K)))
  have n5 := (((α.π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusFactorsh.inv.naturality
    (((α.g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.map
      ((NatTrans.mapHomotopyCategoryPlus
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv).app K)))
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at n1 n2 hf n3 hw' n4 n5
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at n2
  rw [transition_app, Etale.baseChange_eq_derivedBaseChangeMapPlus]
  simp only [homotopyUnit, homotopyTransition, Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2, reassoc_of% hf, hw']
  erw [← reassoc_of% n3]
  rw [reassoc_of% hπ]
  erw [← reassoc_of% n4, ← reassoc_of% n5]

end LimitStage

end AlgebraicGeometry.Etale
