/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsCompCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull

/-!

# (Pull) on the image of the homotopy category

The derived (Pull) `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso` is, modulo the
counits of the left derived functors, the underived (Pull) `ProEtale.CondensedRing.pullIso`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso_hom_app_comp_counit`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

private lemma comp_mapHomotopyCategoryCompIso_refl
    {V W W' D : Type*} [Category* V] [Category* W] [Category* W'] [Category* D]
    [Preadditive V] [Preadditive W] [Preadditive W']
    {J : Type*} (c : ComplexShape J) (F : V ⥤ W) (G : W ⥤ W')
    [F.Additive] [G.Additive] (Q : HomotopyCategory W' c ⥤ D)
    (K : HomotopyCategory V c) {Z : D}
    (h : Z ⟶ Q.obj ((F.mapHomotopyCategory c ⋙ G.mapHomotopyCategory c).obj K)) :
    h ≫ Q.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom.app K) = h := by
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Q.map_id]
  exact Category.comp_id _

private lemma mapHomotopyCategoryCompIso_refl_comp
    {V W W' D : Type*} [Category* V] [Category* W] [Category* W'] [Category* D]
    [Preadditive V] [Preadditive W] [Preadditive W']
    {J : Type*} (c : ComplexShape J) (F : V ⥤ W) (G : W ⥤ W')
    [F.Additive] [G.Additive] (Q : HomotopyCategory W' c ⥤ D)
    (K : HomotopyCategory V c) {Z : D}
    (h : Q.obj (((F ⋙ G).mapHomotopyCategory c).obj K) ⟶ Z) :
    Q.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom.app K) ≫ h = h := by
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Q.map_id]
  exact Category.id_comp _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)



/-- `ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory` is compatible with the
counit of `Lf^*`. -/
@[reassoc]
lemma leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_counit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv.app (DerivedCategory.Qh.obj K) ≫
        ((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K =
      ((f)^*⟦Λ⟧).mapDerivedCategoryFactorsh.hom.app K :=
  Functor.leftDerivedFunctorIsoMapDerivedCategory_inv_app_comp_counit _ K

/-- The underived (Pull) `pullIso` and `mapModUpperStarExtendScalarsIso` on the homotopy
categories. -/
lemma mapHomotopyCategoryCompIso_extendScalarsComp_comp_mapModUpperStarExtendScalarsIso
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso
        (Mod.extendScalarsComp (condensedPullbackHom Λ f) (coefficientMap a X)).symm
          (ComplexShape.up ℤ)).hom.app
        ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (NatTrans.mapHomotopyCategory (mapModUpperStarExtendScalarsIso a f).hom
        (ComplexShape.up ℤ)).app K =
    (NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.mapHomotopyCategory_app]
  have hcI : (Functor.mapHomotopyCategoryCompIso
        (Mod.extendScalarsComp (condensedPullbackHom Λ f) (coefficientMap a X)).symm
          (ComplexShape.up ℤ)).hom.app
        ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) =
      (HomotopyCategory.quotient _ _).map ((Functor.mapHomologicalComplexCompIso
        (Mod.extendScalarsComp (condensedPullbackHom Λ f) (coefficientMap a X)).symm
          (ComplexShape.up ℤ)).hom.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomologicalComplex _ |>.obj P)) := rfl
  rw [hcI, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [mapModUpperStarExtendScalarsIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
    HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f, Mod.comp_hom',
    Functor.mapHomologicalComplexCompIso_hom_app_f]
  rw [← Category.assoc, ← Mod.comp_hom']
  erw [Iso.inv_hom_id_app]
  erw [Mod.id_hom', Category.id_comp, Category.id_comp]

/-- **(Pull) is the underived (Pull) modulo the counits**: on the image `Qh K` of an object of the
homotopy category, `derivedUpperStarExtendScalarsIso a f` followed by the counits of `L(Ext_{a_Y})`
and `Lf^*_Λ'` is the counit of `Lf^*_Λ`, followed by the counit of `L(Ext_{a_X})` and the
underived (Pull) `pullIso a f`. -/
lemma derivedUpperStarExtendScalarsIso_hom_app_comp_counit
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    (derivedUpperStarExtendScalarsIso a f).hom.app (DerivedCategory.Qh.obj K) ≫
        L((f)^*⟦Λ'⟧).map ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K) ≫
        ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
          (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
            (ComplexShape.up ℤ)).hom.app K) =
      (L(Mod.extendScalars (coefficientMap a X)).map (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K) ≫
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
          ((((f)^*⟦Λ⟧).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
            (ComplexShape.up ℤ)).hom.app K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K) :
        (L((f)^*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X))).obj
          (DerivedCategory.Qh.obj K) ⟶ _) := by
  -- Reuse the tensor instances when specializing the generic counit lemmas.
  have (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) := inferInstance
  have (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) := inferInstance
  have (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (P Q S U : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)) :
      GradedObject.HasTensor₄ObjExt P Q S U := inferInstance
  have (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (P Q S : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)) :
      GradedObject.HasGoodTensor₁₂Tensor P Q S := inferInstance
  have (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (P Q S : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)) :
      GradedObject.HasGoodTensorTensor₂₃ P Q S := inferInstance
  simp only [derivedUpperStarExtendScalarsIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_hom_app, Category.id_comp,
    Category.assoc]
  have t1 := (leftDerivedUpperStarIsoMapDerivedCategory Λ' f).inv.naturality
    ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K)
  have t2 := leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_counit f Λ'
    (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at t1 t2 ⊢
  simp only [← reassoc_of% t1]
  simp only [reassoc_of% t2]
  have t3 := Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso_hom_app_comp_counit
    (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ K
  have t4 := Functor.leftDerivedFunctorIsoOfIso_hom_app_comp_counit
    (mapModUpperStarExtendScalarsIso a f) K
  have t5 := Functor.leftDerivedFunctorCompMapDerivedCategoryIso_inv_app_comp_counit
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
    (Mod.extendScalars (condensedPullbackHom Λ f ≫ coefficientMap a X)) K
  dsimp only [Functor.comp_obj, Functor.comp_map] at t3 t4 t5
  simp only [t3, t4, reassoc_of% t5]
  have t6 := (Mod.derivedExtendScalarsCompIso (condensedPullbackHom Λ f) (coefficientMap a X)
    (condensedPullbackHom Λ f ≫ coefficientMap a X) rfl).inv.naturality
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapDerivedCategoryFactorsh.hom.app K)
  have t7 := Mod.derivedExtendScalarsCompIso_inv_app_comp_counit (condensedPullbackHom Λ f)
    (coefficientMap a X)
    ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj K)
  have t8 := Functor.leftDerivedFunctorCompMapDerivedCategoryIso_hom_app_comp_counit
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
    (Mod.extendScalars (condensedPullbackHom Λ f)) K
  dsimp only [Functor.comp_obj, Functor.comp_map] at t6 t7 t8
  simp only [← reassoc_of% t6, reassoc_of% t7]
  simp only [comp_mapHomotopyCategoryCompIso_refl] at t8
  have t9 := congrArg (L(Mod.extendScalars (coefficientMap a X))).map t8
  simp only [Functor.map_comp] at t9
  simp only [mapHomotopyCategoryCompIso_refl_comp]
  simp only [leftDerivedUpperStarIso, reassoc_of% t9]
  have t10 :=
    mapHomotopyCategoryCompIso_extendScalarsComp_comp_mapModUpperStarExtendScalarsIso a f K
  simp only [← DerivedCategory.Qh.map_comp, t10]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
