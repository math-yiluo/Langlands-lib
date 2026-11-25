/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleShortExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShortcutInstances

/-!

# (Pull) is compatible with the connecting morphisms of the reduction triangles

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings such that
`0 ⟶ Λ_Z --k--> Λ_Z --a_Z--> Λ'_Z ⟶ 0` is short exact on `X` and `Y`, and `f : X ⟶ Y` a
morphism of schemes. The natural reduction triangles
`M --k--> M --η--> Res (Ext M) --δ--> M[1]` (`Mod.derivedExtendScalarsTriangle_distinguished`)
on `D(Y_proét, Λ)` and `D(X_proét, Λ)` are compatible with the pullback: `Lf^*` of `δ_M`,
followed by the commutation of `Lf^*` with the shift, is `δ_{Lf^* M}` precomposed with the
commutation `ι` of `Res` with `Lf^*` and `Res` of the inverse of (Pull)
(`ProEtale.CondensedRing.upperStar_map_derivedExtendScalarsTriangleδ_app`).

On the image of a complex `P` of flat modules, both connecting morphisms are connecting
morphisms of short exact sequences of complexes
(`Mod.derivedExtendScalarsTriangleδ_app_Qh_obj_of_shortExact`), `Lf^*` of the connecting
morphism of a short exact sequence is the connecting morphism of its pullback
(`Functor.leftDerivedFunctor_map_triangleOfSESδ`), the pullback of the reduction sequence of
`P` is isomorphic to the reduction sequence of `f^* P` through the underived compatibility of
(Pull) with the units (`ProEtale.CondensedRing.reductionShortComplexUpperStarIso`), and the
composite of `ι` and of `Res` of the inverse of (Pull) is computed by the underived comparisons
(`derivedComapLeftDerivedUpperStarIso_hom_app_comp_map_derivedUpperStarExtendScalarsIso_inv`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- The generic instance search behind every `L(-)` in the statements below is slow.
attribute [local instance] hasTensor₄ObjExt_mod hasGoodTensor₁₂Tensor_mod hasGoodTensorTensor₂₃_mod
  hasColimitsOfShape_int_mod preservesColimitsOfShape_int_curriedTensor_obj_mod
  preservesColimitsOfShape_int_curriedTensor_flip_obj_mod

-- Prove the cancellation in abstract categories, before specializing to derived functors.
private lemma inv_comp_of_comparison {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B A' B' : D} {W X Y Z : C} (e : A ≅ B)
    (p : W ≅ X) (q : X ⟶ Y) (q' : Y ⟶ X) (hq : q ≫ q' = 𝟙 X) (r : Z ≅ Y)
    (u : A ⟶ A') (v : A' ⟶ F.obj W) (s : B ⟶ B') (t : B' ⟶ F.obj Z)
    (h : e.hom ≫ s ≫ t ≫ F.map r.hom = u ≫ v ≫ F.map p.hom ≫ F.map q) :
    e.inv ≫ u ≫ v = (s ≫ t) ≫ F.map (r.hom ≫ q' ≫ p.inv) := by
  rw [Iso.inv_comp_eq]
  calc
    u ≫ v = (u ≫ v ≫ F.map p.hom ≫ F.map q) ≫
        F.map (q' ≫ p.inv) := by
          simp only [Category.assoc, ← F.map_comp, reassoc_of% hq,
            p.hom_inv_id, F.map_id, Category.comp_id]
    _ = (e.hom ≫ s ≫ t ≫ F.map r.hom) ≫ F.map (q' ≫ p.inv) := by rw [h]
    _ = e.hom ≫ (s ≫ t) ≫ F.map (r.hom ≫ q' ≫ p.inv) := by
      simp only [Functor.map_comp, Category.assoc]

section Comap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The inverse of (Pull) on the image of an object of the homotopy category, modulo the
counits. -/
lemma derivedUpperStarExtendScalarsIso_inv_app_comp_counit
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    (derivedUpperStarExtendScalarsIso a f).inv.app (DerivedCategory.Qh.obj K) ≫
        L(Mod.extendScalars (coefficientMap a X)).map (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K) ≫
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
          ((((f)^*⟦Λ⟧).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (L((f)^*⟦Λ'⟧).map ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K) ≫
        ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
          (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
            (ComplexShape.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory (pullIso a f).inv (ComplexShape.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso
            (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
              (ComplexShape.up ℤ)).inv.app K) :
        (L(Mod.extendScalars (coefficientMap a Y)) ⋙ L((f)^*⟦Λ'⟧)).obj
          (DerivedCategory.Qh.obj K) ⟶ _) := by
  have hp : (NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K ≫
      (NatTrans.mapHomotopyCategory (pullIso a f).inv (ComplexShape.up ℤ)).app K = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
      NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  simpa only [Category.assoc, Iso.app_hom, Iso.app_inv, Functor.comp_obj] using
    inv_comp_of_comparison DerivedCategory.Qh
      ((derivedUpperStarExtendScalarsIso a f).app (DerivedCategory.Qh.obj K))
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X))) (.up ℤ)).app K)
      _ _ hp
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧)) (.up ℤ)).app K)
      _ _ _ _ (derivedUpperStarExtendScalarsIso_hom_app_comp_counit a f K)

/-- The composite `Lf^* (Res (Ext M)) ⟶ Res (Lf^* (Ext M)) ⟶ Res (Ext (Lf^* M))` of `ι` and of `Res`
of the inverse of (Pull), on the image of an object of the homotopy category, modulo the
counits: it is the underived composite of `comapUpperStarIso` and of the inverse of `pullIso`. -/
lemma derivedComapLeftDerivedUpperStarIso_hom_app_comp_map_derivedUpperStarExtendScalarsIso_inv
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    (derivedComapLeftDerivedUpperStarIso a f).hom.app
        (L(Mod.extendScalars (coefficientMap a Y)).obj (DerivedCategory.Qh.obj K)) ≫
      D(Mod.comap (coefficientMap a X)).map
        ((derivedUpperStarExtendScalarsIso a f).inv.app (DerivedCategory.Qh.obj K)) ≫
      D(Mod.comap (coefficientMap a X)).map
        (L(Mod.extendScalars (coefficientMap a X)).map
          (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K)) ≫
      D(Mod.comap (coefficientMap a X)).map
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
          ((((f)^*⟦Λ⟧).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((((f)^*⟦Λ⟧).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) =
    (L((f)^*⟦Λ⟧).map (D(Mod.comap (coefficientMap a Y)).map
        ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K)) ≫
      L((f)^*⟦Λ⟧).map ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K)) ≫
      ((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app
        (((Mod.comap (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧))
          (ComplexShape.up ℤ)).hom.app
            (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (NatTrans.mapHomotopyCategory (comapUpperStarIso a f).inv (ComplexShape.up ℤ)).app
            (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (Functor.mapHomotopyCategoryCompIso
            (Iso.refl ((f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X)))
            (ComplexShape.up ℤ)).inv.app
            (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
      DerivedCategory.Qh.map (((Mod.comap (coefficientMap a X)).mapHomotopyCategory
        (ComplexShape.up ℤ)).map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
            (ComplexShape.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory (pullIso a f).inv (ComplexShape.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso
            (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
              (ComplexShape.up ℤ)).inv.app K)) :
      (D(Mod.comap (coefficientMap a Y)) ⋙ L((f)^*⟦Λ⟧)).obj
        (L(Mod.extendScalars (coefficientMap a Y)).obj (DerivedCategory.Qh.obj K)) ⟶ _) := by
  have hB := congrArg (D(Mod.comap (coefficientMap a X))).map
    (derivedUpperStarExtendScalarsIso_inv_app_comp_counit a f K)
  simp only [Functor.map_comp] at hB
  have l1 := (derivedComapLeftDerivedUpperStarIso a f).hom.naturality
    ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K)
  have l2 := (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
        (ComplexShape.up ℤ)).hom.app K ≫
      (NatTrans.mapHomotopyCategory (pullIso a f).inv (ComplexShape.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
          (ComplexShape.up ℤ)).inv.app K)
  have i1 := derivedComapLeftDerivedUpperStarIso_hom_app_Qh_comp a f
    (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have i1' := i1 =≫ DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
    (Iso.refl ((f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X))) (ComplexShape.up ℤ)).inv.app
      (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
  simp only [Category.assoc, ← DerivedCategory.Qh.map_comp, Iso.hom_inv_id_app] at i1'
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at i1'
  dsimp only [Functor.comp_obj, Functor.comp_map] at hB l1 l2 i1' ⊢
  simp only [Functor.map_comp, Category.assoc] at l2 ⊢
  simp only [reassoc_of% hB, ← reassoc_of% l1, l2, reassoc_of% i1']
  simp only [Functor.map_comp, Category.assoc]

/-- The levelwise comparison `f^* (Res (Ext P)) ⟶ Res (Ext (f^* P))` of complexes: the commutation
`comapUpperStarIso` followed by `Res` of the inverse of the underived (Pull) `pullIso`. -/
noncomputable def upperStarExtendComapComplexIso
    (P : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Mod.extendComapComplexFunctor (coefficientMap a Y)).obj P) ≅
      (Mod.extendComapComplexFunctor (coefficientMap a X)).obj
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (NatIso.mapHomologicalComplex (Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mod.extendScalars (coefficientMap a Y)) (comapUpperStarIso a f).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullIso a f).symm (Mod.comap (coefficientMap a X)) ≪≫
    Functor.associator _ _ _) (ComplexShape.up ℤ)).app P

variable (k : ℤ)
  (wY : (k • 𝟙 (condensedRingObj Λ Y)) ≫ coefficientMap a Y = 0)
  (wX : (k • 𝟙 (condensedRingObj Λ X)) ≫ coefficientMap a X = 0)

/-- The pullback of the reduction sequence `P --k--> P ⟶ Res (Ext P)` of a complex is the
reduction sequence of the pullback, through `upperStarExtendComapComplexIso`; this is the
compatibility of the underived (Pull) with the units. -/
noncomputable def reductionShortComplexUpperStarIso
    (P : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (Mod.reductionShortComplex k wY P).map ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)) ≅
      Mod.reductionShortComplex k wX (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (upperStarExtendComapComplexIso a f P)
    (by
      ext n : 2
      simp only [Iso.refl_hom, Linear.comp_smul, Category.comp_id, HomologicalComplex.smul_f_apply,
        HomologicalComplex.id_f, Mod.zsmul_hom, Mod.id_hom', ShortComplex.map_f, Functor.map_smul,
        CategoryTheory.Functor.map_id]
      rfl)
    (by
      ext n : 2
      have h := upperStar_map_unit_comp_comapUpperStarIso_inv_app a f (P.X n)
      rw [Mod.extendRestrictAdjunction_unit_app, Mod.extendRestrictAdjunction_unit_app] at h
      simp only [upperStarExtendComapComplexIso]
      simp only [Iso.refl_hom, Category.id_comp, Mod.extendUnitComplexHom_f, Mod.extendUnit_hom,
        ShortComplex.map_g, Iso.app_hom, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f, NatIso.mapHomologicalComplex_hom_app_f, Iso.trans_hom,
        Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
        Functor.comp_obj, Functor.associator_hom_app, Functor.whiskerLeft_app,
        Functor.associator_inv_app, Functor.whiskerRight_app, Category.comp_id, Mod.comp_hom',
        Mod.comap_map_hom]
      rw [← Category.assoc, ← Mod.comp_hom', h, Mod.comp_hom', Category.assoc, Mod.comap_map_hom,
        ← Mod.comp_hom', Iso.hom_inv_id_app, Mod.id_hom']
      erw [Category.comp_id]
      rfl)

set_option maxRecDepth 20000 in -- deep defeq checks between homotopy category objects
/-- The comparison of `derivedComapLeftDerivedUpperStarIso_hom_app_comp_map_...` on the image of a
complex `P` is the image of `upperStarExtendComapComplexIso`. -/
lemma upperStarExtendComapComplexIso_quotient_map
    (P : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧))
      (ComplexShape.up ℤ)).hom.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) ≫
      (NatTrans.mapHomotopyCategory (comapUpperStarIso a f).inv (ComplexShape.up ℤ)).app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl ((f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X)))
        (ComplexShape.up ℤ)).inv.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) ≫
      ((Mod.comap (coefficientMap a X)).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
            (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient _ _).obj P) ≫
          (NatTrans.mapHomotopyCategory (pullIso a f).inv (ComplexShape.up ℤ)).app
            ((HomotopyCategory.quotient _ _).obj P) ≫
          (Functor.mapHomotopyCategoryCompIso
            (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
              (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.quotient _ _).obj P)) =
    (HomotopyCategory.quotient _ _).map (upperStarExtendComapComplexIso a f P).hom := by
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  simp only [NatTrans.mapHomotopyCategory_app]
  erw [Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  congr 1

variable (hY : (ShortComplex.mk _ _ wY).ShortExact) (hX : (ShortComplex.mk _ _ wX).ShortExact)

/-- **(Pull) is compatible with the connecting morphisms of the reduction triangles**, on the
image of a complex of flat modules. -/
lemma upperStar_map_derivedExtendScalarsTriangleδ_app_Qh
    (P : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hP : ∀ n, ObjectProperty.flat (P.X n)) :
    L((f)^*⟦Λ⟧).map ((Mod.derivedExtendScalarsTriangleδ k wY hY).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ≫
      (L((f)^*⟦Λ⟧).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) =
    (derivedComapLeftDerivedUpperStarIso a f).hom.app
        (L(Mod.extendScalars (coefficientMap a Y)).obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ≫
      D(Mod.comap (coefficientMap a X)).map ((derivedUpperStarExtendScalarsIso a f).inv.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ≫
      (Mod.derivedExtendScalarsTriangleδ k wX hX).app
        (L((f)^*⟦Λ⟧).obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) := by
  have hS : (Mod.reductionShortComplex k wY P).ShortExact :=
    Mod.shortExact_extendUnitComplexHom k wY hY P hP
  have hS' : (Mod.reductionShortComplex k wX
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).ShortExact :=
    ShortComplex.shortExact_of_iso (reductionShortComplexUpperStarIso a f k wY wX P)
      (hS.map_of_exact _)
  have nδ := (Mod.derivedExtendScalarsTriangleδ k wX hX).naturality
    (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P))
  dsimp only [Functor.comp_obj, Functor.comp_map] at nδ
  apply (cancel_mono ((shiftFunctor _ (1 : ℤ)).map (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app
    ((HomotopyCategory.quotient _ _).obj P)))).1
  simp only [Category.assoc]
  simp only [← nδ,
    Mod.derivedExtendScalarsTriangleδ_app_Qh_obj_of_shortExact k wY hY P hS]
  have d2 := Mod.derivedExtendScalarsTriangleδ_app_Qh_obj_of_shortExact k wX hX _ hS'
  conv_rhs =>
    enter [2, 2, 2]
    erw [d2]
  have Φ :=
    derivedComapLeftDerivedUpperStarIso_hom_app_comp_map_derivedUpperStarExtendScalarsIso_inv
      a f ((HomotopyCategory.quotient _ _).obj P)
  simp only [Mod.derivedExtendComapComparisonh]
  conv_lhs =>
    arg 1
    rw [Functor.map_comp]
  simp only [Category.assoc]
  conv_rhs => erw [reassoc_of% Φ]
  have : NatTrans.CommShift ((f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory).inv ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ
  have hG := Functor.leftDerivedFunctor_map_triangleOfSESδ (f)^*⟦Λ⟧ hS
  have hG' : L((f)^*⟦Λ⟧).map ((DerivedCategory.quotientCompQhIso _).hom.app
        ((Mod.extendComapComplexFunctor (coefficientMap a Y)).obj P) ≫
        DerivedCategory.triangleOfSESδ hS ≫
        (shiftFunctor _ (1 : ℤ)).map ((DerivedCategory.quotientCompQhIso _).inv.app P)) ≫
      (L((f)^*⟦Λ⟧).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (shiftFunctor _ (1 : ℤ)).map
        (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)) = _ := hG
  conv_lhs =>
    arg 2
    rw [hG']
  have hV := congrArg DerivedCategory.Qh.map (upperStarExtendComapComplexIso_quotient_map a f P)
  simp only [Functor.map_comp] at hV
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality
    (upperStarExtendComapComplexIso a f P).hom
  have hσ := DerivedCategory.triangleOfSESδ_naturality (hS.map_of_exact _) hS'
    (reductionShortComplexUpperStarIso a f k wY wX P).hom
  simp only [reductionShortComplexUpperStarIso, ShortComplex.isoMk_hom_τ₁,
    ShortComplex.isoMk_hom_τ₃, Iso.refl_hom, CategoryTheory.Functor.map_id] at hσ
  simp only [Functor.map_comp, Category.assoc]
  simp only [reassoc_of% hV, reassoc_of% hq, ← reassoc_of% hσ]
  rfl

/-- **(Pull) is compatible with the connecting morphisms of the reduction triangles**: for
`M ∈ D(Y_proét, Λ)`, `Lf^*` of the connecting morphism `δ_M`, followed by the commutation of `Lf^*`
with the shift, is the commutation `ι` of `Res` with `Lf^*`, followed by `Res` of the inverse of
(Pull) and the connecting morphism at `Lf^* M`. -/
theorem upperStar_map_derivedExtendScalarsTriangleδ_app
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    L((f)^*⟦Λ⟧).map ((Mod.derivedExtendScalarsTriangleδ k wY hY).app M) ≫
      (L((f)^*⟦Λ⟧).commShiftIso (1 : ℤ)).hom.app M =
    (derivedComapLeftDerivedUpperStarIso a f).hom.app
        (L(Mod.extendScalars (coefficientMap a Y)).obj M) ≫
      D(Mod.comap (coefficientMap a X)).map ((derivedUpperStarExtendScalarsIso a f).inv.app M) ≫
      (Mod.derivedExtendScalarsTriangleδ k wX hX).app (L((f)^*⟦Λ⟧).obj M) := by
  let P := (CochainComplex.flatResolutionFunctor _).obj (DerivedCategory.Q.objPreimage M)
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) ≅ M :=
    (DerivedCategory.quotientCompQhIso _).app P ≪≫
      asIso (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app _)) ≪≫
      DerivedCategory.Q.objObjPreimageIso M
  have h := upperStar_map_derivedExtendScalarsTriangleδ_app_Qh a f k wY wX hY hX P
    (CochainComplex.flat_flatResolutionFunctor_obj_X _)
  have n1 := (Mod.derivedExtendScalarsTriangleδ k wY hY).naturality e.hom
  have n2 := (L((f)^*⟦Λ⟧).commShiftIso (1 : ℤ)).hom.naturality e.hom
  have n3 := (derivedComapLeftDerivedUpperStarIso a f).hom.naturality
    (L(Mod.extendScalars (coefficientMap a Y)).map e.hom)
  have n4 := (derivedUpperStarExtendScalarsIso a f).inv.naturality e.hom
  have n5 := (Mod.derivedExtendScalarsTriangleδ k wX hX).naturality (L((f)^*⟦Λ⟧).map e.hom)
  dsimp only [Functor.comp_obj, Functor.comp_map] at n1 n2 n3 n4 n5
  apply (cancel_epi (L((f)^*⟦Λ⟧).map (D(Mod.comap (coefficientMap a Y)).map
    (L(Mod.extendScalars (coefficientMap a Y)).map e.hom)))).1
  simp only [← Functor.map_comp_assoc, n1,
    Functor.map_comp, Category.assoc, n2, reassoc_of% n3, ← Functor.map_comp_assoc, n4,
    Functor.map_comp, Category.assoc, n5, reassoc_of% h]

end Comap

end AlgebraicGeometry.ProEtale.CondensedRing
