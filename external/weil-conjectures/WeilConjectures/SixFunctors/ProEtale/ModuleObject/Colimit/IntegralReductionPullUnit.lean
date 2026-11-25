/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionTriangleNatural

/-!

# (Pull) is compatible with the units of the extension-restriction adjunctions

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. Write `η` for the units of the derived adjunctions `L(Ext_{a_Z}) ⊣ D(Res_{a_Z})`,
`ι : D(Res_{a_Y}) ⋙ Lf^*_Λ ≅ Lf^*_Λ' ⋙ D(Res_{a_X})` for the commutation of the restriction of
scalars with the derived pullbacks (`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso`)
and (Pull) for `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso a f`. This file proves
that (Pull) is compatible with the units: `Lf^*(η_M) ≫ ι = η_{Lf^* M} ≫ Res((Pull)_M)` for every
`M` (`upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app`).

On the image `Qh P` of a K-flat complex `P`, (Pull) and `ι` are computed, modulo the counits of
the left derived functors, by their underived counterparts
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso_hom_app_comp_counit`,
`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso_hom_app_Qh_comp`), and the units
by the levelwise units (`Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_fac`); the
statement then reduces to the compatibility of the underived (Pull) with the units
(`ProEtale.CondensedRing.upperStar_map_unit_comp_comapUpperStarIso_inv_app`). Every object of
the derived category being isomorphic to the image of a K-flat complex, this proves it in general.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Comap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The commutation `derivedComapLeftDerivedUpperStarIso` is obtained from the levelwise
commutation `derivedComapUpperStarIso` and the identifications of the derived pullbacks with the
levelwise pullbacks. -/
lemma derivedComapLeftDerivedUpperStarIso_hom_eq :
    (derivedComapLeftDerivedUpperStarIso a f).hom =
      (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ f) ≪≫
        (derivedComapUpperStarIso a f).symm ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm _).hom := by
  ext K
  rw [derivedComapLeftDerivedUpperStarIso_hom_app]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    derivedComapUpperStarIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategorySquareIso]
  rfl

/-- Tensor existence and colimit preservation, reused as proof-local instances. -/
private lemma pullUnit_tensorInstances
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    let C₀ := Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R
    (∀ M : C₀, PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C₀).obj M)) ∧
    (∀ M : C₀, PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C₀).flip.obj M)) ∧
    (∀ A B C D : GradedObject ℤ C₀, GradedObject.HasTensor₄ObjExt A B C D) ∧
    (∀ A B C : GradedObject ℤ C₀, GradedObject.HasGoodTensor₁₂Tensor A B C) ∧
    (∀ A B C : GradedObject ℤ C₀, GradedObject.HasGoodTensorTensor₂₃ A B C) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Compose the counit squares in an abstract category before specializing to sheaves. -/
private lemma pullUnit_comp_counit_diagram
    {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ A₁₁ A₁₂ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    {e : A₄ ⟶ A₅} {f : A₅ ⟶ A₆} {g : A₆ ⟶ A₇} {h : A₇ ⟶ A₈}
    {i : A₀ ⟶ A₉} {j : A₉ ⟶ A₁₀} {k : A₁₀ ⟶ A₁₁} {l : A₁₁ ⟶ A₈}
    {q : A₄ ⟶ A₆} {r : A₃ ⟶ A₈} {s : A₂ ⟶ A₁₁}
    {t : A₁ ⟶ A₁₂} {u : A₁₂ ⟶ A₁₀} {v : A₉ ⟶ A₁₂}
    (h₁ : e ≫ f = q) (h₂ : d ≫ q ≫ g ≫ h = r) (h₃ : c ≫ r = s ≫ l)
    (h₄ : b ≫ s = t ≫ u ≫ k) (h₅ : i ≫ v = a ≫ t) (h₆ : v ≫ u = j) :
    (a ≫ b ≫ c ≫ d ≫ e) ≫ f ≫ g ≫ h = i ≫ j ≫ k ≫ l := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, h₂, h₃, reassoc_of% h₄, ← reassoc_of% h₅, reassoc_of% h₆]

private lemma pullUnit_cancel_mapped_iso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) {G H : E ⥤ C} (e : G ≅ H) (Z : E)
    {A B C' : D} (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ F.obj (G.obj Z))
    {d : A ⟶ F.obj (H.obj Z)} (h : a ≫ b ≫ c ≫ F.map (e.hom.app Z) = d) :
    a ≫ b ≫ c = d ≫ F.map (e.inv.app Z) := by
  have h' : (a ≫ b ≫ c) ≫ (F.mapIso (e.app Z)).hom = d := by
    simpa only [Functor.mapIso_hom, Iso.app_hom, Category.assoc] using h
  exact ((Iso.comp_inv_eq (F.mapIso (e.app Z))).2 h'.symm).symm

/-- The commutation `ι` of the restriction of scalars with the derived pullbacks, on the image of
an object of the homotopy category, is the underived commutation `comapUpperStarIso` modulo
the counits. -/
lemma derivedComapLeftDerivedUpperStarIso_hom_app_Qh_comp
    (Z : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y))
      (ComplexShape.up ℤ)) :
    (derivedComapLeftDerivedUpperStarIso a f).hom.app (DerivedCategory.Qh.obj Z) ≫
        D(Mod.comap (coefficientMap a X)).map (((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app Z) ≫
        (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.app
          ((((f)^*⟦Λ'⟧).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl ((f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X))) (ComplexShape.up ℤ)).hom.app Z) =
      (L((f)^*⟦Λ⟧).map ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app Z) ≫
        ((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app
          (((Mod.comap (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧)) (ComplexShape.up ℤ)).hom.app Z) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (comapUpperStarIso a f).inv (ComplexShape.up ℤ)).app Z) :
        (D(Mod.comap (coefficientMap a Y)) ⋙ L((f)^*⟦Λ⟧)).obj (DerivedCategory.Qh.obj Z) ⟶ _) := by
  have s1 := congrArg (D(Mod.comap (coefficientMap a X))).map
    (leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_counit f Λ' Z)
  have s2 := Functor.mapDerivedCategoryCompIso_fach (f)^*⟦Λ'⟧ (Mod.comap (coefficientMap a X)) Z
  have s3 := Functor.mapDerivedCategoryNatIso_inv_app_Qh_comp_factorsh (comapUpperStarIso a f) Z
  have s4 := Functor.mapDerivedCategoryCompIso_inv_app_Qh_comp_factorsh
    (Mod.comap (coefficientMap a Y)) (f)^*⟦Λ⟧ Z
  have s5 := (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.naturality
    ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app Z)
  have s6 := (((leftDerivedUpperStarIsoMapDerivedCategory Λ f).app
    (DerivedCategory.Qh.obj
      (((Mod.comap (coefficientMap a Y)).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj Z))).inv_comp_eq.mp
    (leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_counit f Λ
      (((Mod.comap (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z))).symm
  simp only [Functor.map_comp] at s1
  dsimp only [Functor.comp_obj, Functor.comp_map] at s1 s2 s3 s4 s5 s6 ⊢
  simpa only [derivedComapLeftDerivedUpperStarIso_hom_eq, derivedComapUpperStarIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, Category.assoc] using
      (pullUnit_comp_counit_diagram s1 s2 s3 s4 s5 s6)

/-- The underived compatibility of (Pull) with the units of `Ext ⊣ Res`
(`ProEtale.CondensedRing.upperStar_map_unit_comp_comapUpperStarIso_inv_app`), on the homotopy
categories. -/
lemma upperStar_mapHomotopyCategory_unit_comp_comapUpperStarIso_inv
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((Mod.extendRestrictAdjunction (coefficientMap a Y)).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app K) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧))
          (ComplexShape.up ℤ)).hom.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (NatTrans.mapHomotopyCategory (comapUpperStarIso a f).inv (ComplexShape.up ℤ)).app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl ((f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X)))
          (ComplexShape.up ℤ)).inv.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      ((Mod.comap (coefficientMap a X)).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
            (ComplexShape.up ℤ)).hom.app K) =
    ((Mod.extendRestrictAdjunction (coefficientMap a X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      ((Mod.comap (coefficientMap a X)).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
            (ComplexShape.up ℤ)).hom.app K) ≫
      ((Mod.comap (coefficientMap a X)).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K) := by
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp]
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient]
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 2
  have h := congrArg (fun g ↦ g.hom) (upperStar_map_unit_comp_comapUpperStarIso_inv_app a f (P.X n))
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f,
    Mod.comp_hom']
  simp only [Mod.comp_hom'] at h
  exact h

/-- **(Pull) is compatible with the units of `Ext ⊣ Res`**, on the image of a K-flat complex. -/
lemma upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app_Qh
    (P : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    L((f)^*⟦Λ⟧).map ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ≫
      (derivedComapLeftDerivedUpperStarIso a f).hom.app
        (L(Mod.extendScalars (coefficientMap a Y)).obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) =
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app
        (L((f)^*⟦Λ⟧).obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ≫
      D(Mod.comap (coefficientMap a X)).map ((derivedUpperStarExtendScalarsIso a f).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) := by
  have ht := pullUnit_tensorInstances Y (condensedRingObj Λ Y)
  have := ht.1
  have := ht.2.1
  have := ht.2.2.1
  have := ht.2.2.2.1
  have := ht.2.2.2.2
  have ht := pullUnit_tensorInstances Y (condensedRingObj Λ' Y)
  have := ht.1
  have := ht.2.1
  have := ht.2.2.1
  have := ht.2.2.2.1
  have := ht.2.2.2.2
  let K := (HomotopyCategory.quotient
    (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (.up ℤ)).obj P
  have := (Mod.extendScalars (coefficientMap a Y)).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  have : IsIso ((f)^*⟦Λ'⟧.leftDerivedFunctorCounit) := inferInstance
  let c := L((f)^*⟦Λ'⟧).map
      ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K) ≫
    ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
      (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
        (ComplexShape.up ℤ)).hom.app K)
  have : IsIso c := by dsimp only [c]; infer_instance
  refine (Iso.cancel_iso_hom_right _ _
    ((D(Mod.comap (coefficientMap a X))).mapIso (asIso c))).1 ?_
  dsimp only [Functor.mapIso_hom, asIso_hom, c]
  refine (Iso.cancel_iso_hom_right _ _
    ((Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.app
      (((Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K))).1 ?_
  have r1 := derivedUpperStarExtendScalarsIso_hom_app_comp_counit a f K
  have r2 := (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.naturality
    (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K)
  have r3 := Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_fac (coefficientMap a X)
    ((((f)^*⟦Λ⟧).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have r4 := (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
        (ComplexShape.up ℤ)).hom.app K ≫
      (NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K)
  dsimp only [K, Iso.app_hom, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
    Functor.id_map] at r1 r2 r3 r4 ⊢
  simp only [Category.assoc]
  simp only [← Functor.map_comp_assoc, r1]
  simp only [Functor.map_comp, Category.assoc] at r4 ⊢
  simp only [← reassoc_of% r2, r4, reassoc_of% r3]
  have l1 := (derivedComapLeftDerivedUpperStarIso a f).hom.naturality
    ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K)
  have l2 := (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
        (ComplexShape.up ℤ)).hom.app K)
  have i1 := derivedComapLeftDerivedUpperStarIso_hom_app_Qh_comp a f
    (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have i1' := pullUnit_cancel_mapped_iso DerivedCategory.Qh
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X))) (ComplexShape.up ℤ))
    (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
    _ _ _ i1
  dsimp only [K, Functor.comp_obj, Functor.comp_map] at l1 l2 i1'
  simp only [← reassoc_of% l1, l2, reassoc_of% i1']
  have r5 := Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_fac (coefficientMap a Y) K
  have e1 := ((f)^*⟦Λ⟧).leftDerivedFunctorCounit.naturality
    (((Mod.extendRestrictAdjunction (coefficientMap a Y)).mapHomotopyCategory
      (ComplexShape.up ℤ)).unit.app K)
  dsimp only [K, Functor.comp_obj, Functor.comp_map, Functor.id_obj] at r5 e1
  simp only [← Functor.map_comp_assoc, r5, reassoc_of% e1]
  simp only [← DerivedCategory.Qh.map_comp, Category.assoc]
  simp only [upperStar_mapHomotopyCategory_unit_comp_comapUpperStarIso_inv]

/-- **(Pull) is compatible with the units of `Ext ⊣ Res`**: for `M ∈ D(Y_proét, Λ)`, the
pullback of the unit `M ⟶ Res (Ext M)`, followed by the commutation `ι` of `Res` with `Lf^*`, is
the unit at `Lf^* M` followed by `Res` of (Pull). -/
theorem upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    L((f)^*⟦Λ⟧).map ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).unit.app
        M) ≫
      (derivedComapLeftDerivedUpperStarIso a f).hom.app
        (L(Mod.extendScalars (coefficientMap a Y)).obj M) =
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app
        (L((f)^*⟦Λ⟧).obj M) ≫
      D(Mod.comap (coefficientMap a X)).map ((derivedUpperStarExtendScalarsIso a f).hom.app M) := by
  have ht := pullUnit_tensorInstances Y (condensedRingObj Λ Y)
  have := ht.1
  have := ht.2.1
  have := ht.2.2.1
  have := ht.2.2.2.1
  have := ht.2.2.2.2
  let P := (CochainComplex.flatResolutionFunctor _).obj (DerivedCategory.Q.objPreimage M)
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) ≅ M :=
    (DerivedCategory.quotientCompQhIso _).app P ≪≫
      asIso (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app _)) ≪≫
      DerivedCategory.Q.objObjPreimageIso M
  have h := upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app_Qh a f P
    (CochainComplex.kFlat_flatResolutionFunctor_obj _)
  let lhs :=
    Functor.whiskerRight
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).unit L((f)^*⟦Λ⟧) ≫
    Functor.whiskerLeft L(Mod.extendScalars (coefficientMap a Y))
      (derivedComapLeftDerivedUpperStarIso a f).hom
  let rhs :=
    Functor.whiskerLeft L((f)^*⟦Λ⟧)
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit ≫
    Functor.whiskerRight (derivedUpperStarExtendScalarsIso a f).hom
      D(Mod.comap (coefficientMap a X))
  change lhs.app M = rhs.app M
  apply (Iso.cancel_iso_hom_left ((L((f)^*⟦Λ⟧)).mapIso e) _ _).1
  dsimp only [Functor.mapIso_hom]
  have hl := lhs.naturality e.hom
  have hr := rhs.naturality e.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hl hr
  rw [hl, hr]
  exact congrArg (fun k ↦ k ≫ _) h

end Comap

end AlgebraicGeometry.ProEtale.CondensedRing
