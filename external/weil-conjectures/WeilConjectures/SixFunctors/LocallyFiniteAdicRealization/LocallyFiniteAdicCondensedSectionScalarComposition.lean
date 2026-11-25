/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # Composition of section scalar extension to the closure

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-finite-condensed-section-scalar-composition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
section
attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] HomRel CategoryTheory.Quotient.Hom
  CategoryTheory.Quotient.category
private theorem transportedUniq_inv_unit
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {R S : B ⥤ A} (a : F ⊣ R) (b : G ⊣ S) (r : R ≅ S)
    (M : A) :
    a.homEquiv _ _ ((b.leftAdjointUniq (a.ofNatIsoRight r)).inv.app M) ≫
      r.hom.app (G.obj M) = b.unit.app M := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (a.ofNatIsoRight r) b M
  rw [← Adjunction.leftAdjointUniq_inv_app] at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  rw [Adjunction.homEquiv_unit, Category.assoc]
  erw [r.hom.naturality]
  exact h

private theorem transportedUniq_hom_unit
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {R S : B ⥤ A} (a : F ⊣ R) (b : G ⊣ S) (r : R ≅ S)
    (M : A) :
    a.homEquiv _ _ ((a.leftAdjointUniq (b.ofNatIsoRight r.symm)).hom.app M) ≫
      r.hom.app (G.obj M) = b.unit.app M := by
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem leftAdjointCompIso_eq
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {Lh : A ⥤ B} {Rh : B ⥤ A} {Lk : B ⥤ C} {Rk : C ⥤ B}
    {Ld : A ⥤ C} {Rd : C ⥤ A}
    (a : Lh ⊣ Rh) (b : Lk ⊣ Rk) (d : Ld ⊣ Rd) (r : Rk ⋙ Rh ≅ Rd) :
    Adjunction.leftAdjointCompIso a b d r =
      ((a.comp b).ofNatIsoRight r).leftAdjointUniq d := by
  apply Iso.ext
  ext K
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointCompIso,
    conjugateEquiv_symm_apply_app]

private theorem normalized_associator
    {A B C AD BD CD : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* AD] [Category* BD] [Category* CD]
    (QA : A ⥤ AD) (QB : B ⥤ BD) (QC : C ⥤ CD)
    {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
    {H : A ⥤ C} {U : C ⥤ A}
    {FD : AD ⥤ BD} {RD : BD ⥤ AD} {GD : BD ⥤ CD} {SD : CD ⥤ BD}
    {HD : AD ⥤ CD} {UD : CD ⥤ AD}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ U)
    (ad : FD ⊣ RD) (bd : GD ⊣ SD) (cd : HD ⊣ UD)
    (εF : QA ⋙ FD ⟶ F ⋙ QB) (εG : QB ⋙ GD ⟶ G ⋙ QC)
    (εH : QA ⋙ HD ⟶ H ⋙ QC)
    (ρF : R ⋙ QA ⟶ QB ⋙ RD) (ρG : S ⋙ QB ⟶ QC ⋙ SD)
    (ρH : U ⋙ QA ⟶ QC ⋙ UD)
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF.app K)
    (hG : ∀ P K (f : G.obj P ⟶ K),
      bd.homEquiv _ _ (εG.app P ≫ QC.map f) = QB.map (b.homEquiv _ _ f) ≫ ρG.app K)
    (hH : ∀ P K (f : H.obj P ⟶ K),
      cd.homEquiv _ _ (εH.app P ≫ QC.map f) = QA.map (c.homEquiv _ _ f) ≫ ρH.app K)
    (r : S ⋙ R ≅ U) (rd : SD ⋙ RD ≅ UD) (ν : F ⋙ G ≅ H)
    (hn : ∀ P, (a.comp b).homEquiv _ _ (ν.hom.app P) ≫
      r.hom.app (H.obj P) = c.unit.app P)
    (hr : ∀ K, (ρF.app (S.obj K) ≫ RD.map (ρG.app K)) ≫
      rd.hom.app (QC.obj K) = QA.map (r.hom.app K) ≫ ρH.app K)
    (P : A) :
    (Adjunction.leftAdjointCompIso ad bd cd rd).hom.app (QA.obj P) ≫ εH.app P =
      GD.map (εF.app P) ≫ εG.app (F.obj P) ≫ QC.map (ν.hom.app P) := by
  have hc := normalizedAdjunction_composition a b ad bd εF εG ρF ρG hF hG
  have hu := normalizedAdjunction_uniqueness (QA := QA) (QB := QC) (a.comp b) c
    (ad.comp bd) cd
    (fun P ↦ GD.map (εF.app P) ≫ εG.app (F.obj P)) εH.app
    (fun K ↦ ρF.app (S.obj K) ≫ RD.map (ρG.app K)) ρH.app
    (by intro P K f; simpa only [Category.assoc] using hc P K f)
    hH r rd ν.hom.app hn hr P
  rw [← leftAdjointCompIso_eq] at hu
  simpa only [Category.assoc] using hu

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S T : C} [MonObj R] [MonObj S] [MonObj T]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]
  (χ : R ⟶ T) [IsMonHom χ]
private theorem modTranspose
    (P : HomotopyCategory (Mod C R) (.up ℤ))
    (K : HomotopyCategory (Mod C S) (.up ℤ))
    (f : ((extendScalars φ).mapHomotopyCategory (.up ℤ)).obj P ⟶ K) :
    (derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _
      ((extendScalars φ).leftDerivedFunctorCounit.app P ≫ DerivedCategory.Qh.map f) =
    DerivedCategory.Qh.map
      (((extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).homEquiv _ _ f) ≫
        (comap φ).mapDerivedCategoryFactorsh.inv.app K := by
  have hu := derivedExtendMapDerivedCategoryAdjunction_unit_app_fac φ P
  have hu' :
      (derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Qh.obj P) ≫
        (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctorCounit.app P) =
      DerivedCategory.Qh.map
        (((extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).unit.app P) ≫
          (comap φ).mapDerivedCategoryFactorsh.inv.app
            (((extendScalars φ).mapHomotopyCategory (.up ℤ)).obj P) := by
    apply (cancel_mono ((comap φ).mapDerivedCategoryFactorsh.hom.app _)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hu
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hu']
  simp only [Category.assoc]
  erw [← (comap φ).mapDerivedCategoryFactorsh.inv.naturality f]
  dsimp only [Functor.comp_map]
  rw [← Category.assoc, ← DerivedCategory.Qh.map_comp]
  rfl

attribute [local implicit_reducible] HomotopyCategory in
private theorem restrictionHomotopyFactors
    (w : φ ≫ ψ = χ) (K : HomotopyCategory (Mod C T) (.up ℤ)) :
    (comap φ).mapDerivedCategoryFactorsh.inv.app
        (((comap ψ).mapHomotopyCategory (.up ℤ)).obj K) ≫
      (comap φ).mapDerivedCategory.map ((comap ψ).mapDerivedCategoryFactorsh.inv.app K) ≫
      (mapDerivedCategoryComapCompIso φ ψ χ w).hom.app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso ((comapComp φ ψ).symm ≪≫ comapCongr w)
        (.up ℤ)).hom.app K) ≫ (comap χ).mapDerivedCategoryFactorsh.inv.app K := by
  let η := (comapComp φ ψ).symm ≪≫ comapCongr w
  have hc := Functor.mapDerivedCategoryCompIso_fach (comap ψ) (comap φ) K
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hc
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hc
  have hi :
      ((comap ψ).mapDerivedCategoryCompIso (comap φ)).hom.app
          (DerivedCategory.Qh.obj K) ≫
        (comap ψ ⋙ comap φ).mapDerivedCategoryFactorsh.hom.app K =
      (comap φ).mapDerivedCategory.map ((comap ψ).mapDerivedCategoryFactorsh.hom.app K) ≫
        (comap φ).mapDerivedCategoryFactorsh.hom.app
          (((comap ψ).mapHomotopyCategory (.up ℤ)).obj K) := by
    apply (cancel_epi (((comap ψ).mapDerivedCategoryCompIso (comap φ)).inv.app
      (DerivedCategory.Qh.obj K))).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact hc.symm
  haveI : IsIso ((comap χ).mapDerivedCategoryFactorsh.hom.app K) := inferInstance
  apply (cancel_mono ((comap χ).mapDerivedCategoryFactorsh.hom.app K)).mp
  simp only [mapDerivedCategoryComapCompIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fach]
  rw [← Category.assoc _ _ (DerivedCategory.Qh.map _), hi]
  dsimp only [Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift,
    HomotopyCategory.quotient, CategoryTheory.Quotient.functor,
    Functor.comp_obj, Functor.mapHomologicalComplex] at *
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  -- Use the inverse/unit cancellation equations at the derived-category level.
  erw [(comap ψ).mapDerivedCategoryFactorsh.inv_hom_id_app K,
    (comap χ).mapDerivedCategoryFactorsh.inv_hom_id_app K,
    Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc, Category.comp_id]
  congr 1
private theorem ordinaryComp_unit (w : φ ≫ ψ = χ) (M : Mod C R) :
    ((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).homEquiv _ _
        (((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq w).hom.app M) ≫
      ((comapComp φ ψ).symm ≪≫ comapCongr w).hom.app ((extendScalars χ).obj M) =
    (extendRestrictAdjunction χ).unit.app M := by
  let a := (extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)
  let b := extendRestrictAdjunction (φ ≫ ψ)
  let c := extendRestrictAdjunction χ
  let r := (comapComp φ ψ).symm
  let t := comapCongr w
  have h₁ := transportedUniq_inv_unit a b r M
  have h₂ := transportedUniq_hom_unit b c t M
  dsimp only [extendScalarsComp, extendScalarsIsoOfEq, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc]
  erw [r.hom.naturality_assoc]
  have h₁' := h₁
  rw [Adjunction.homEquiv_unit] at h₁'
  erw [reassoc_of% h₁']
  simpa only [Adjunction.homEquiv_unit, Category.assoc] using h₂
attribute [local implicit_reducible] HomotopyCategory in
private theorem homotopyComp_unit (w : φ ≫ ψ = χ)
    (P : HomotopyCategory (Mod C R) (.up ℤ)) :
    (((extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).comp
        ((extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ))).homEquiv _ _
        ((Functor.mapHomotopyCategoryCompIso
          ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq w) (.up ℤ)).hom.app P) ≫
      (Functor.mapHomotopyCategoryCompIso
        ((comapComp φ ψ).symm ≪≫ comapCongr w) (.up ℤ)).hom.app
          (((extendScalars χ).mapHomotopyCategory (.up ℤ)).obj P) =
    ((extendRestrictAdjunction χ).mapHomotopyCategory (.up ℤ)).unit.app P := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rw [Adjunction.comp_homEquiv]
  change ((extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).homEquiv _ _
    (((extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ)).homEquiv _ _ _) ≫ _ = _
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient]
  change ((HomotopyCategory.quotient (Mod C R) (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient (Mod C R) (.up ℤ)).map _) ≫
    (HomotopyCategory.quotient (Mod C R) (.up ℤ)).map _ =
    (HomotopyCategory.quotient (Mod C R) (.up ℤ)).map _
  dsimp only [Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift,
    HomotopyCategory.quotient, CategoryTheory.Quotient.functor,
    Functor.comp_obj, Functor.mapHomologicalComplex] at *
  change ((HomotopyCategory.quotient (Mod C R) (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient (Mod C R) (.up ℤ)).map _) ≫
    (HomotopyCategory.quotient (Mod C R) (.up ℤ)).map _ =
    (HomotopyCategory.quotient (Mod C R) (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  try dsimp only [Functor.mapHomologicalComplex]
  ext i
  have hh := ordinaryComp_unit φ ψ χ w (K.X i)
  rw [Adjunction.comp_homEquiv] at hh
  change (extendRestrictAdjunction φ).homEquiv _ _
    ((extendRestrictAdjunction ψ).homEquiv _ _ _) ≫ _ = _ at hh
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at hh
  simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Adjunction.mapHomologicalComplex_unit_app_f, Adjunction.comp_homEquiv,
    Adjunction.homEquiv_unit, Equiv.trans_apply, HomotopyCategory.quotient_obj_as,
    Functor.mapHomologicalComplex_obj_X, Functor.id_obj] using
      congrArg (fun f ↦ f.hom) hh

attribute [local implicit_reducible] HomotopyCategory in
private theorem exactModComp_eq
    [PreservesFiniteLimits (extendScalars φ)]
    [PreservesFiniteLimits (extendScalars ψ)]
    [PreservesFiniteLimits (extendScalars χ)]
    (w : φ ≫ ψ = χ)
    (hn : ∀ P : HomotopyCategory (Mod C R) (.up ℤ),
      (((extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).comp
          ((extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ))).homEquiv _ _
          ((Functor.mapHomotopyCategoryCompIso
            ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq w) (.up ℤ)).hom.app P) ≫
        (Functor.mapHomotopyCategoryCompIso
          ((comapComp φ ψ).symm ≪≫ comapCongr w) (.up ℤ)).hom.app
            (((extendScalars χ).mapHomotopyCategory (.up ℤ)).obj P) =
      ((extendRestrictAdjunction χ).mapHomotopyCategory (.up ℤ)).unit.app P) :
    letI : PreservesFiniteLimits (extendScalars (φ ≫ ψ)) :=
      preservesFiniteLimits_of_natIso (extendScalarsIsoOfEq w).symm
    ((extendScalars φ).leftDerivedFunctorCompIso (extendScalars ψ)).symm ≪≫
        (extendScalars φ ⋙ extendScalars ψ).leftDerivedFunctorNatIso
          ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq w) =
      Adjunction.leftAdjointCompIso (derivedExtendMapDerivedCategoryAdjunction φ)
        (derivedExtendMapDerivedCategoryAdjunction ψ)
        (derivedExtendMapDerivedCategoryAdjunction χ)
        (mapDerivedCategoryComapCompIso φ ψ χ w) := by
  letI : PreservesFiniteLimits (extendScalars (φ ≫ ψ)) :=
    preservesFiniteLimits_of_natIso (extendScalarsIsoOfEq w).symm
  letI : PreservesFiniteLimits (extendScalars φ ⋙ extendScalars ψ) := inferInstance
  let ν := (extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq w
  let r := (comapComp φ ψ).symm ≪≫ comapCongr w
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Mod C R) (.up ℤ))
  intro P
  have he := normalized_associator DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh
    ((extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ))
    ((extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ))
    ((extendRestrictAdjunction χ).mapHomotopyCategory (.up ℤ))
    (derivedExtendMapDerivedCategoryAdjunction φ)
    (derivedExtendMapDerivedCategoryAdjunction ψ)
    (derivedExtendMapDerivedCategoryAdjunction χ)
    (extendScalars φ).leftDerivedFunctorCounit
    (extendScalars ψ).leftDerivedFunctorCounit
    (extendScalars χ).leftDerivedFunctorCounit
    (comap φ).mapDerivedCategoryFactorsh.inv
    (comap ψ).mapDerivedCategoryFactorsh.inv
    (comap χ).mapDerivedCategoryFactorsh.inv
    (modTranspose φ) (modTranspose ψ) (modTranspose χ)
    (Functor.mapHomotopyCategoryCompIso r (.up ℤ))
    (mapDerivedCategoryComapCompIso φ ψ χ w)
    (Functor.mapHomotopyCategoryCompIso ν (.up ℤ)) hn
    (by intro K; simpa only [Category.assoc] using
      restrictionHomotopyFactors φ ψ χ w K) P
  apply (cancel_mono ((extendScalars χ).leftDerivedFunctorCounit.app P)).mp
  rw [he]
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.leftDerivedFunctorNatIso_hom_app_comp_counit]
  have hc := Functor.leftDerivedFunctorCompIso_hom_app_comp_counit
    (extendScalars φ) (extendScalars ψ) P
  rw [← hc]
  dsimp only [Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift,
    HomotopyCategory.quotient, CategoryTheory.Quotient.functor,
    Functor.comp_obj, Functor.mapHomologicalComplex] at *
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  congr 2
end CategoryTheory.Mod
end

section
attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] HomRel CategoryTheory.Quotient.Hom
  CategoryTheory.Quotient.category
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.AdicFiniteRealization
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem compNatIso_refl
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    mapDerivedCategoryCompNatIso (Iso.refl (F ⋙ G)) =
      mapDerivedCategoryCompIso F G := by
  apply Iso.ext
  simp only [mapDerivedCategoryCompNatIso, Iso.trans_hom,
    mapDerivedCategoryNatIso_refl, Category.comp_id]

private theorem square_factor
    {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory E]
    {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    mapDerivedCategorySquareIso e = mapDerivedCategoryCompNatIso e ≪≫
      (mapDerivedCategoryCompIso G₁ G₂).symm := by
  simp only [mapDerivedCategorySquareIso, mapDerivedCategoryCompNatIso, Iso.trans_assoc]

variable {A B C D E F : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]
  (R₁ : B ⥤ A) (R₂ : C ⥤ B) (R₃ : C ⥤ A)
  (R₁' : E ⥤ D) (R₂' : F ⥤ E) (R₃' : F ⥤ D)
  (U : A ⥤ D) (V : B ⥤ E) (W : C ⥤ F)
  [R₁.Additive] [R₂.Additive] [R₃.Additive]
  [R₁'.Additive] [R₂'.Additive] [R₃'.Additive]
  [U.Additive] [V.Additive] [W.Additive]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
  [PreservesFiniteLimits R₁'] [PreservesFiniteColimits R₁']
  [PreservesFiniteLimits R₂'] [PreservesFiniteColimits R₂']
  [PreservesFiniteLimits R₃'] [PreservesFiniteColimits R₃']
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits W] [PreservesFiniteColimits W]
private theorem exactSquare_composition
    (r : R₂ ⋙ R₁ ≅ R₃) (r' : R₂' ⋙ R₁' ≅ R₃')
    (k₁ : R₁ ⋙ U ≅ V ⋙ R₁') (k₂ : R₂ ⋙ V ≅ W ⋙ R₂')
    (k₃ : R₃ ⋙ U ≅ W ⋙ R₃')
    (hk : ∀ M, U.map (r.hom.app M) ≫ k₃.hom.app M =
      k₁.hom.app (R₂.obj M) ≫ R₁'.map (k₂.hom.app M) ≫ r'.hom.app (W.obj M))
    (M : DerivedCategory C) :
    U.mapDerivedCategory.map ((mapDerivedCategoryCompNatIso r).hom.app M) ≫
        (mapDerivedCategorySquareIso k₃).hom.app M =
      (mapDerivedCategorySquareIso k₁).hom.app (R₂.mapDerivedCategory.obj M) ≫
        R₁'.mapDerivedCategory.map ((mapDerivedCategorySquareIso k₂).hom.app M) ≫
        (mapDerivedCategoryCompNatIso r').hom.app (W.mapDerivedCategory.obj M) := by
  let δ : R₂ ⋙ (V ⋙ R₁') ≅ W ⋙ R₃' :=
    isoWhiskerRight k₂ R₁' ≪≫ isoWhiskerLeft W r'
  have h₁ := mapDerivedCategoryCompNatIso_cocycle r k₃ k₁ δ hk M
  have h₂ := mapDerivedCategoryCompNatIso_cocycle
    (F₁₂ := R₂) (F₂₃ := V) (F₃₄ := R₁')
    (F₁₃ := W ⋙ R₂') (F₂₄ := V ⋙ R₁') (F₁₄ := W ⋙ R₃')
    k₂ (isoWhiskerLeft W r') (Iso.refl (V ⋙ R₁')) δ
    (by intro N; simp [δ]) M
  have h₃ := mapDerivedCategoryCompNatIso_cocycle
    (F₁₂ := W) (F₂₃ := R₂') (F₃₄ := R₁')
    (F₁₃ := W ⋙ R₂') (F₂₄ := R₃') (F₁₄ := W ⋙ R₃')
    (Iso.refl (W ⋙ R₂'))
    (isoWhiskerLeft W r') r' (Iso.refl (W ⋙ R₃'))
    (by intro N; simp) M
  simp only [compNatIso_refl, Iso.symm_hom] at h₂ h₃
  have h₂' : (mapDerivedCategoryCompNatIso δ).hom.app M =
      (mapDerivedCategoryCompIso V R₁').inv.app (R₂.mapDerivedCategory.obj M) ≫
        R₁'.mapDerivedCategory.map ((mapDerivedCategoryCompNatIso k₂).hom.app M) ≫
        (mapDerivedCategoryCompNatIso (F := W ⋙ R₂') (G := R₁')
          (isoWhiskerLeft W r')).hom.app M := by
    rw [h₂, Iso.inv_hom_id_app_assoc]
  have h₃' :
      (mapDerivedCategoryCompNatIso (F := W ⋙ R₂') (G := R₁')
          (isoWhiskerLeft W r')).hom.app M ≫
        (mapDerivedCategoryCompIso W R₃').inv.app M =
      R₁'.mapDerivedCategory.map ((mapDerivedCategoryCompIso W R₂').inv.app M) ≫
        (mapDerivedCategoryCompNatIso r').hom.app (W.mapDerivedCategory.obj M) := by
    apply (cancel_epi (R₁'.mapDerivedCategory.map
      ((mapDerivedCategoryCompIso W R₂').hom.app M))).mp
    rw [← Category.assoc, h₃]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      ← R₁'.mapDerivedCategory.map_comp_assoc, R₁'.mapDerivedCategory.map_id,
      Category.id_comp]
    exact Category.comp_id _
  simp only [square_factor, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  rw [h₂']
  simp only [Category.assoc]
  rw [h₃', R₁'.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
end CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local implicit_reducible]
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
variable (X : Scheme.{u})
  {R S T : Sheaf (ProEt.topology X) Ab.{u + 1}}
  [MonObj R] [MonObj S] [MonObj T]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]
private theorem sectionRingMap_comp :
    sectionRingMap X φ ≫ sectionRingMap X ψ = sectionRingMap X (φ ≫ ψ) := by
  ext U x
  rfl

private theorem sectionRingMap_comp_eq
    (χ : R ⟶ T) [IsMonHom χ] (w : φ ≫ ψ = χ) :
    sectionRingMap X φ ≫ sectionRingMap X ψ = sectionRingMap X χ := by
  have hc : sectionRingMap X (φ ≫ ψ) = sectionRingMap X χ := by
    cases w
    rfl
  exact (sectionRingMap_comp X φ ψ).trans hc

private theorem sectionModuleComapIso_comp_congr
    (χ : R ⟶ T) [IsMonHom χ] (w : φ ≫ ψ = χ)
    (w₀ : sectionRingMap X φ ≫ sectionRingMap X ψ = sectionRingMap X χ)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) T) :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology X) R).functor.map
        (((Mod.comapComp φ ψ).symm ≪≫ Mod.comapCongr w).hom.app M) ≫
      (sectionModuleComapIso X χ).hom.app M =
    (sectionModuleComapIso X φ).hom.app ((Mod.comap ψ).obj M) ≫
      (pbcRestrict (sectionRingMap X φ)).map ((sectionModuleComapIso X ψ).hom.app M) ≫
      (pbcRestrictComp (sectionRingMap X φ) (sectionRingMap X ψ)
        (sectionRingMap X χ) w₀).hom.app
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (ProEt.topology X) T).functor.obj M) := by
  ext U x
  erw [(pbcRestrictComp_exists (sectionRingMap X φ) (sectionRingMap X ψ)
    (sectionRingMap X χ) w₀).exists.choose_spec]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local implicit_reducible]
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
variable (X : Scheme.{u})
  {R S T : Sheaf (ProEt.topology X) Ab.{u + 1}}
  [MonObj R] [MonObj S] [MonObj T]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]
  (χ : R ⟶ T) [IsMonHom χ]
private local instance sectionAdditive
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (ProEt.topology X) R).functor.Additive :=
  Functor.additive_of_preserves_binary_products _
private def sectionRestrictionIso
    {R S : Sheaf (ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    (Mod.comap φ).mapDerivedCategory ⋙ sectionDerived X R ≅
      sectionDerived X S ⋙ pbcDerivedRestrict (sectionRingMap X φ) := by
  unfold sectionDerived
  exact Functor.mapDerivedCategorySquareIso (sectionModuleComapIso X φ)
private theorem sectionRestrictionIso_comp (w : φ ≫ ψ = χ)
    (w₀ : sectionRingMap X φ ≫ sectionRingMap X ψ = sectionRingMap X χ)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) T)) :
    (sectionDerived X R).map
        ((Mod.mapDerivedCategoryComapCompIso φ ψ χ w).hom.app M) ≫
      (sectionRestrictionIso X χ).hom.app M =
    (sectionRestrictionIso X φ).hom.app ((Mod.comap ψ).mapDerivedCategory.obj M) ≫
      (pbcDerivedRestrict (sectionRingMap X φ)).map
        ((sectionRestrictionIso X ψ).hom.app M) ≫
      (pbcDerivedRestrictComp (sectionRingMap X φ) (sectionRingMap X ψ)
        (sectionRingMap X χ) w₀).hom.app ((sectionDerived X T).obj M) := by
  unfold sectionRestrictionIso sectionDerived Mod.mapDerivedCategoryComapCompIso
    pbcDerivedRestrictComp pbcDerivedRestrict
  exact Functor.exactSquare_composition _ _ _ _ _ _ _ _ _
    _ _ _ _ _ (sectionModuleComapIso_comp_congr X φ ψ χ w w₀) M
end AlgebraicGeometry.ProEtale.CondensedRing
end

attribute [local irreducible] HasDerivedCategory.standard
private theorem scalarComparison_inv_eq
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    {L : C ⥤ D} {R : D ⥤ C} {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
    (a : L ⊣ R) (a₀ : L₀ ⊣ R₀) (U : C ⥤ C₀) (V : D ⥤ D₀)
    (k : R ⋙ U ≅ V ⋙ R₀) (s : L ⋙ V ≅ U ⋙ L₀)
    (hs : ∀ M : C, U.map (a.unit.app M) ≫ k.hom.app (L.obj M) ≫
      R₀.map (s.hom.app M) = a₀.unit.app (U.obj M)) (M : C) :
    s.inv.app M = (a₀.homEquiv (U.obj M) (V.obj (L.obj M))).symm
      (U.map (a.unit.app M) ≫ k.hom.app (L.obj M)) := by
  apply (a₀.homEquiv _ _).injective
  dsimp only [Functor.comp_obj] at *
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, ← hs M]
  simp only [Category.assoc, ← R₀.map_comp, Iso.hom_inv_id_app,
    Functor.map_id, Category.comp_id]
  erw [R₀.map_id, Category.comp_id]

private theorem scalarComparison_isMate
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    {L : C ⥤ D} {R : D ⥤ C} {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
    (a : L ⊣ R) (a₀ : L₀ ⊣ R₀) (U : C ⥤ C₀) (V : D ⥤ D₀)
    (k : R ⋙ U ≅ V ⋙ R₀) (s : L ⋙ V ≅ U ⋙ L₀)
    (hs : ∀ M : C, U.map (a.unit.app M) ≫ k.hom.app (L.obj M) ≫
      R₀.map (s.hom.app M) = a₀.unit.app (U.obj M)) :
    TwoSquare.mk U L L₀ V s.inv =
      (mateEquiv a a₀).symm (TwoSquare.mk R V U R₀ k.hom) := by
  ext M
  rw [scalarComparison_inv_eq a a₀ U V k s hs M]
  apply (a₀.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact unit_mateEquiv_symm a a₀ (TwoSquare.mk R V U R₀ k.hom) M

private theorem inverseMate_composition
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : A ⥤ C} {R₃ : C ⥤ A}
    {L₁' : D ⥤ E} {R₁' : E ⥤ D} {L₂' : E ⥤ F} {R₂' : F ⥤ E}
    {L₃' : D ⥤ F} {R₃' : F ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (b₁ : L₁' ⊣ R₁') (b₂ : L₂' ⊣ R₂') (b₃ : L₃' ⊣ R₃')
    (U : A ⥤ D) (V : B ⥤ E) (W : C ⥤ F)
    (s₁ : L₁ ⋙ V ≅ U ⋙ L₁') (s₂ : L₂ ⋙ W ≅ V ⋙ L₂')
    (s₃ : L₃ ⋙ W ≅ U ⋙ L₃')
    (k₁ : R₁ ⋙ U ≅ V ⋙ R₁') (k₂ : R₂ ⋙ V ≅ W ⋙ R₂')
    (k₃ : R₃ ⋙ U ≅ W ⋙ R₃')
    (d : L₁ ⋙ L₂ ≅ L₃) (j : L₁' ⋙ L₂' ≅ L₃')
    (r : R₂ ⋙ R₁ ≅ R₃) (r' : R₂' ⋙ R₁' ≅ R₃')
    (hs₁ : mateEquiv a₁ b₁ (TwoSquare.mk U L₁ L₁' V s₁.inv) = k₁.hom)
    (hs₂ : mateEquiv a₂ b₂ (TwoSquare.mk V L₂ L₂' W s₂.inv) = k₂.hom)
    (hs₃ : mateEquiv a₃ b₃ (TwoSquare.mk U L₃ L₃' W s₃.inv) = k₃.hom)
    (hd : conjugateEquiv a₃ (a₁.comp a₂) d.hom = r.inv)
    (hj : conjugateEquiv b₃ (b₁.comp b₂) j.hom = r'.inv)
    (hk : (TwoSquare.hComp (TwoSquare.mk R₂ W V R₂' k₂.hom)
        (TwoSquare.mk R₁ V U R₁' k₁.hom)).whiskerTop r.inv =
      (TwoSquare.mk R₃ W U R₃' k₃.hom).whiskerBottom r'.inv) :
    (TwoSquare.vComp (TwoSquare.mk U L₁ L₁' V s₁.inv)
        (TwoSquare.mk V L₂ L₂' W s₂.inv)).whiskerLeft d.hom =
      (TwoSquare.mk U L₃ L₃' W s₃.inv).whiskerRight j.hom := by
  apply (mateEquiv a₃ (b₁.comp b₂)).injective
  rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp,
    mateEquiv_hcomp, hs₁, hs₂, hs₃, hd, hj]
  exact hk

private theorem coherentInverse_faces
    {D : Type*} [Category D] {X Y Z P Q : D}
    (a : X ≅ Y) (b : X ≅ Z) (c : Z ≅ P) (d : Y ≅ Q) (e : P ≅ Q)
    (h : c.inv ≫ b.inv ≫ a.hom = e.hom ≫ d.inv) :
    a.inv ≫ b.hom = d.hom ≫ e.inv ≫ c.inv := by
  apply (cancel_epi (c.inv ≫ b.inv ≫ a.hom)).mp
  calc
    (c.inv ≫ b.inv ≫ a.hom) ≫ (a.inv ≫ b.hom) = c.inv := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
        Category.comp_id]
    _ = (c.inv ≫ b.inv ≫ a.hom) ≫ (d.hom ≫ e.inv ≫ c.inv) := by
      rw [h]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

private theorem scalarComparison_composition
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : A ⥤ C} {R₃ : C ⥤ A}
    {L₁' : D ⥤ E} {R₁' : E ⥤ D} {L₂' : E ⥤ F} {R₂' : F ⥤ E}
    {L₃' : D ⥤ F} {R₃' : F ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (b₁ : L₁' ⊣ R₁') (b₂ : L₂' ⊣ R₂') (b₃ : L₃' ⊣ R₃')
    (U : A ⥤ D) (V : B ⥤ E) (W : C ⥤ F)
    (s₁ : L₁ ⋙ V ≅ U ⋙ L₁') (s₂ : L₂ ⋙ W ≅ V ⋙ L₂')
    (s₃ : L₃ ⋙ W ≅ U ⋙ L₃')
    (k₁ : R₁ ⋙ U ≅ V ⋙ R₁') (k₂ : R₂ ⋙ V ≅ W ⋙ R₂')
    (k₃ : R₃ ⋙ U ≅ W ⋙ R₃')
    (d : L₁ ⋙ L₂ ≅ L₃) (j : L₁' ⋙ L₂' ≅ L₃')
    (r : R₂ ⋙ R₁ ≅ R₃) (r' : R₂' ⋙ R₁' ≅ R₃')
    (hs₁ : mateEquiv a₁ b₁ (TwoSquare.mk U L₁ L₁' V s₁.inv) = k₁.hom)
    (hs₂ : mateEquiv a₂ b₂ (TwoSquare.mk V L₂ L₂' W s₂.inv) = k₂.hom)
    (hs₃ : mateEquiv a₃ b₃ (TwoSquare.mk U L₃ L₃' W s₃.inv) = k₃.hom)
    (hd : conjugateEquiv a₃ (a₁.comp a₂) d.hom = r.inv)
    (hj : conjugateEquiv b₃ (b₁.comp b₂) j.hom = r'.inv)
    (hk : ∀ M, U.map (r.hom.app M) ≫ k₃.hom.app M =
      k₁.hom.app (R₂.obj M) ≫ R₁'.map (k₂.hom.app M) ≫ r'.hom.app (W.obj M))
    (M : A) :
    W.map (d.inv.app M) ≫ s₂.hom.app (L₁.obj M) =
      s₃.hom.app M ≫ j.inv.app (U.obj M) ≫ L₂'.map (s₁.inv.app M) := by
  have hk' : (TwoSquare.hComp (TwoSquare.mk R₂ W V R₂' k₂.hom)
        (TwoSquare.mk R₁ V U R₁' k₁.hom)).whiskerTop r.inv =
      (TwoSquare.mk R₃ W U R₃' k₃.hom).whiskerBottom r'.inv := by
    ext N
    dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    apply (cancel_mono (r'.hom.app (W.obj N))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← hk N, ← U.map_comp_assoc, Iso.inv_hom_id_app, U.map_id, Category.id_comp]
    change k₃.hom.app N = k₃.hom.app N ≫ 𝟙 _
    exact (Category.comp_id _).symm
  have hm := inverseMate_composition a₁ a₂ a₃ b₁ b₂ b₃ U V W
    s₁ s₂ s₃ k₁ k₂ k₃ d j r r' hs₁ hs₂ hs₃ hd hj hk'
  have hc := congrArg (fun t ↦ t.natTrans.app M) hm
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app] at hc
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hc
  exact coherentInverse_faces (W.mapIso (d.app M)) (s₂.app (L₁.obj M))
    (L₂'.mapIso (s₁.app M)) (s₃.app M) (j.app (U.obj M)) hc

private theorem chosenScalarComparison_isMate
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    {L : C ⥤ D} {R : D ⥤ C} {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
    (a : L ⊣ R) (a₀ : L₀ ⊣ R₀) (U : C ⥤ C₀) (V : D ⥤ D₀)
    [U.IsEquivalence] [V.IsEquivalence] (k : R ⋙ U ≅ V ⋙ R₀) :
    mateEquiv a a₀ (TwoSquare.mk U L L₀ V
      (scalarAdjunctionCoefficientEquivalence a a₀ U V k).choose.inv) = k.hom := by
  rw [scalarComparison_isMate a a₀ U V k _
    (scalarAdjunctionCoefficientEquivalence a a₀ U V k).choose_spec]
  exact (mateEquiv a a₀).apply_symm_apply _

open CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
open AdicFiniteRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
set_option allowUnsafeReducibility true in
attribute [local reducible]
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  CategoryTheory.Sheaf.braidedCategory CategoryTheory.Sheaf.symmetricCategory
attribute [local instance 2000] ProEtale.sheafMonoidalCategory
  ProEtale.sheafMonoidalClosed ProEtale.hasFunctorialFlatResolution_sheaf
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
private local instance finiteComm (E : Index l (PadicAlgCl l)) :
    IsCommMonObj (ProEtale.padicSubfieldRingObj X l E) :=
  ProEtale.isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj E) X
private local instance closureComm : IsCommMonObj (ProEtale.padicAlgClRingObj X l) :=
  ProEtale.isCommMonObj_condensedRingObj (Profinite.padicAlgClRingObj l) X
private local instance sectionAdditive
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (ProEt.topology X) R).functor.Additive :=
  Functor.additive_of_preserves_binary_products _
private def finiteSectionAdjunction
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    ProEtale.derivedExtendScalarsSubfield X l h ⊣
      (Mod.comap (ProEtale.padicSubfieldRingObjMap X l h)).mapDerivedCategory := by
  letI hE := ProEtale.isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj E) X
  letI hL := ProEtale.isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj L) X
  exact @Mod.derivedExtendMapDerivedCategoryAdjunction
    (Sheaf (ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
    (ProEtale.padicSubfieldRingObj X l E) (ProEtale.padicSubfieldRingObj X l L)
    _ _ hE hL (ProEtale.padicSubfieldRingObjMap X l h) _
private def closureSectionAdjunction (E : Index l (PadicAlgCl l)) :
    ProEtale.derivedExtendScalarsToPadicAlgCl X l E ⊣
      (Mod.comap (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)).mapDerivedCategory := by
  letI hE := ProEtale.isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj E) X
  letI hC := ProEtale.isCommMonObj_condensedRingObj (Profinite.padicAlgClRingObj l) X
  exact @Mod.derivedExtendMapDerivedCategoryAdjunction
    (Sheaf (ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
    (ProEtale.padicSubfieldRingObj X l E) (ProEtale.padicAlgClRingObj X l)
    _ _ hE hC (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E) _
private def finiteSectionRestrictionIso
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    (Mod.comap (ProEtale.padicSubfieldRingObjMap X l h)).mapDerivedCategory ⋙
        sectionDerived X (ProEtale.padicSubfieldRingObj X l E) ≅
      sectionDerived X (ProEtale.padicSubfieldRingObj X l L) ⋙
        pbcDerivedRestrict (ProEtale.CondensedRing.sectionRingMap X
          (ProEtale.padicSubfieldRingObjMap X l h)) := by
  letI := Functor.additive_of_preserves_binary_products
    (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X)
      (ProEtale.padicSubfieldRingObj X l E)).functor
  letI := Functor.additive_of_preserves_binary_products
    (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X)
      (ProEtale.padicSubfieldRingObj X l L)).functor
  unfold sectionDerived
  exact Functor.mapDerivedCategorySquareIso
    (ProEtale.CondensedRing.sectionModuleComapIso X
      (ProEtale.padicSubfieldRingObjMap X l h))

private theorem finiteSection_isMate
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    mateEquiv
      (finiteSectionAdjunction l X h)
      (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X
        (ProEtale.padicSubfieldRingObjMap X l h)))
      (TwoSquare.mk (sectionDerived X (ProEtale.padicSubfieldRingObj X l E))
        (ProEtale.derivedExtendScalarsSubfield X l h)
        (pbcDerivedExtend (ProEtale.CondensedRing.sectionRingMap X
          (ProEtale.padicSubfieldRingObjMap X l h)))
        (sectionDerived X (ProEtale.padicSubfieldRingObj X l L))
        (finiteSectionScalarComparison l X h).inv) =
      (finiteSectionRestrictionIso l X h).hom := by
  unfold finiteSectionAdjunction
  unfold finiteSectionScalarComparison finiteSectionRestrictionIso sectionDerived
  exact chosenScalarComparison_isMate
    (finiteSectionAdjunction l X h)
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X
      (ProEtale.padicSubfieldRingObjMap X l h)))
    (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X)
      (ProEtale.padicSubfieldRingObj X l E)).functor.mapDerivedCategory
    (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X)
      (ProEtale.padicSubfieldRingObj X l L)).functor.mapDerivedCategory _
private def closureSectionRestrictionIso (E : Index l (PadicAlgCl l)) :
    (Mod.comap (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)).mapDerivedCategory ⋙
        sectionDerived X (ProEtale.padicSubfieldRingObj X l E) ≅
      integralSections l X ⋙ pbcDerivedRestrict
        (ProEtale.CondensedRing.sectionRingMap X
          (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)) := by
  unfold integralSections sectionDerived
  exact Functor.mapDerivedCategorySquareIso
    (ProEtale.CondensedRing.sectionModuleComapIso X
      (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E))
private theorem closureSection_isMate (E : Index l (PadicAlgCl l)) :
    mateEquiv
      (closureSectionAdjunction l X E)
      (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X
        (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)))
      (TwoSquare.mk (sectionDerived X (ProEtale.padicSubfieldRingObj X l E))
        (ProEtale.derivedExtendScalarsToPadicAlgCl X l E)
        (pbcDerivedExtend (ProEtale.CondensedRing.sectionRingMap X
          (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E))) (integralSections l X)
        (closureSectionScalarComparison l X E).inv) =
      (closureSectionRestrictionIso l X E).hom := by
  unfold closureSectionAdjunction
  unfold closureSectionScalarComparison closureSectionRestrictionIso integralSections sectionDerived
  exact chosenScalarComparison_isMate
    (closureSectionAdjunction l X E)
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X
      (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)))
    (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X)
      (ProEtale.padicSubfieldRingObj X l E)).functor.mapDerivedCategory
    (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X)
      (ProEtale.padicAlgClRingObj X l)).functor.mapDerivedCategory _

private theorem finiteClosureSectionScalarComparison_comp
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (ProEtale.padicSubfieldRingObj X l E))) :
    (integralSections l X).map
        ((ProEtale.derivedExtendScalarsCompIso X l h).inv.app M) ≫
      (closureSectionScalarComparison l X L).hom.app
        ((ProEtale.derivedExtendScalarsSubfield X l h).obj M) =
    (closureSectionScalarComparison l X E).hom.app M ≫
      (Adjunction.leftAdjointCompIso
        (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X
          (ProEtale.padicSubfieldRingObjMap X l h)))
        (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X
          (ProEtale.padicSubfieldRingObjToPadicAlgCl X l L)))
        (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X
          (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)))
        (pbcDerivedRestrictComp _ _ _ (by
          exact ProEtale.CondensedRing.sectionRingMap_comp_eq X _ _ _
            (ProEtale.padicSubfieldRingObjMap_comp_toPadicAlgCl X l h)))).inv.app
            ((sectionDerived X (ProEtale.padicSubfieldRingObj X l E)).obj M) ≫
      (pbcDerivedExtend (ProEtale.CondensedRing.sectionRingMap X
        (ProEtale.padicSubfieldRingObjToPadicAlgCl X l L))).map
        ((finiteSectionScalarComparison l X h).inv.app M) := by
  letI hE := ProEtale.isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj E) X
  letI hL := ProEtale.isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj L) X
  letI hC := ProEtale.isCommMonObj_condensedRingObj (Profinite.padicAlgClRingObj l) X
  let φ := ProEtale.padicSubfieldRingObjMap X l h
  let ψ := ProEtale.padicSubfieldRingObjToPadicAlgCl X l L
  let χ := ProEtale.padicSubfieldRingObjToPadicAlgCl X l E
  have w : φ ≫ ψ = χ := ProEtale.padicSubfieldRingObjMap_comp_toPadicAlgCl X l h
  have w₀ : ProEtale.CondensedRing.sectionRingMap X φ ≫
      ProEtale.CondensedRing.sectionRingMap X ψ =
        ProEtale.CondensedRing.sectionRingMap X χ := by
    exact ProEtale.CondensedRing.sectionRingMap_comp_eq X φ ψ χ w
  let r := Mod.mapDerivedCategoryComapCompIso φ ψ χ w
  let r' := pbcDerivedRestrictComp (ProEtale.CondensedRing.sectionRingMap X φ)
    (ProEtale.CondensedRing.sectionRingMap X ψ)
    (ProEtale.CondensedRing.sectionRingMap X χ) w₀
  let j := Adjunction.leftAdjointCompIso
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X φ))
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X ψ))
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X χ)) r'
  refine scalarComparison_composition
    (finiteSectionAdjunction l X h)
    (closureSectionAdjunction l X L) (closureSectionAdjunction l X E)
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X φ))
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X ψ))
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X χ))
    (sectionDerived X (ProEtale.padicSubfieldRingObj X l E))
    (sectionDerived X (ProEtale.padicSubfieldRingObj X l L)) (integralSections l X)
    (finiteSectionScalarComparison l X h)
    (closureSectionScalarComparison l X L) (closureSectionScalarComparison l X E)
    (finiteSectionRestrictionIso l X h) (closureSectionRestrictionIso l X L)
    (closureSectionRestrictionIso l X E) (ProEtale.derivedExtendScalarsCompIso X l h)
    j r r' (finiteSection_isMate l X h) (closureSection_isMate l X L)
    (closureSection_isMate l X E) ?_ ?_ ?_ M
  · letI hφ : PreservesFiniteLimits (Mod.extendScalars φ) :=
      ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap
        (X := X) (ℓ := l) h
    letI hψ : PreservesFiniteLimits (Mod.extendScalars ψ) :=
      ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
        (X := X) (ℓ := l) L
    letI hχ : PreservesFiniteLimits (Mod.extendScalars χ) :=
      ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
        (X := X) (ℓ := l) E
    have hd : ProEtale.derivedExtendScalarsCompIso X l h =
        Adjunction.leftAdjointCompIso (finiteSectionAdjunction l X h)
          (closureSectionAdjunction l X L) (closureSectionAdjunction l X E) r := by
      exact @Mod.exactModComp_eq (Sheaf (ProEt.topology X) Ab.{u + 1})
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE hL hC φ _ ψ _ χ _ hφ hψ hχ w
        (@Mod.homotopyComp_unit (Sheaf (ProEt.topology X) Ab.{u + 1})
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE hL hC φ _ ψ _ χ _ w)
    rw [hd]
    simp only [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
      Equiv.apply_symm_apply]
  · simp only [j, Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
      Equiv.apply_symm_apply]
  · intro N
    unfold finiteSectionRestrictionIso closureSectionRestrictionIso integralSections
    exact ProEtale.CondensedRing.sectionRestrictionIso_comp X φ ψ χ w w₀ N
end WeilConjectures.LocallyFiniteAdicRealization

private theorem restrictionComp_assoc
    (X : Scheme.{u}) {R₀ R₁ R₂ R₃ : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R₀ ⟶ R₁) (b : R₁ ⟶ R₂) (c : R₂ ⟶ R₃)
    (d : R₀ ⟶ R₂) (e : R₁ ⟶ R₃) (f : R₀ ⟶ R₃)
    (hab : a ≫ b = d) (hbc : b ≫ c = e)
    (hdc : d ≫ c = f) (hae : a ≫ e = f) (M : pbcModules X R₃) :
    (pbcRestrict a).map ((pbcRestrictComp b c e hbc).hom.app M) ≫
        (pbcRestrictComp a e f hae).hom.app M =
      (pbcRestrictComp a b d hab).hom.app ((pbcRestrict c).obj M) ≫
        (pbcRestrictComp d c f hdc).hom.app M := by
  ext U x
  change ((pbcRestrictComp a e f hae).hom.app M).val.app U
      (((pbcRestrictComp b c e hbc).hom.app M).val.app U x) =
    ((pbcRestrictComp d c f hdc).hom.app M).val.app U
      (((pbcRestrictComp a b d hab).hom.app ((pbcRestrict c).obj M)).val.app U x)
  erw [(pbcRestrictComp_exists a e f hae).exists.choose_spec,
    (pbcRestrictComp_exists b c e hbc).exists.choose_spec,
    (pbcRestrictComp_exists d c f hdc).exists.choose_spec,
    (pbcRestrictComp_exists a b d hab).exists.choose_spec]

private theorem derivedRestrictionComp_assoc
    (X : Scheme.{u}) {R₀ R₁ R₂ R₃ : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R₀ ⟶ R₁) (b : R₁ ⟶ R₂) (c : R₂ ⟶ R₃)
    (d : R₀ ⟶ R₂) (e : R₁ ⟶ R₃) (f : R₀ ⟶ R₃)
    (hab : a ≫ b = d) (hbc : b ≫ c = e)
    (hdc : d ≫ c = f) (hae : a ≫ e = f)
    (K : DerivedCategory (pbcModules X R₃)) :
    (pbcDerivedRestrict a).map ((pbcDerivedRestrictComp b c e hbc).hom.app K) ≫
        (pbcDerivedRestrictComp a e f hae).hom.app K =
      (pbcDerivedRestrictComp a b d hab).hom.app ((pbcDerivedRestrict c).obj K) ≫
        (pbcDerivedRestrictComp d c f hdc).hom.app K := by
  exact Functor.mapDerivedCategoryCompNatIso_cocycle
    (pbcRestrictComp b c e hbc) (pbcRestrictComp a e f hae)
    (pbcRestrictComp a b d hab) (pbcRestrictComp d c f hdc)
    (restrictionComp_assoc X a b c d e f hab hbc hdc hae) K

private theorem scalarExtensionComp_assoc
    (X : Scheme.{u}) {R₀ R₁ R₂ R₃ : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R₀ ⟶ R₁) (b : R₁ ⟶ R₂) (c : R₂ ⟶ R₃)
    (d : R₀ ⟶ R₂) (e : R₁ ⟶ R₃) (f : R₀ ⟶ R₃)
    (hab : a ≫ b = d) (hbc : b ≫ c = e)
    (hdc : d ≫ c = f) (hae : a ≫ e = f) :
    Functor.isoWhiskerLeft (pbcDerivedExtend a)
        (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction b)
          (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction e)
          (pbcDerivedRestrictComp b c e hbc)) ≪≫
      Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction e) (pbcDerivedScalarAdjunction f)
        (pbcDerivedRestrictComp a e f hae) =
      (Functor.associator (pbcDerivedExtend a) (pbcDerivedExtend b)
        (pbcDerivedExtend c)).symm ≪≫
      Functor.isoWhiskerRight
        (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
          (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction d)
          (pbcDerivedRestrictComp a b d hab)) (pbcDerivedExtend c) ≪≫
      Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction d)
        (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction f)
        (pbcDerivedRestrictComp d c f hdc) := by
  apply Adjunction.leftAdjointCompIso_assoc
  apply Iso.ext
  apply NatTrans.ext
  funext K
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app]
  simpa only [Category.id_comp] using
    (derivedRestrictionComp_assoc X a b c d e f hab hbc hdc hae K).symm

private theorem leftAdjointSquare_factor
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {La : A ⥤ B} {Ra : B ⥤ A} {Lb : B ⥤ D} {Rb : D ⥤ B}
    {Lc : A ⥤ C} {Rc : C ⥤ A} {Ld : C ⥤ D} {Rd : D ⥤ C}
    {Lf : A ⥤ D} {Rf : D ⥤ A}
    (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc) (d : Ld ⊣ Rd)
    (f : Lf ⊣ Rf) (r : Rb ⋙ Ra ≅ Rf) (s : Rd ⋙ Rc ≅ Rf) :
    Adjunction.leftAdjointCompIso a b (c.comp d) (r ≪≫ s.symm) =
      Adjunction.leftAdjointCompIso a b f r ≪≫
        (Adjunction.leftAdjointCompIso c d f s).symm := by
  apply Iso.ext
  apply (conjugateEquiv (c.comp d) (a.comp b)).injective
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← conjugateEquiv_comp _ f,
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  simp only [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
    Equiv.apply_symm_apply, Iso.trans_inv, Iso.symm_inv]

private theorem coefficientExtensionSquare_factor
    (X : Scheme.{u})
    {R₀ R₁ R₂ S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R₀ ⟶ R₁) (b : R₁ ⟶ S) (c : R₀ ⟶ R₂) (d : R₂ ⟶ S)
    (h : a ≫ b = c ≫ d) :
    WeilConjectures.AdicFiniteRealization.coefficientExtensionSquare X a b c d h =
      Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction (a ≫ b))
        (pbcDerivedRestrictComp a b (a ≫ b) rfl) ≪≫
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction c)
        (pbcDerivedScalarAdjunction d) (pbcDerivedScalarAdjunction (a ≫ b))
        (pbcDerivedRestrictComp c d (a ≫ b) h.symm)).symm := by
  unfold WeilConjectures.AdicFiniteRealization.coefficientExtensionSquare
    derivedRestrictionSquare
  exact leftAdjointSquare_factor _ _ _ _ _ _ _

private theorem coefficientRectangle
    (X : Scheme.{u})
    {RE RL FE FL RC : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : RE ⟶ RL) (i : RE ⟶ FE) (j : RL ⟶ FL) (s : FE ⟶ FL)
    (legE : FE ⟶ RC) (legL : FL ⟶ RC) (b : RL ⟶ RC) (c : RE ⟶ RC)
    (haj : a ≫ j = i ≫ s) (hb : j ≫ legL = b) (hc : i ≫ legE = c)
    (hab : a ≫ b = c) (hleg : s ≫ legL = legE)
    (M : DerivedCategory (pbcModules X RE)) :
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
        (pbcDerivedRestrictComp a b c hab)).inv.app M ≫
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction j)
        (pbcDerivedScalarAdjunction legL) (pbcDerivedScalarAdjunction b)
        (pbcDerivedRestrictComp j legL b hb)).inv.app ((pbcDerivedExtend a).obj M) =
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction i)
        (pbcDerivedScalarAdjunction legE) (pbcDerivedScalarAdjunction c)
        (pbcDerivedRestrictComp i legE c hc)).inv.app M ≫
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction s)
        (pbcDerivedScalarAdjunction legL) (pbcDerivedScalarAdjunction legE)
        (pbcDerivedRestrictComp s legL legE hleg)).inv.app ((pbcDerivedExtend i).obj M) ≫
      (pbcDerivedExtend legL).map
        ((WeilConjectures.AdicFiniteRealization.coefficientExtensionSquare
          X a j i s haj).inv.app M) := by
  have hdc : (a ≫ j) ≫ legL = c := by rw [Category.assoc, hb, hab]
  have h₁ := congrArg (fun e ↦ e.inv.app M)
    (scalarExtensionComp_assoc X a j legL (a ≫ j) b c rfl hb hdc hab)
  have h₂ := congrArg (fun e ↦ e.inv.app M)
    (scalarExtensionComp_assoc X i s legL (a ≫ j) legE c haj.symm hleg hdc hc)
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, Functor.associator_hom_app, Category.comp_id] at h₁ h₂
  rw [h₁, coefficientExtensionSquare_factor]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  rw [← Category.assoc, h₂]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp]
  erw [(pbcDerivedExtend legL).map_id, Category.id_comp]

private theorem coefficientSection_paste
    {C D E C₀ D₀ E₀ F₀ G₀ : Type*}
    [Category C] [Category D] [Category E]
    [Category C₀] [Category D₀] [Category E₀] [Category F₀] [Category G₀]
    (U : C ⥤ C₀) (V : D ⥤ D₀) (W : E ⥤ E₀)
    (L : C ⥤ D) (P : D ⥤ E) (Q : C ⥤ E)
    (A : C₀ ⥤ D₀) (B : D₀ ⥤ E₀) (H : C₀ ⥤ E₀)
    (i : C₀ ⥤ F₀) (k : D₀ ⥤ G₀) (κ : F₀ ⥤ G₀)
    (legF : F₀ ⥤ E₀) (legG : G₀ ⥤ E₀)
    (d : L ⋙ P ≅ Q) (s₁ : L ⋙ V ≅ U ⋙ A)
    (s₂ : P ⋙ W ≅ V ⋙ B) (s₃ : Q ⋙ W ≅ U ⋙ H)
    (j : A ⋙ B ≅ H) (mE : i ⋙ legF ≅ H) (mL : k ⋙ legG ≅ B)
    (n : A ⋙ k ≅ i ⋙ κ) (t : κ ⋙ legG ≅ legF)
    (hbase : ∀ M, W.map (d.inv.app M) ≫ s₂.hom.app (L.obj M) =
      s₃.hom.app M ≫ j.inv.app (U.obj M) ≫ B.map (s₁.inv.app M))
    (hrect : ∀ N, j.inv.app N ≫ mL.inv.app (A.obj N) =
      mE.inv.app N ≫ t.inv.app (i.obj N) ≫ legG.map (n.inv.app N)) (M : C) :
    W.map (d.inv.app M) ≫ s₂.hom.app (L.obj M) ≫
        mL.inv.app (V.obj (L.obj M)) =
      s₃.hom.app M ≫ mE.inv.app (U.obj M) ≫ t.inv.app (i.obj (U.obj M)) ≫
        legG.map (n.inv.app (U.obj M) ≫ k.map (s₁.inv.app M)) := by
  rw [← Category.assoc, hbase]
  simp only [Category.assoc, Functor.map_comp]
  erw [mL.inv.naturality]
  rw [reassoc_of% hrect]
  rfl

private theorem coefficientEncoding_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (κ : C ⥤ D) (legC : C ⥤ E) (legD : D ⥤ E)
    (t : κ ⋙ legD ≅ legC)
    {X Y : E} {F I : C} {G J : D}
    (f : X ⟶ Y) (p : X ≅ legC.obj I) (q : Y ≅ legD.obj J)
    (e : F ≅ I) (e' : G ≅ J) (r : J ≅ κ.obj I)
    (h : f ≫ q.hom = p.hom ≫ t.inv.app I ≫ legD.map r.inv) :
    f ≫ (q ≪≫ legD.mapIso e'.symm).hom =
      (p ≪≫ legC.mapIso e.symm).hom ≫ t.inv.app F ≫
        legD.map ((e' ≪≫ r ≪≫ κ.mapIso e.symm).inv) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Functor.map_comp]
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  erw [t.inv.naturality_assoc]
  simp only [Functor.comp_map, Category.assoc, ← legD.map_comp_assoc,
    ← κ.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  all_goals erw [κ.map_id I, Category.id_comp]
  all_goals simp only [Category.assoc]

open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization
set_option allowUnsafeReducibility true in
attribute [local reducible] closureRing ProEtale.constructibleExtendScalars
  ProEtale.constructibleToPadicAlgCl finiteCondensedClosureFunctor
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Section encoding of extension to the condensed algebraic closure, before any
raw-stage realization or constructibility lift is introduced.
Source: BS 6.8.2, the section scalar adjunction and the finite coefficient cocone.
(blueprint: lem-sf-finite-condensed-section-scalar-composition). -/
@[irreducible] def finiteCondensedClosureEncoding (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l)) :
    ProEtale.derivedExtendScalarsToPadicAlgCl X l E ⋙ integralSections l X ≅
      (finiteCondensedEncoding l X A E).functor ⋙
        pbcDerivedExtend (A.closure.leg E) := by
  let S := sectionDerived X (ProEtale.padicSubfieldRingObj X l E)
  let t := ProEtale.CondensedRing.sectionRingMap X
    (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)
  let m : pbcDerivedExtend t ≅
      pbcDerivedExtend (A.closure.finiteIso E).hom ⋙
        pbcDerivedExtend (A.closure.leg E) :=
    (Adjunction.leftAdjointCompIso
      (pbcDerivedScalarAdjunction (A.closure.finiteIso E).hom)
      (pbcDerivedScalarAdjunction (A.closure.leg E)) (pbcDerivedScalarAdjunction t)
      (pbcDerivedRestrictComp _ _ t (A.closure.leg_normalization E))).symm
  exact closureSectionScalarComparison l X E ≪≫
    Functor.isoWhiskerLeft S m ≪≫
    Functor.isoWhiskerRight (eqToIso (finiteCondensedEncoding_functor l X A E)).symm
      (pbcDerivedExtend (A.closure.leg E))

/-- The section scalar mate preserves composition to the closure.
Source: BS 6.8.2 and tensor transitivity in 6.8.14(2).
(blueprint: lem-sf-finite-condensed-section-scalar-composition).

Proof in words: express both finite and closure section comparisons as the unique
inverse mates of the identity-on-sections restriction comparisons. The restriction
comparisons compose: after applying the section equivalences, both are identity
linear maps on every section. This equality passes to derived categories by exact
localization. Horizontal pasting of mates gives the corresponding composition
identity for extension. The internal tensor compositor is the derived ordinary
tensor compositor; its unit characterization agrees with the adjunction mate.
Finally apply associativity of left-adjoint composition to the finite ring
isomorphisms, their scalar square and the closure cocone. All inverse mates are
invertible, so cancellation gives the displayed identity. Identity inclusions,
zero complexes and the empty scheme use the same unit equations.
-/
theorem finiteCondensedClosureEncoding_comp (A : FiniteCondensedData l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (ProEtale.padicSubfieldRingObj X l E))) :
    (integralSections l X).map
        ((ProEtale.derivedExtendScalarsCompIso X l h).inv.app M) ≫
      (finiteCondensedClosureEncoding l X A L).hom.app
        ((ProEtale.derivedExtendScalarsSubfield X l h).obj M) =
    (finiteCondensedClosureEncoding l X A E).hom.app M ≫
      (Adjunction.leftAdjointCompIso
        (pbcDerivedScalarAdjunction (A.scalar.coefficient h).coefficient)
        (pbcDerivedScalarAdjunction (A.closure.leg L))
        (pbcDerivedScalarAdjunction (A.closure.leg E))
        (pbcDerivedRestrictComp (A.scalar.coefficient h).coefficient
          (A.closure.leg L) (A.closure.leg E) (A.closure.cocone h))).inv.app
            ((finiteCondensedEncoding l X A E).functor.obj M) ≫
      (pbcDerivedExtend (A.closure.leg L)).map
        ((finiteCondensedScalarEncoding l X A h).inv.app M) := by
  let a := ProEtale.CondensedRing.sectionRingMap X
    (ProEtale.padicSubfieldRingObjMap X l h)
  let b := ProEtale.CondensedRing.sectionRingMap X
    (ProEtale.padicSubfieldRingObjToPadicAlgCl X l L)
  let c := ProEtale.CondensedRing.sectionRingMap X
    (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)
  have hab : a ≫ b = c := by
    dsimp only [a, b, c]
    exact ProEtale.CondensedRing.sectionRingMap_comp_eq X _ _ _
      (ProEtale.padicSubfieldRingObjMap_comp_toPadicAlgCl X l h)
  let i := (A.closure.finiteIso E).hom
  let k := (A.closure.finiteIso L).hom
  let s := (A.scalar.coefficient h).coefficient
  let U := sectionDerived X (ProEtale.padicSubfieldRingObj X l E)
  let V := sectionDerived X (ProEtale.padicSubfieldRingObj X l L)
  let W := integralSections l X
  let H := ProEtale.derivedExtendScalarsSubfield X l h
  let P := ProEtale.derivedExtendScalarsToPadicAlgCl X l L
  let Q := ProEtale.derivedExtendScalarsToPadicAlgCl X l E
  let d := ProEtale.derivedExtendScalarsCompIso X l h
  let s₁ := finiteSectionScalarComparison l X h
  let s₂ := closureSectionScalarComparison l X L
  let s₃ := closureSectionScalarComparison l X E
  let j := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
    (pbcDerivedRestrictComp a b c hab)
  let mE := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction i)
    (pbcDerivedScalarAdjunction (A.closure.leg E)) (pbcDerivedScalarAdjunction c)
    (pbcDerivedRestrictComp i (A.closure.leg E) c (A.closure.leg_normalization E))
  let mL := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction k)
    (pbcDerivedScalarAdjunction (A.closure.leg L)) (pbcDerivedScalarAdjunction b)
    (pbcDerivedRestrictComp k (A.closure.leg L) b (A.closure.leg_normalization L))
  let n := coefficientExtensionSquare X a k i s
    (A.closure.coefficient_normalization h).symm
  let t := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction s)
    (pbcDerivedScalarAdjunction (A.closure.leg L))
    (pbcDerivedScalarAdjunction (A.closure.leg E))
    (pbcDerivedRestrictComp s (A.closure.leg L) (A.closure.leg E) (A.closure.cocone h))
  have h₀ := coefficientSection_paste U V W H P Q
    (pbcDerivedExtend a) (pbcDerivedExtend b) (pbcDerivedExtend c)
    (pbcDerivedExtend i) (pbcDerivedExtend k) (pbcDerivedExtend s)
    (pbcDerivedExtend (A.closure.leg E)) (pbcDerivedExtend (A.closure.leg L))
    d s₁ s₂ s₃ j mE mL n t
    (finiteClosureSectionScalarComparison_comp l X h)
    (coefficientRectangle X a i k s (A.closure.leg E) (A.closure.leg L) b c
      (A.closure.coefficient_normalization h).symm (A.closure.leg_normalization L)
      (A.closure.leg_normalization E) hab (A.closure.cocone h)) M
  let p₀ := s₃.app M ≪≫ mE.symm.app (U.obj M)
  let q₀ := s₂.app (H.obj M) ≪≫ mL.symm.app (V.obj (H.obj M))
  let e := (eqToIso (finiteCondensedEncoding_functor l X A E)).app M
  let e' := (eqToIso (finiteCondensedEncoding_functor l X A L)).app (H.obj M)
  let r := (pbcDerivedExtend k).mapIso (s₁.app M) ≪≫ n.app (U.obj M)
  have hh := coefficientEncoding_transport (pbcDerivedExtend s)
    (pbcDerivedExtend (A.closure.leg E)) (pbcDerivedExtend (A.closure.leg L))
    t (W.map (d.inv.app M)) p₀ q₀ e e' r (by
      simpa only [p₀, q₀, r, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
        Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using h₀)
  unfold finiteCondensedClosureEncoding finiteCondensedScalarEncoding
  simpa only [p₀, q₀, e, e', r, t, i, k, s, U, V, W, H, P, Q, d, s₁, s₂, s₃,
    mE, mL, n, a, b, c, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_map, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc] using hh

end WeilConjectures.LocallyFiniteAdicRealization
