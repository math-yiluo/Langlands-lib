/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement

/-! # Scalar complex adjunction normalization

Source: Stacks Project, Tag 07A6.
(blueprint: lem-sf-scalar-complex-adjunction-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  pbcDerivedScalarAdjunction HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint pbcExtensionCounit pbcComplexCounit

private theorem scalar_complexUnit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules W R) ℤ) :
    (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P) := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have hr (X : HomotopyCategory (pbcModules W R) (.up ℤ)) :
      ∃ (K : HomotopyCategory (pbcModules W R) (.up ℤ)) (s : K ⟶ X),
        IsIso ((pbcExtensionCounit φ).app K) ∧
          HomotopyCategory.quasiIso (pbcModules W R) (.up ℤ) s := by
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, s, hK, hs⟩ :=
      ScalarReductionDerivedProof.kFlatResolutions.{u + 1, u, u + 1}
        (J := ProEt.topology W) (O := R) G
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, pbcExtensionCounit_isIso φ K hK,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  obtain ⟨d, hd⟩ := ScalarReductionDerivedProof.derivedAdjunction_of_resolutions
    (pbcExtend φ) (pbcRestrict φ) (pbcScalarAdjunction φ)
    (pbcDerivedExtend φ) (pbcExtensionCounit φ) (pbcDerivedExtension_universal φ) hr
  have hn (K : CochainComplex (pbcModules W R) ℤ) :
        d.unit.app (DerivedCategory.Q.obj K) ≫
          (pbcRestrict φ).mapDerivedCategory.map
            ((pbcDerivedExtend φ).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
              (pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj K) ≫
              DerivedCategory.Qh.map
                (((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
              (DerivedCategory.quotientCompQhIso _).hom.app
                (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj K)) ≫
          (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
            (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app K) := by
    have hp := hd ((HomotopyCategory.quotient _ _).obj K)
    change d.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj K)) ≫
      (pbcRestrict φ).mapDerivedCategory.map
        ((pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj K)) ≫
      (pbcRestrict φ).mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj K)) = _ at hp
    simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
      Adjunction.mapHomotopyCategory_unit_app_quotient] at hp
    dsimp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
      Functor.mapHomotopyCategoryFactors, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] at hp ⊢
    erw [(pbcDerivedExtend φ).map_id, DerivedCategory.Qh.map_id,
      Category.comp_id, Category.id_comp]
    erw [(pbcRestrict φ).mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
      Category.id_comp] at hp
    repeat' erw [Category.comp_id] at hp
    erw [Category.comp_id]
    exact hp
  have he : d = pbcDerivedScalarAdjunction φ :=
    (pbcDerivedScalarAdjunction_exists φ).unique
      (fun K _ ↦ by simpa only [pbcDerivedRestrict, pbcComplexCounit] using hn K)
      (by
        simpa only [pbcDerivedScalarAdjunction] using
          (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec)
  rw [← he]
  simpa only [pbcDerivedRestrict, pbcComplexCounit] using hn P

/-- Scalar derived transposition agrees with ordinary transposition on every complex.
Source: Stacks Tag 07A6 (blueprint: lem-sf-scalar-complex-adjunction-normalization).
Proof: the resolving-class construction supplies the scalar unit equation for all
complexes. Uniqueness identifies its adjunction with the canonical one. Cancel the
exact restriction comparison and use naturality to obtain the Hom equation. -/
theorem scalarComplexTranspose {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules T R) ℤ) (K : CochainComplex (pbcModules T S) ℤ)
    (f : ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    (pbcDerivedScalarAdjunction φ).homEquiv _ _
        (pbcComplexCounit φ P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
          (((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.inv.app K := by
  have hu : (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) =
    DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.inv.app
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) := by
    apply (Iso.eq_comp_inv ((pbcRestrict φ).mapDerivedCategoryFactors.app _)).2
    erw [Category.assoc]
    exact scalar_complexUnit φ P
  erw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← Category.assoc, hu,
    Category.assoc]
  erw [← (pbcRestrict φ).mapDerivedCategoryFactors.inv.naturality f]
  simp only [Functor.comp_map]
  erw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Adjunction.homEquiv_unit]
  rfl

end WeilConjectures.PurCompactSupport
