/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# Computing the derived comparison (Push) on complexes

Ingredients for computing the derived comparison
`ProEtale.CondensedRing.derivedPushHom : Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'` on the image of a
complex, in terms of the underived `ProEtale.CondensedRing.pushHom`:

* `ProEtale.CondensedRing.derivedComapLowerStarIso_hom_app_Qh`: `derivedComapLowerStarIso` on
  `Qh K` is `comapLowerStarIso` applied levelwise, through the right derived units;
* `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_fac`: the counit of
  `S ⊗ᴸ_R - ⊣ D(comap φ)` on `Qh M` is the levelwise counit;
* `ProEtale.CondensedRing.pushHom_app_eq`,
  `ProEtale.CondensedRing.mapHomotopyCategory_pushHom_app` and
  `ProEtale.CondensedRing.derivedPushHom_app_eq`: the pointwise mate formulas for `pushHom`
  (also on homotopy categories) and `derivedPushHom`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [IsCommMonObj Λ'] in
/-- `derivedComapLowerStarIso` on the image of a complex, through the units of the right derived
pushforwards. -/
lemma derivedComapLowerStarIso_hom_app_Qh
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
      (ComplexShape.up ℤ)) :
    (Mod.comap (coefficientMap a Y)).mapDerivedCategory.map
        (((f)_*⟦Λ'⟧).rightDerivedFunctorUnit.app K) ≫
      (derivedComapLowerStarIso a f).hom.app (DerivedCategory.Qh.obj K) =
    (Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app
        ((((f)_*⟦Λ'⟧).mapHomotopyCategory _).obj K) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom _).app K) ≫
      ((f)_*⟦Λ⟧).rightDerivedFunctorUnit.app
        (((Mod.comap (coefficientMap a X)).mapHomotopyCategory _).obj K) ≫
      ((f)_*⟦Λ⟧).rightDerivedFunctor.map
        ((Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.inv.app K) := by
  have h₁ := Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac (f)_*⟦Λ'⟧
    (Mod.comap (coefficientMap a Y)) K
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app'] at h₁
  have h₂ := Functor.rightDerivedNatTrans_app
    ((f)_*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a Y)).rightDerivedFunctor
    (Mod.comap (coefficientMap a X) ⋙ (f)_*⟦Λ⟧).rightDerivedFunctor
    ((f)_*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a Y)).rightDerivedFunctorUnit
    (Mod.comap (coefficientMap a X) ⋙ (f)_*⟦Λ⟧).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom
      (ComplexShape.up ℤ)) DerivedCategory.Qh) K
  have h₃ := Functor.rightDerivedFunctorCompIso_fac_app (Mod.comap (coefficientMap a X))
    (f)_*⟦Λ⟧ K
  rw [Functor.rightDerivedFunctorCompUnit_app] at h₃
  have h₄ := NatTrans.congr_app
    (Mod.comap (coefficientMap a X)).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₄
  simp only [derivedComapLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [← cancel_epi ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.inv.app
    ((((f)_*⟦Λ'⟧).mapHomotopyCategory _).obj K)), ← Category.assoc, ← Category.assoc,
    ← h₁]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% h₂]
  erw [reassoc_of% h₃]
  rw [← Functor.map_comp]
  erw [h₄]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{u + 1} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{u + 1} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The counit of the derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` on the image of a complex `M`,
read through the comparison for the exact restriction of scalars and the counit of the derived
extension of scalars, is the levelwise counit `S ⊗_R M ⟶ M`. -/
lemma derivedExtendMapDerivedCategoryAdjunction_counit_app_fac
    (M : HomotopyCategory (Mod C S) (ComplexShape.up ℤ)) :
    (extendScalars φ).leftDerivedFunctor.map
        ((comap φ).mapDerivedCategoryFactorsh.inv.app M) ≫
      (derivedExtendMapDerivedCategoryAdjunction φ).counit.app (DerivedCategory.Qh.obj M) =
    (extendScalars φ).leftDerivedFunctorCounit.app
        (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Qh.map
        (((extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)).counit.app M) := by
  have h₁ := (extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)
    |>.derivedε_fac_app
    (HomotopyCategory.quasiIso (Mod C S) (ComplexShape.up ℤ))
    (extendScalars φ).leftDerivedFunctorCounit (comap φ).rightDerivedFunctorUnit M
  have h₃ := NatTrans.congr_app (comap φ).rightDerivedFunctorIsoMapDerivedCategory_hom_fac M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  simp only [derivedExtendMapDerivedCategoryAdjunction, derivedExtendRestrictAdjunction,
    rightDerivedComapIsoMapDerivedCategory, Adjunction.derivedAdjunction,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app]
  rw [← h₃]
  rw [Functor.whiskerRight_app, Adjunction.derived_counit, Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc (extendScalars φ).leftDerivedFunctor
      ((comap φ).rightDerivedFunctorIsoMapDerivedCategory.hom.app _), Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp]
  exact h₁

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The underived (Push) as the mate of `comapLowerStarIso`, pointwise. -/
lemma pushHom_app_eq (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (pushHom a f).app M =
      (Mod.extendScalars (coefficientMap a Y)).map
        (((f)_*⟦Λ⟧).map ((Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app M) ≫
          (comapLowerStarIso a f).inv.app ((Mod.extendScalars (coefficientMap a X)).obj M)) ≫
        (Mod.extendRestrictAdjunction (coefficientMap a Y)).counit.app
          (((f)_*⟦Λ'⟧).obj ((Mod.extendScalars (coefficientMap a X)).obj M)) := by
  simp only [pushHom, Adjunction.pushHomOfComapIso, mateEquiv, Equiv.coe_fn_symm_mk,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_map, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Functor.comp_obj]
  rfl

/-- The underived (Push) on the homotopy category, as the mate of `comapLowerStarIso` along the
adjunctions induced on homotopy categories. -/
lemma mapHomotopyCategory_pushHom_app
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (ComplexShape.up ℤ)) :
    ((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory _).map
        ((((f)_*⟦Λ⟧).mapHomotopyCategory _).map
          (((Mod.extendRestrictAdjunction (coefficientMap a X)).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app K) ≫
          (NatTrans.mapHomotopyCategory (comapLowerStarIso a f).inv _).app
            (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory _).obj K)) ≫
      ((Mod.extendRestrictAdjunction (coefficientMap a Y)).mapHomotopyCategory
        (ComplexShape.up ℤ)).counit.app
          ((((f)_*⟦Λ'⟧).mapHomotopyCategory _).obj
            (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory _).obj K)) =
    (NatTrans.mapHomotopyCategory (pushHom a f) _).app K := by
  obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  erw [Adjunction.mapHomotopyCategory_counit_app_quotient]
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map]
  rw [← Functor.map_comp, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  refine congrArg _ ?_
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.map_comp, Category.assoc]
  erw [pushHom_app_eq a f (I.X n)]
  simp only [Functor.map_comp, Category.assoc]
  rfl
variable [IsCommMonObj Λ']
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

/-- The derived (Push) as the mate of `derivedComapLowerStarIso`, pointwise. -/
lemma derivedPushHom_app_eq
    (Z : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (derivedPushHom a f).app Z =
      (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.map
        (((f)_*⟦Λ⟧).rightDerivedFunctor.map
          ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app Z)) ≫
      (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.map
        ((derivedComapLowerStarIso a f).inv.app _) ≫
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).counit.app _ := by
  simp only [derivedPushHom, Adjunction.pushHomOfComapIso, mateEquiv, Equiv.coe_fn_symm_mk,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_map, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Functor.comp_obj, Functor.id_obj]

end AlgebraicGeometry.ProEtale.CondensedRing
