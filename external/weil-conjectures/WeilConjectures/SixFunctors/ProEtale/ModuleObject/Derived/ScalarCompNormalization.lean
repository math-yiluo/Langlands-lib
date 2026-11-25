/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsCompCounit
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp

/-! Scalar transitivity counit normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Mod.derivedExtendMapDerivedCategoryAdjunction

private lemma scalarCompNormalization_comparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    {ι : Type*} (c : ComplexShape ι) (K : HomotopyCategory C c) :
    (NatTrans.mapHomotopyCategory e.inv c).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).inv.app K =
      (Functor.mapHomotopyCategoryCompIso e c).inv.app K := by
  rw [Functor.mapHomotopyCategoryCompIso_refl_inv_app]
  erw [Category.comp_id]
  rfl

/-- The chosen derived scalar transitivity isomorphism respects the resolution counits.

Source: the scalar mate normalization in proof step 2 of
`lem-sp-original-integral-finite-quotient-mate-transport`, above the direct-image exchange
of the latest blueprint `def-exchange-projection`.

Proof in words. The underived comparison is uniqueness of left adjoints, so its unit
identity follows from `unit_leftAdjointUniq_hom_app`. Transport this identity to homotopy
categories. The exact restriction comparison is normalized on Qh by the localization
factorization equations. Apply the derived scalar adjunction to the desired equality,
use the unit identity for the conjugate transitivity map, and move the restriction
comparison through the counits by naturality. The formulas for the derived scalar units
then reduce the result to the underived unit identity. No flatness is required.
The calculation also applies to zero rings and zero complexes.
(blueprint: lem-sp-scalar-comp-normalization) -/
theorem scalarCompNormalization
    {U : Scheme.{u}} {R S T : Sheaf (ProEt.topology U) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    [MonObj T] [IsCommMonObj T]
    (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) R) (.up ℤ)) :
    (Mod.derivedExtendScalarsCompIso φ ψ (φ ≫ ψ) rfl).hom.app
        (DerivedCategory.Qh.obj K) ≫
      L(Mod.extendScalars ψ).map ((Mod.extendScalars φ).leftDerivedFunctorCounit.app K) ≫
      (Mod.extendScalars ψ).leftDerivedFunctorCounit.app
        (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj K) =
    (Mod.extendScalars (φ ≫ ψ)).leftDerivedFunctorCounit.app K ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (Mod.extendScalarsComp φ ψ).hom (.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (Mod.extendScalars φ ⋙ Mod.extendScalars ψ)) (.up ℤ)).inv.app K) := by
  erw [scalarCompNormalization_comparison (Mod.extendScalarsComp φ ψ).symm (.up ℤ) K]
  have h := congrArg (fun f ↦ f ≫ DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Mod.extendScalarsComp φ ψ).symm (.up ℤ)).inv.app K))
      (Mod.derivedExtendScalarsCompIso_hom_app_comp_counit φ ψ K)
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h


end AlgebraicGeometry.ProEtale.CondensedRing
