/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.ScalarExtension.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Extension of scalars of étale sheaves is monoidal

For a morphism of commutative rings `φ : R →+* S`, extension of scalars
`S ⊗_R - : Sh(X_ét, R) ⥤ Sh(X_ét, S)` (`AlgebraicGeometry.Etale.sheafExtendScalars`) is
strong monoidal, and for a morphism of schemes `g : Y ⟶ X` the isomorphism
`g^* (S ⊗_R F) ≅ S ⊗_R g^* F` of
`AlgebraicGeometry.Etale.sheafExtendScalarsCompUpperStarIso` is monoidal.

This is the étale counterpart of `WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal`.

## Main results

- `AlgebraicGeometry.Etale.monoidal_sheafExtendScalars`: extension of scalars is strong
  monoidal, its oplax structure being that of the left adjoint of the lax monoidal restriction
  of scalars.
- `AlgebraicGeometry.Etale.sheafExtendScalarsCompUpperStarIso_eq_conjugateIsoEquiv`: the
  commutation with `g^*` is the conjugate of the identification `g_* ⋙ res = res ⋙ g_*`.
- `AlgebraicGeometry.Etale.isMonoidal_sheafExtendScalarsCompUpperStarIso_hom`: the
  commutation with `g^*` is monoidal.

## Implementation notes

The monoidal structures on étale sheaves are the global instances
`AlgebraicGeometry.Etale.sheafMonoidalCategory` and `AlgebraicGeometry.Etale.sheafBraidedCategory`,
with the braiding of `ModuleCat` coming from its symmetric structure, exactly as for the derived
tensor product `AlgebraicGeometry.Etale.derivedTensor`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

-- The braiding of `ModuleCat` found by instance search (`instBraidedCategory`) is not syntactically
-- the one underlying the derived tensor product of étale sheaves, and the kernel cannot compare
-- the two monoidal structures in reasonable time; with these instances, instance search produces
-- exactly the monoidal structure used by `AlgebraicGeometry.Etale.derivedTensor`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u})

/-- Restriction of scalars of étale sheaves is lax monoidal. -/
noncomputable instance laxMonoidal_sheafComposeRestrictScalars :
    (sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ)).LaxMonoidal :=
  sheafComposeLaxMonoidal _ _

/-- Extension of scalars of étale sheaves is oplax monoidal, being left adjoint to the lax
monoidal restriction of scalars. -/
noncomputable instance oplaxMonoidal_sheafExtendScalars :
    (sheafExtendScalars φ X).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- The adjunction between extension and restriction of scalars of étale sheaves is
monoidal. -/
instance isMonoidal_sheafExtendScalarsAdjunction :
    (sheafExtendScalarsAdjunction φ X).IsMonoidal :=
  isMonoidal_sheafAdjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

instance isIso_δ_sheafExtendScalars
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsIso (Functor.OplaxMonoidal.δ (sheafExtendScalars φ X) F G) :=
  isIso_δ_composeAndSheafify _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ) F G

instance isIso_η_sheafExtendScalars :
    IsIso (Functor.OplaxMonoidal.η (sheafExtendScalars φ X)) :=
  isIso_η_composeAndSheafify _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- Extension of scalars of étale sheaves is strong monoidal. -/
noncomputable instance monoidal_sheafExtendScalars :
    (sheafExtendScalars φ X).Monoidal :=
  .ofOplaxMonoidal _

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- Restriction of scalars commutes with the direct image `g_*`: both composites restrict a
sheaf along base change and forget the `S`-module structure to an `R`-module structure. -/
noncomputable def lowerStarCompSheafComposeRestrictScalarsIso :
    (g)_*[ModuleCat.{u + 1} S] ⋙
        sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ) ≅
      sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ) ⋙
        (g)_*[ModuleCat.{u + 1} R] :=
  Iso.refl _

/-- The isomorphism `g^* (S ⊗_R F) ≅ S ⊗_R g^* F` of
`AlgebraicGeometry.Etale.sheafExtendScalarsCompUpperStarIso`, obtained by uniqueness of
left adjoints, is the conjugate of the identification `g_* ⋙ res = res ⋙ g_*` of
`AlgebraicGeometry.Etale.lowerStarCompSheafComposeRestrictScalarsIso`. -/
lemma sheafExtendScalarsCompUpperStarIso_eq_conjugateIsoEquiv :
    sheafExtendScalarsCompUpperStarIso φ g =
      (conjugateIsoEquiv
        ((upperStarLowerStarAdjunction _ g).comp (sheafExtendScalarsAdjunction φ Y))
        ((sheafExtendScalarsAdjunction φ X).comp (upperStarLowerStarAdjunction _ g))).symm
        (lowerStarCompSheafComposeRestrictScalarsIso φ g).symm := by
  ext F : 3
  apply ((sheafExtendScalarsAdjunction φ X).comp
    (upperStarLowerStarAdjunction _ g)).homEquiv _ _ |>.injective
  rw [sheafExtendScalarsCompUpperStarIso, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit, conjugateIsoEquiv_symm_apply_hom]
  rw [← unit_conjugateEquiv_symm]
  simp only [Functor.comp_obj, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.id_obj,
    Adjunction.comp_unit_app, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.comp_id, lowerStarCompSheafComposeRestrictScalarsIso, Iso.refl_symm,
    NatTrans.id_app, Category.assoc]
  exact (Category.comp_id _).symm

/-- The identification `g_* ⋙ res ≅ res ⋙ g_*` of
`AlgebraicGeometry.Etale.lowerStarCompSheafComposeRestrictScalarsIso` is monoidal. -/
instance isMonoidal_lowerStarCompSheafComposeRestrictScalarsIso_hom :
    NatTrans.IsMonoidal (lowerStarCompSheafComposeRestrictScalarsIso φ g).hom := by
  have := Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
    (MorphismProperty.Over.pullback @Etale ⊤ g) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale) (A := ModuleCat.{u + 1} S)
    (ModuleCat.restrictScalars.{u + 1} φ)
  exact this

/-- The isomorphism `g^* (S ⊗_R F) ≅ S ⊗_R g^* F` of
`AlgebraicGeometry.Etale.sheafExtendScalarsCompUpperStarIso` is monoidal, being the
conjugate of the monoidal identification `g_* ⋙ res ≅ res ⋙ g_*`. -/
instance isMonoidal_sheafExtendScalarsCompUpperStarIso_hom :
    NatTrans.IsMonoidal (sheafExtendScalarsCompUpperStarIso φ g).hom := by
  have : NatTrans.IsMonoidal (lowerStarCompSheafComposeRestrictScalarsIso φ g).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (lowerStarCompSheafComposeRestrictScalarsIso φ g).inv)
  rw [sheafExtendScalarsCompUpperStarIso_eq_conjugateIsoEquiv]
  exact isMonoidal_conjugateEquiv_symm _ _ _

end AlgebraicGeometry.Etale
