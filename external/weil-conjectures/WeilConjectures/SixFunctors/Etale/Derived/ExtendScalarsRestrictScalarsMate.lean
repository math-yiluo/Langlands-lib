/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsDerived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars

/-!
# Derived pullback, extension and restriction of scalars of étale sheaves

Let `φ : R →+* S` be a morphism of commutative rings and `g : Z ⟶ Y` a morphism of schemes. The
commutation `Lg^* Ψ ≅ Ψ Lg^*` of derived extension of scalars `Ψ = - ⊗ᴸ_R S` with the derived
pullback (`AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso`) and the
commutation `Lg^* Res ≅ Res Lg^*` of restriction of scalars with the derived pullback
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso`) are mates along the
adjunctions `Ψ ⊣ Res`
(`AlgebraicGeometry.Etale.mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_inv`).

This is the étale counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.RestrictScalarsMate`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)

section Sheaf

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The mate of `g^*(S ⊗_R -) ≅ S ⊗_R g^*` along extension and restriction of scalars of étale
sheaves is the comparison `g^* (Res M) ⟶ Res (g^* M)` of
`AlgebraicGeometry.Etale.upperStarRestrictScalars`. -/
lemma mateEquiv_sheafExtendScalarsCompUpperStarIso_inv :
    mateEquiv (sheafExtendScalarsAdjunction φ Y)
        (sheafExtendScalarsAdjunction φ Z)
        (sheafExtendScalarsCompUpperStarIso φ g).inv =
      upperStarRestrictScalars φ g := by
  rw [upperStarRestrictScalars, Equiv.eq_symm_apply]
  apply NatTrans.ext
  funext G
  rw [iterated_mateEquiv_conjugateEquiv]
  have h0 : conjugateEquiv ((sheafExtendScalarsAdjunction φ Y).comp
      (upperStarLowerStarAdjunction _ g))
      (((upperStarLowerStarAdjunction _ g).comp
        (sheafExtendScalarsAdjunction φ Z)).ofNatIsoRight
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))
      (sheafExtendScalarsCompUpperStarIso φ g).inv = 𝟙 _ := by
    simp only [sheafExtendScalarsCompUpperStarIso, Adjunction.leftAdjointUniq,
      Iso.symm_inv, conjugateIsoEquiv_symm_apply_hom, Iso.refl_hom]
    exact (conjugateEquiv _ _).apply_symm_apply _
  have h1 := NatTrans.congr_app h0 G
  simp only [conjugateEquiv_apply_app] at h1 ⊢
  simpa [Adjunction.ofNatIsoRight, lowerStarCompRestrictScalarsIso] using h1

end Sheaf

/-- On the image `Qh K` of an object of the homotopy category, the counit of `Ψ ⊣ Res` is
induced by the counit of the adjunction between extension and restriction of scalars on the
homotopy categories. -/
lemma leftDerivedEtaleSheafExtendScalarsAdjunction_counit_app_Qh_obj (X : Scheme.{u})
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) (.up ℤ)) :
    (leftDerivedEtaleSheafExtendScalarsAdjunction φ X).counit.app (DerivedCategory.Qh.obj K) =
      (L(sheafExtendScalars φ X)).map
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactorsh.hom.app K) ≫
        (sheafExtendScalars φ X).leftDerivedFunctorCounit.app
          (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategory
            (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          (((sheafExtendScalarsAdjunction φ X).mapHomotopyCategory
            (.up ℤ)).counit.app K) := by
  set r := Sheaf.restrictScalars X.smallEtaleTopology φ
  have h₁ := ((sheafExtendScalarsAdjunction φ X).mapHomotopyCategory
    (.up ℤ)).derivedε_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
    (sheafExtendScalars φ X).leftDerivedFunctorCounit
    r.rightDerivedFunctorUnit K
  have h₃ := NatTrans.congr_app
    r.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp at h₁ h₃
  have h₃' : r.rightDerivedFunctorIsoMapDerivedCategory.inv.app
      (DerivedCategory.Qh.obj K) =
      r.mapDerivedCategoryFactorsh.hom.app K ≫
        r.rightDerivedFunctorUnit.app K := by
    rw [← cancel_mono (r.rightDerivedFunctorIsoMapDerivedCategory.hom.app _),
      Iso.inv_hom_id_app, Category.assoc, h₃, Iso.hom_inv_id_app]
    rfl
  simp only [leftDerivedEtaleSheafExtendScalarsAdjunction, Adjunction.ofNatIsoRight_counit,
    NatTrans.comp_app, Functor.whiskerRight_app]
  rw [h₃', Functor.map_comp, Category.assoc, Adjunction.derivedAdjunction,
    Adjunction.derived_counit, h₁]
  rfl

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The inverse form of `leftDerivedUpperStarEtaleSheafExtendScalarsIso_hom_app_comp_counit`. -/
lemma leftDerivedUpperStarEtaleSheafExtendScalarsIso_inv_app_comp_counit
    (K : HomotopyCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso φ g).inv.app (DerivedCategory.Qh.obj K) ≫
        (leftDerivedEtaleSheafExtendScalarsUpperStarCounit φ g).app K =
      (leftDerivedUpperStarEtaleSheafExtendScalarsCounit φ g).app K ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso φ g).inv.app K) := by
  rw [← cancel_epi ((leftDerivedUpperStarEtaleSheafExtendScalarsIso φ g).hom.app
    (DerivedCategory.Qh.obj K)), Iso.hom_inv_id_app_assoc,
    leftDerivedUpperStarEtaleSheafExtendScalarsIso_hom_app_comp_counit_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  simp

/-- The commutation `Lg^* Ψ ≅ Ψ Lg^*` of derived extension of scalars with the derived pullback
is the mate, along the adjunctions `Ψ ⊣ Res`, of the commutation `Lg^* Res ≅ Res Lg^*` of
restriction of scalars with the derived pullback. -/
theorem mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_inv :
    mateEquiv (leftDerivedEtaleSheafExtendScalarsAdjunction φ Y)
        (leftDerivedEtaleSheafExtendScalarsAdjunction φ Z)
        (leftDerivedUpperStarEtaleSheafExtendScalarsIso φ g).inv =
      (leftDerivedUpperStarRestrictScalarsIso φ g).hom := by
  exact Adjunction.mateEquiv_leftDerived_inv_eq (sheafExtendScalarsAdjunction φ Y)
    (sheafExtendScalarsAdjunction φ Z)
    (sheafExtendScalarsCompUpperStarIso φ g)
    (upperStarRestrictScalarsIso φ g) (mateEquiv_sheafExtendScalarsCompUpperStarIso_inv φ g)
    (mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso φ g) rfl _ _ _ _
    (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh _ _
    (g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh
    (leftDerivedEtaleSheafExtendScalarsAdjunction φ Y)
    (leftDerivedEtaleSheafExtendScalarsAdjunction φ Z)
    (leftDerivedEtaleSheafExtendScalarsAdjunction_counit_app_Qh_obj φ Y)
    (leftDerivedEtaleSheafExtendScalarsAdjunction_counit_app_Qh_obj φ Z)
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso φ g) _ rfl _ rfl
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso_inv_app_comp_counit φ g) _ rfl

end AlgebraicGeometry.Etale
