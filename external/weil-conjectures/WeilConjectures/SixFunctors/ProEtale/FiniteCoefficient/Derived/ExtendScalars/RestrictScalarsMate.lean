/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Projection
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit

/-!
# Derived pullback, extension and restriction of scalars

Let `S` be an algebra over a noetherian commutative ring `R` and `g : Z ⟶ Y` a morphism of
schemes. The commutation `Lg^* Ψ ≅ Ψ Lg^*` of derived scalar extension `Ψ = - ⊗ᴸ_R S` with the
derived pullback (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`) and the
commutation `Lg^* Res ≅ Res Lg^*` of restriction of scalars with the derived pullback
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso`) are mates along the
adjunctions `Ψ ⊣ Res` (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
  {Y Z : Scheme.{u}} (g : Z ⟶ Y)

omit [IsNoetherianRing R] in
/-- The mate of `g^*(S ⊗_R -) ≅ S ⊗_R g^*` along extension and restriction of scalars is the
commutation `g^* (Res M) ≅ Res (g^* M)` of
`AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso`. -/
lemma upperStarRestrictScalarsMap_eq :
    upperStarRestrictScalarsMap R S g = (upperStarRestrictScalarsIso (algebraMap R S) g).hom := by
  have hA : (mateEquiv (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g)
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g)
        (upperStarRestrictScalarsMap R S g)) =
      conjugateEquiv ((sheafExtendScalarsAdjunction (algebraMap R S) Y).comp
          (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g))
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).comp
          (sheafExtendScalarsAdjunction (algebraMap R S) Z))
        (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv :=
    iterated_mateEquiv_conjugateEquiv _ _ _ _ _
  rw [sheafExtendScalarsCompUpperStarIso, conjugateIsoEquiv_symm_apply_inv,
    Equiv.apply_symm_apply] at hA
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g)
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Y) (algebraMap R S))
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) (algebraMap R S))
    (TwoSquare.mk _ _ _ _ (lowerStarCompSheafComposeCoextendScalarsIso R S g).inv)
  rw [mateEquiv_symm_lowerStarCompSheafComposeCoextendScalarsIso] at h
  exact ((Equiv.eq_symm_apply _).2 hA).trans (h.trans rfl)

omit [IsNoetherianRing R] in
/-- On the image of an object of the homotopy category, the commutation
`Lg^* Res ≅ Res Lg^*` is induced, through the counits of the derived pullbacks, by
`g^* Res ≅ Res g^*`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_hom_app_Qh_obj
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} S)) (.up ℤ)) :
    (leftDerivedUpperStarRestrictScalarsIso (algebraMap R S) g).hom.app
        (DerivedCategory.Qh.obj K) ≫
      (Sheaf.derivedRestrictScalars _ (algebraMap R S)).map
        ((g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorCounit.app K) ≫
      (Sheaf.restrictScalars (ProEt.topology Z) (algebraMap R S)).mapDerivedCategoryFactorsh.hom.app
        (((g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).obj K) =
    L((g)^*[ModuleCat.{u + 1} R]).map
        ((Sheaf.restrictScalars (ProEt.topology Y)
          (algebraMap R S)).mapDerivedCategoryFactorsh.hom.app K) ≫
      (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorCounit.app
        (((Sheaf.restrictScalars _ (algebraMap R S)).mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory (upperStarRestrictScalarsIso (algebraMap R S) g).hom
          (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) := by
  exact Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj_comp_counit
    (R₁ := Sheaf.restrictScalars (ProEt.topology Y) (algebraMap R S))
    (R₂ := Sheaf.restrictScalars (ProEt.topology Z) (algebraMap R S)) _ _
    (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh _ _
    (g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh
    (upperStarRestrictScalarsIso (algebraMap R S) g) _ rfl K

omit [IsNoetherianRing R] in
/-- The counit form of `upperStarRestrictScalarsMap_eq` on homotopy categories. -/
lemma mapHomotopyCategory_upperStarRestrictScalarsIso_counit
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} S)) (.up ℤ)) :
    ((sheafExtendScalars (algebraMap R S) Z).mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory (upperStarRestrictScalarsIso (algebraMap R S) g).hom
            (.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) ≫
      ((sheafExtendScalarsAdjunction (algebraMap R S) Z).mapHomotopyCategory (.up ℤ)).counit.app
        (((g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).obj K) =
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).inv.app
        (((Sheaf.restrictScalars (ProEt.topology Y) (algebraMap R S)).mapHomotopyCategory
          (.up ℤ)).obj K) ≫
      ((g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).map
        (((sheafExtendScalarsAdjunction (algebraMap R S) Y).mapHomotopyCategory (.up ℤ)).counit.app
          K) := by
  exact Adjunction.mapHomotopyCategory_map_comp_counit_app (.up ℤ)
    (sheafExtendScalarsAdjunction (algebraMap R S) Y)
    (sheafExtendScalarsAdjunction (algebraMap R S) Z)
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g) _ (upperStarRestrictScalarsMap_eq R S g)
    (R₁ := Sheaf.restrictScalars (ProEt.topology Y) (algebraMap R S))
    (R₂ := Sheaf.restrictScalars (ProEt.topology Z) (algebraMap R S)) _ rfl K

/-- The inverse form of `leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit`. -/
lemma leftDerivedUpperStarExtendScalarsIso_inv_app_comp_counit
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedUpperStarExtendScalarsIso R S g).inv.app (DerivedCategory.Qh.obj K) ≫
        (leftDerivedSheafExtendScalarsUpperStarCounit R S g).app K =
      (leftDerivedUpperStarSheafExtendScalarsCounit R S g).app K ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).inv.app K) := by
  rw [← cancel_epi ((leftDerivedUpperStarExtendScalarsIso R S g).hom.app
    (DerivedCategory.Qh.obj K)), Iso.hom_inv_id_app_assoc,
    leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  simp

/-- The commutation `Lg^* Ψ ≅ Ψ Lg^*` of derived scalar extension with the derived pullback is
the mate, along the adjunctions `Ψ ⊣ Res`, of the commutation `Lg^* Res ≅ Res Lg^*` of
restriction of scalars with the derived pullback (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`). -/
theorem mateEquiv_leftDerivedUpperStarExtendScalarsIso_inv :
    mateEquiv (leftDerivedSheafExtendScalarsAdjunction R S Y)
        (leftDerivedSheafExtendScalarsAdjunction R S Z)
        (leftDerivedUpperStarExtendScalarsIso R S g).inv =
      (leftDerivedUpperStarRestrictScalarsIso (algebraMap R S) g).hom := by
  exact Adjunction.mateEquiv_leftDerived_inv_eq (sheafExtendScalarsAdjunction (algebraMap R S) Y)
    (sheafExtendScalarsAdjunction (algebraMap R S) Z)
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g)
    (upperStarRestrictScalarsIso (algebraMap R S) g) (upperStarRestrictScalarsMap_eq R S g)
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g) rfl _ _ _ _
    (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh _ _
    (g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh
    (leftDerivedSheafExtendScalarsAdjunction R S Y) (leftDerivedSheafExtendScalarsAdjunction R S Z)
    (leftDerivedSheafExtendScalarsAdjunction_counit_app_Qh_obj R S Y)
    (leftDerivedSheafExtendScalarsAdjunction_counit_app_Qh_obj R S Z)
    (leftDerivedUpperStarExtendScalarsIso R S g) _ rfl _ rfl
    (leftDerivedUpperStarExtendScalarsIso_inv_app_comp_counit R S g) _ rfl

end AlgebraicGeometry.ProEtale
