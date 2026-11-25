/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar

/-!
# The derived base change map and restriction of scalars

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings. For a commutative square of schemes
`g' ≫ f = f' ≫ g` whose vertical morphisms have higher direct images vanishing in large degrees,
the derived base change map `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`) is compatible with the coefficient comparisons
of `Rf_*`, `Rf'_*`, `Lg^*` and `Lg'^*`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_restrictScalars`). This is used for the
compatible systems of Frobenius coefficient morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` is compatible with the
coefficient comparisons of the derived pullbacks. -/
lemma derivedSquareUpperStarIso_hom_app_restrictScalars (sq : CommSq g' f' f g)
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (L((f')^*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app N) ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ f').hom.app
        ((L((g)^*[ModuleCat.{u + 1} Λ'])).obj N) ≫
      (Sheaf.derivedRestrictScalars _ ρ).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom.app N) =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
        ((Sheaf.derivedRestrictScalars _ ρ).obj N) ≫
      (L((g')^*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarRestrictScalarsIso ρ f).hom.app N) ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ g').hom.app
        ((L((f)^*[ModuleCat.{u + 1} Λ'])).obj N) := by
  have h₁ := leftDerivedUpperStarRestrictScalarsIso_comp_hom_app' ρ f' g (g' ≫ f) sq.w N
  have h₂ := leftDerivedUpperStarRestrictScalarsIso_comp_hom_app' ρ g' f (g' ≫ f) rfl N
  have h₁' : (L((f')^*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app N) ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ f').hom.app
        ((L((g)^*[ModuleCat.{u + 1} Λ'])).obj N) =
      (leftDerivedUpperStarComp _ f' g (g' ≫ f) sq.w).inv.app
          ((Sheaf.derivedRestrictScalars _ ρ).obj N) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ (g' ≫ f)).hom.app N ≫
        (Sheaf.derivedRestrictScalars _ ρ).map
          ((leftDerivedUpperStarComp _ f' g (g' ≫ f) sq.w).hom.app N) := by
    rw [h₁, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% h₁']
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h₂]
/-- **The derived base change map is compatible with restriction of scalars** (statement (A)):
for a commutative square `g' ≫ f = f' ≫ g` whose vertical morphisms have higher direct images
vanishing in degrees `> d` and `> d'`, the derived base change map
`Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` over `Λ` and over `Λ'` are related by the coefficient
comparisons of `Rf_*`, `Lg^*`, `Lg'^*` and `Rf'_*`. -/
lemma derivedBaseChangeMap_app_restrictScalars (sq : CommSq g' f' f g) (d d' : ℕ)
    (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hd' : ∀ (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d' < q →
      IsZero ((((f')_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d hd)
        (leftDerivedUpperStarRestrictScalarsIso ρ g)).hom.app K ≫
      (Sheaf.derivedRestrictScalars Y'.smallEtaleTopology ρ).map
        ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ') sq).app K) =
    (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj K) ≫
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f' d' hd')).hom.app K := by
  rw [pasteTwoSquaresIso_hom_app, pasteTwoSquaresIso_hom_app, Category.assoc]
  exact Adjunction.mateEquiv_restrict (derivedUpperStarLowerStarAdjunction _ f)
    (derivedUpperStarLowerStarAdjunction _ f') (derivedUpperStarLowerStarAdjunction _ f)
    (derivedUpperStarLowerStarAdjunction _ f') (derivedSquareUpperStarIso _ sq).hom
    (derivedSquareUpperStarIso _ sq).hom (leftDerivedUpperStarRestrictScalarsIso ρ f)
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d hd)
    (leftDerivedUpperStarRestrictScalarsIso ρ f')
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f' d' hd')
    (leftDerivedUpperStarRestrictScalarsIso ρ g) (leftDerivedUpperStarRestrictScalarsIso ρ g')
    (mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso ρ f d hd)
    (mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso ρ f' d'
      hd')
    (derivedSquareUpperStarIso_hom_app_restrictScalars ρ sq) K

end AlgebraicGeometry.Etale
