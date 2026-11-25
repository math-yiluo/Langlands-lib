/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.CompactificationLowerStarBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence

/-!
# `Rf_! ≅ Rf_*` intertwines the exchange maps

For a cartesian square `g' ≫ f = f' ≫ g` with `f` and `f'` proper, the isomorphisms
`Rf_! ≅ Rf_*` and `Rf'_! ≅ Rf'_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`) intertwine the
compactly supported base change map `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`) and the proper base change map
`Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` (`AlgebraicGeometry.Etale.derivedBaseChangeMap`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
  {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [IsProper f] [IsProper f']

omit [Finite Λ] [IsProper f'] in
/-- The isomorphism `Rf_! ≅ Rf_*` is the forget-supports map of the chosen compactification
`(i, p)` of `f`: `Rp_*` of `D(i_!) ⟶ Ri_*`, followed by `Ri_* ⋙ Rp_* ⟶ Rf_*`. -/
lemma rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_app_eq
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).hom.app K =
      R(((HasCompactification.compactification f).g)_*[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekToLowerStar _
            (HasCompactification.compactification f).i).app K) ≫
        (rightDerivedLowerStarCompHom _ (HasCompactification.compactification f).i
          (HasCompactification.compactification f).g f
          (HasCompactification.compactification f).comm).app K := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
    rightDerivedLowerShriekToLowerStarComp_comp_eq]
  rfl

/-- **`Rf_! ≅ Rf_*` intertwines the exchange maps** `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` and
`Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` of a cartesian square `g' ≫ f = f' ≫ g` with `f` and `f'`
proper. -/
theorem rightDerivedLowerShriekBaseChangeMap_comp_lowerStarIso
    (sq : IsPullback g' f' f g) :
    rightDerivedLowerShriekBaseChangeMap Λ sq ≫
        Functor.whiskerLeft L((g')^*[ModuleCat.{u + 1} Λ])
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f').hom =
      Functor.whiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} Λ) f).hom L((g)^*[ModuleCat.{u + 1} Λ]) ≫
        derivedBaseChangeMap _ sq.toCommSq := by
  let c := HasCompactification.compactification f
  ext K
  rw [rightDerivedLowerShriekBaseChangeMap_eq]
  simp only [rightDerivedLowerShriekBaseChangeMap', rightDerivedLowerShriekIso,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    Category.assoc, rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_app_eq, Functor.map_comp]
  rw [rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar]
  exact rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app_comp_toLowerStar _
    sq.toCommSq c (c.ofIsPullback sq) _ (c.isPullback_i_ofIsPullback sq)
    (IsPullback.of_hasPullback c.g g).toCommSq K

/-- `AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_comp_lowerStarIso`
at an object. -/
@[reassoc]
theorem rightDerivedLowerShriekBaseChangeMap_app_comp_lowerStarIso
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeMap Λ sq).app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f').hom.app
          ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((g)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).hom.app K) ≫
        (derivedBaseChangeMap _ sq.toCommSq).app K := by
  simpa using NatTrans.congr_app
    (rightDerivedLowerShriekBaseChangeMap_comp_lowerStarIso
      (Λ := Λ) sq) K

/-- The inverse form of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_comp_lowerStarIso`:
`Lg^*` of `Rf_* ≅ Rf_!` followed by `Ex_!` is `Ex_*` followed by `Rf'_* ≅ Rf'_!`. -/
@[reassoc]
theorem leftDerivedUpperStar_map_lowerStarIso_inv_comp_rightDerivedLowerShriekBaseChangeMap
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).inv.app K) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sq).app K =
      (derivedBaseChangeMap _ sq.toCommSq).app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f').inv.app
          ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) := by
  rw [← Iso.app_inv (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f'),
    Iso.eq_comp_inv, Iso.app_hom, Category.assoc,
    rightDerivedLowerShriekBaseChangeMap_app_comp_lowerStarIso, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end Etale

end AlgebraicGeometry
