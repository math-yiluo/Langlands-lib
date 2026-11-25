/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange

/-!
# Base change of the exceptional inverse image from a compatible family of units

For a cartesian square `g' ≫ f = f' ≫ g` and a compactification `c` of `f`, the canonical base
change map `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) is an isomorphism as soon as the
compactly supported direct images `Rf_!(c)` and `Rf'_!(c')` of `c` and of its base change `c'`
have the derived pullbacks `Lf^*` and `Lf'^*` as right adjoints, with units compatible with the
compact-support base change `Ex_!(c)`: then the mate of `Ex_!(c)⁻¹` is the canonical isomorphism
`Lg'^* Lf^* ≅ Lf'^* Lg^*`, and invertibility of mates does not depend on the choice of the
adjunctions.

This is the formal part of the étale case of the proof of blueprint
`proposition-exceptional-inverse-image-smooth-morphism--6`: for an étale `f` the derived pullback is
right adjoint to the compactly supported direct image.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isIso_mateEquiv'`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_unit`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- **Base change from adjunctions along the compactification.** For a cartesian square
`g' ≫ f = f' ≫ g` with quasi-compact `f'`, let `c` be the chosen compactification of `f` and
`c'` its base change. If, for some right adjoints of `Rf_!(c)` and `Rf'_!(c')`, the mate of the
inverse of the compact-support base change `Ex_!(c)` is invertible, then the base change map
`Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an isomorphism. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_isIso_mateEquiv'
    (sq : IsPullback g' f' f g)
    {R₁ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {R₂ : _root_.DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (adj₁ : Rf_!(HasCompactification.compactification f)[ModuleCat.{u + 1} Λ] ⊣ R₁)
    (adj₂ : Rf_!((HasCompactification.compactification f).ofIsPullback sq)[ModuleCat.{u + 1} Λ]
      ⊣ R₂)
    [IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
      (HasCompactification.compactification f))]
    (hm : IsIso (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _
      (inv (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
        (HasCompactification.compactification f)))))) :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have hEx := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have h : inv (rightDerivedLowerShriekBaseChangeMap Λ sq) =
      Functor.whiskerLeft _ (rightDerivedLowerShriekIso Λ
        ((HasCompactification.compactification f).ofIsPullback sq)).inv ≫
      inv (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
        (HasCompactification.compactification f)) := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [rightDerivedLowerShriekBaseChangeMap, Category.assoc,
      ← Category.assoc (Functor.whiskerLeft _ _),
      ← Functor.whiskerLeft_comp, Iso.hom_inv_id, Functor.whiskerLeft_id', Category.id_comp,
      IsIso.hom_inv_id]
  have hinv : TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)) =
      ((TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} Λ) sq (HasCompactification.compactification f)))).whiskerLeft
          (Iso.refl (R(f)_![ModuleCat.{u + 1} Λ])).hom).whiskerRight
        (rightDerivedLowerShriekIso Λ
          ((HasCompactification.compactification f).ofIsPullback sq)).inv := by
    rw [h]
    ext K
    simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom,
      NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have := @isIso_mateEquiv_whiskerLeft_whiskerRight _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    adj₁ (rightDerivedUpperShriekAdjunction _ f) adj₂
    (rightDerivedUpperShriekAdjunction _ f') (Iso.refl (R(f)_![ModuleCat.{u + 1} Λ]))
    (rightDerivedLowerShriekIso Λ ((HasCompactification.compactification f).ofIsPullback sq))
    _ hm
  change IsIso (mateEquiv (rightDerivedUpperShriekAdjunction _ f)
    (rightDerivedUpperShriekAdjunction _ f')
    (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))))
  rw [hinv]
  exact this

/-- **Base change from compatible units.** For a cartesian square `g' ≫ f = f' ≫ g` with
quasi-compact `f'`, let `c` be the chosen compactification of `f` and `c'` its base change.
Suppose that `Rf_!(c) ⊣ Lf^*` and `Rf'_!(c') ⊣ Lf'^*`, with units `η` and `η'` compatible with
the compact-support base change: `η'_{Lg'^* N}` is `Lg'^* η_N` followed by the canonical
isomorphism `Lg'^* Lf^* ≅ Lf'^* Lg^*` and `Lf'^*` of `Ex_!(c)`. Then the base change map
`Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an isomorphism: the mate of `Ex_!(c)⁻¹` is the canonical
isomorphism (`CategoryTheory.mateEquiv_eq_of_unit`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_unit (sq : IsPullback g' f' f g)
    (adj₁ : Rf_!(HasCompactification.compactification f)[ModuleCat.{u + 1} Λ] ⊣
      L((f)^*[ModuleCat.{u + 1} Λ]))
    (adj₂ : Rf_!((HasCompactification.compactification f).ofIsPullback sq)[ModuleCat.{u + 1} Λ]
      ⊣ L((f')^*[ModuleCat.{u + 1} Λ]))
    (h : ∀ N, L((g')^*[ModuleCat.{u + 1} Λ]).map (adj₁.unit.app N) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).inv.app _ ≫
      L((f')^*[ModuleCat.{u + 1} Λ]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
          (HasCompactification.compactification f)).app N) =
      adj₂.unit.app (L((g')^*[ModuleCat.{u + 1} Λ]).obj N)) :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite Λ sq
    (HasCompactification.compactification f)
  have hm := mateEquiv_eq_of_unit adj₁ adj₂ (TwoSquare.mk _ _ _ _
      (inv (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
        (HasCompactification.compactification f))))
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).inv)
    (fun N ↦ by
      rw [← h N]
      simp only [TwoSquare.mk, Category.assoc, ← Functor.map_comp,
        NatIso.isIso_inv_app, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
      erw [Category.comp_id])
  have : IsIso (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _
      (inv (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
        (HasCompactification.compactification f))))) := by
    rw [hm]
    dsimp only [TwoSquare.mk]
    infer_instance
  exact isIso_rightDerivedUpperShriekBaseChangeMap_of_isIso_mateEquiv' Λ sq adj₁ adj₂ this

end Etale

end AlgebraicGeometry
