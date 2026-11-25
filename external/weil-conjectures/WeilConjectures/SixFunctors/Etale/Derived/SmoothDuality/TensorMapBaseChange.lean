/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDualityBaseChange

/-!
# Base change of the tensor maps of the exceptional inverse image

For a cartesian square `g' ≫ f = f' ≫ g` with `f'` quasi-compact, the base change map
`β : Lg'^* Rf^! ⟶ Rf'^! Lg^*` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`)
intertwines the tensor maps `Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)` of `f` and of `f'`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`), the co-projection maps of
`lem-pur-coprojection`. This is `CategoryTheory.Adjunction.projectionTensorMap_mateEquiv` for the
compatibility of the projection map with base change
(`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`).

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap_baseChange`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

-- The instances of
-- `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDualityBaseChange`, under which
-- the base change of the projection map matches syntactically.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- **Base change of the co-projection.** The base change map `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*`
intertwines the tensor maps of `f` and `f'`:
```
Lg'^*(Rf^! M ⊗ Lf^* N) ──Lg'^* τ──▶ Lg'^* Rf^!(M ⊗ N) ──β──▶ Rf'^! Lg^*(M ⊗ N)
        ≅ │                                                   │ ≅
          ▼                                                   ▼
Lg'^* Rf^! M ⊗ Lg'^* Lf^* N ──β ⊗ κ──▶ Rf'^! Lg^* M ⊗ Lf'^* Lg^* N ──τ'──▶ Rf'^!(Lg^* M ⊗ Lg^* N)
```
-/
theorem rightDerivedUpperShriekTensorMap_baseChange
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (rightDerivedUpperShriekTensorMap f M N) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq).app (M ⊗ N) ≫
          (R(f')^![Λ]).map (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g M N).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g' _ _).hom ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq).app M ▷ _ ≫
          _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N ≫
            rightDerivedUpperShriekTensorMap f' _ _ := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  exact Adjunction.projectionTensorMap_mateEquiv
    (rightDerivedUpperShriekAdjunction Λ f)
    (rightDerivedUpperShriekAdjunction Λ f')
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f').app M).app N)
    (projectionMap_app_app_naturality_left f')
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g' M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left g φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap Λ sq) (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib M N

end Etale

end AlgebraicGeometry
