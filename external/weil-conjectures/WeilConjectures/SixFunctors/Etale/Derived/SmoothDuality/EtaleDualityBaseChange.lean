/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMapIsoUnit
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChange

/-!
# Base change reflects the invertibility of tensor maps

For a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `f'` quasi-compact, the base change map `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) intertwines the tensor maps of
`f` and of `f'` (`CategoryTheory.Adjunction.projectionTensorMap_mateEquiv`). Hence, where `β`
is an isomorphism, `Lg'^*` of the tensor map of `f` at `(M, N)` is an isomorphism after applying
any functor `H` as soon as the tensor map of `f'` at `(Lg^* M, Lg^* N)` is
(`AlgebraicGeometry.Etale.isIso_map_leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_map_leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`, whose
-- compatibility of the projection map with base change is used below: with the same instances,
-- its statement matches the one expected here syntactically.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- **Base change reflects the invertibility of tensor maps.** For a cartesian square
`g' ≫ f = f' ≫ g` with quasi-compact `f'`, if the base change map `Lg'^* Rf^! ⟶ Rf'^! Lg^*` is
an isomorphism at `M` and at `M ⊗ᴸ N`, then for every functor `H`, `H` of `Lg'^*` of the tensor
map of `f` at `(M, N)` is an isomorphism as soon as `H` of the tensor map of `f'` at
`(Lg^* M, Lg^* N)` is one. -/
theorem isIso_map_leftDerivedUpperStar_map_rightDerivedUpperShriekTensorMap
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app M)]
    [IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (M ⊗ N))]
    {E : Type*} [Category* E]
    (H : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ E)
    (h : IsIso (H.map (rightDerivedUpperShriekTensorMap f'
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M) ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N)))) :
    IsIso (H.map
      ((L((g')^*[ModuleCat.{u + 1} Λ])).map (rightDerivedUpperShriekTensorMap f M N))) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  have : ∀ N, IsIso (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N) :=
    fun N ↦ by
      unfold derivedSquareUpperStarIsoInvApp
      infer_instance
  have : IsIso ((mateEquiv (rightDerivedUpperShriekAdjunction Λ f)
      (rightDerivedUpperShriekAdjunction Λ f')
        (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))).app M) :=
    ‹IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app M)›
  have : IsIso ((mateEquiv (rightDerivedUpperShriekAdjunction Λ f)
      (rightDerivedUpperShriekAdjunction Λ f')
        (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))).app (M ⊗ N)) :=
    ‹IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (M ⊗ N))›
  exact Adjunction.isIso_map_map_projectionTensorMap_of_isIso
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
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib M N H h

end Etale

end AlgebraicGeometry
