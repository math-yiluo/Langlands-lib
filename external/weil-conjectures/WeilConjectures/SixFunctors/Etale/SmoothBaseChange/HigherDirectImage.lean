/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition

/-!
# Transition maps of higher direct images

For a commutative triangle `a ≫ h = h'` of schemes, with `a : Y' ⟶ Y` and `h : Y ⟶ X`, there
is a canonical map `Rh_* K ⟶ Rh'_* (a^* K)`, the composite of the unit of `Lh'^* ⊣ Rh'_*`,
the composition isomorphism `Lh'^* ≅ Lh^* ⋙ La^*` and the counit of `Lh^* ⊣ Rh_*`. In degree
`q` it gives the transition map `R^q h_* F ⟶ R^q h'_* a^* F` of higher direct images. These
are the maps along which higher direct images are compared when the source scheme varies, as
in the limit theorem `AlgebraicGeometry.Etale.higherDirectImage_limit`.

The transition maps and the limit theorem are in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition`, the
cohomology presheaf and its consequences in `...HigherDirectImage.CohomPresheaf` and
`...HigherDirectImage.FilteredColimit`; this module imports all of them.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarPlusTransition`: the map `Rh_* K ⟶ Rh'_* (a^* K)`.
- `AlgebraicGeometry.Etale.higherDirectImageTransition`: the map
  `R^q h_* F ⟶ R^q h'_* a^* F`.
- `AlgebraicGeometry.Etale.higherDirectImagePresheaf`: the presheaf `W ↦ H^q(W ×_X Y, K|)`.
- `AlgebraicGeometry.Etale.higherDirectImagePresheafToSheaf`: the canonical map from it to
  `R^q h_* K`.

## Main statements

- `AlgebraicGeometry.Etale.higherDirectImage_limit`: higher direct images commute with limits
  of schemes along affine transition morphisms.
- `AlgebraicGeometry.Etale.isIso_higherDirectImagePresheafToSheaf`: `R^q h_* K` is the
  sheafification of `W ↦ H^q(W ×_X Y, K|)` for a quasi-compact quasi-separated `h`.
- `AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`: higher direct images
  along a quasi-compact quasi-separated morphism commute with filtered colimits of sheaves.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`: the
  higher direct image `R^q h_* (Λ/dΛ)` vanishes as soon as every class of
  `H^q(U ×_X Y, ℤ/e)`, for `e ∣ d` and `U` affine étale over `X`, dies on an étale cover of `U`.

## References

- Stacks Project, Lemma 59.51.7, <https://stacks.math.columbia.edu/tag/09Z1>
- Stacks Project, Lemma 59.51.6, <https://stacks.math.columbia.edu/tag/03Q8>
-/
