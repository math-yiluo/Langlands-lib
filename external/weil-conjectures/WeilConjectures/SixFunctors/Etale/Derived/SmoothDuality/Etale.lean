/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChangeCharts
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChangeUnit

/-!
# Base change for the exceptional inverse image along an étale morphism

The étale case (c) of the proof of blueprint
`proposition-exceptional-inverse-image-smooth-morphism--6` (in the form of the proof of
`proposition-exceptional-inverse-image-smooth-morphism`): for an étale morphism `e : X ⟶ Y`
admitting a compactification, `Re^! ≅ Le^*`, with counit the counit of the extension by zero `e_!`,
and the canonical base change map `Lg'^* Re^! ⟶ Re'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) is an isomorphism
(`AlgebraicGeometry.Etale.etaleBaseChange`).

The compactly supported direct image `Rf_!(c)` of a compactification `c` of `e` is the
extension by zero `De_!` (`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`), so
that `Rf_!(c) ⊣ Le^*`, and the units of these adjunctions commute with base change
(`AlgebraicGeometry.Etale.compactificationEtaleUnit_baseChange`); the base change map, the mate
of the inverse of the compact-support base change, is then the canonical isomorphism
`Lg'^* Le^* ≅ Le'^* Lg^*`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_unit`).

## Main statements

- `AlgebraicGeometry.Etale.etaleBaseChange`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_affineLine`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Base change for the exceptional inverse image along an étale morphism**: for an étale
`e` admitting a compactification and a cartesian square `g' ≫ e = e' ≫ g` with quasi-compact
`e'` admitting a compactification, the canonical base change map `Lg'^* Re^! ⟶ Re'^! Lg^*` is an
isomorphism. -/
theorem etaleBaseChange : EtaleBaseChange Λ := by
  intro V W V' W' e _ _ _ g e' g' sq _ _
  have : _root_.AlgebraicGeometry.Etale e' := MorphismProperty.of_isPullback sq inferInstance
  have := isIso_compactificationEtaleComparison Λ e (HasCompactification.compactification e)
  have := isIso_compactificationEtaleComparison Λ e'
    ((HasCompactification.compactification e).ofIsPullback sq)
  refine isIso_rightDerivedUpperShriekBaseChangeMap_of_unit Λ sq
    (compactificationEtaleAdjunction Λ e (HasCompactification.compactification e))
    (compactificationEtaleAdjunction Λ e'
      ((HasCompactification.compactification e).ofIsPullback sq)) (fun N ↦ ?_)
  rw [compactificationEtaleAdjunction_unit_app, compactificationEtaleAdjunction_unit_app]
  exact compactificationEtaleUnit_baseChange Λ sq (HasCompactification.compactification e) N

/-- **Base change for smooth morphisms from the affine-line case**: if the affine-line
projections satisfy base change (`AlgebraicGeometry.Etale.AffineLineBaseChange`,
the elementary case (a) of the proof of blueprint
`proposition-exceptional-inverse-image-smooth-morphism--6`), then for every smooth `f : X ⟶ Y` of
relative dimension `d` admitting a compactification, over a quasi-separated `Y`, with the exponent
of `Λ` invertible on `X`, the canonical base change map `Lg'^* Rf^! ⟶ Rf'^! Lg^*` of a cartesian
square with quasi-compact `f'` admitting a compactification is an isomorphism: the étale case is
`AlgebraicGeometry.Etale.etaleBaseChange`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_affineLine (h₁ : AffineLineBaseChange Λ)
    {X Y : Scheme.{u}} [QuasiSeparatedSpace Y] [HasInvertibleExponent Λ X] (f : X ⟶ Y)
    [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f] ⦃X' Y' : Scheme.{u}⦄
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) :=
  isIso_rightDerivedUpperShriekBaseChangeMap_of_etale_of_affineLine (etaleBaseChange Λ) h₁ f d sq

end Etale

end AlgebraicGeometry
