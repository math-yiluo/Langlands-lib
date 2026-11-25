/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange

/-!
# The compactly supported base change map

For a cartesian square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

and a compactification `c` of `f`, write `c = (X ⟶[i] Z ⟶[p] Y)`, i.e. `i := c.i` and
`p := c.g` (we write `p` rather than `g` for the proper map, since `g` is the base change
morphism). The base changed compactification `c.ofIsPullback sq = (X' ⟶[i'] Z ×_Y Y' ⟶[p'] Y')`
of `f'` sits in a diagram of two cartesian squares

```
  X' --g'--> X
  |          |
  i'         i
  ↓          ↓
  Z' --g''-> Z
  |          |
  p'         p
  ↓          ↓
  Y' --g---> Y
```

with `Z' = Z ×_Y Y'` and `g'' = pullback.fst c.g g`. Pasting the derived base change map `Ex_*`
of the bottom square with the derived base change isomorphism of the extension by zero for the
top square gives the compactly supported base change map `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*`,
computed with `c` and its base change. Using the chosen compactification of `f` and the
comparison isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso` for `f'` gives
`Ex_!` for the derived lower shrieks `R(f)_!` and `R(f')_!`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`: the
  exchange map `Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`: the exchange map
  `Ex_! : Lg^* R(f)_! ⟶ R(f')_! Lg'^*`.

## Main results

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_iff`:
  `Ex_!(c)` is an isomorphism if and only if `Ex_*` of the bottom square, whiskered by `Di_!`,
  is one.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap`:
  `Ex_!(c)` is an isomorphism if `Ex_*` of the bottom square is.

## TODO

- Show that `Ex_!(c)` does not depend on `c`, i.e. that it is compatible with the comparison
  isomorphisms `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationIso`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso` is only available for torsion
  coefficients, where it rests on unbounded proper base change, so `Ex_!` is defined there
  only. The blueprint defines `Ex_!` on bounded below derived categories; a version built from
  `derivedBaseChangeMapPlus` and `rightDerivedLowerShriekOfCompactificationPlusIso` would only
  need bounded below proper base change.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **The compactly supported base change map along a compactification** `Ex_!(c)`: for a
cartesian square `g' ≫ f = f' ≫ g` and a compactification `c` of `f`, the natural
transformation `Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*`, where `c ×_Y Y'` is the base changed
compactification `c.ofIsPullback sq` of `f'`. Write `i := c.i`, `p := c.g`, and `i'`, `p'` for
the corresponding maps of `c ×_Y Y'`, so that `Rp_*` is `R((c.g)_*[A])`. Then `Ex_!(c)` is the
derived base change map `Ex_*` of the cartesian square `Z ×_Y Y' ⟶ Z` over `g`, whiskered by
`Di_!`, followed by the inverse of the derived base change isomorphism of the extension by
zero `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso` for the cartesian
square `AlgebraicGeometry.Compactification.isPullback_i_ofIsPullback`, whiskered by `Rp'_*`.

```
  D(X) --Lg'^*--> D(X')
   |               |
  Di_!     ≅     Di'_!
   ↓               ↓
  D(Z) --Lg''^*-> D(Z')
   |               |
  Rp_*    ⇓ Ex_*  Rp'_*
   ↓               ↓
  D(Y) --Lg^*---> D(Y')
```

(blueprint: `sk-def-sf-exchanges`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    Rf_!(c)[A] ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ Rf_!(c.ofIsPullback sq)[A] :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open[A])
      (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g g).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionLowerShriekBaseChangeIso A (c.isPullback_i_ofIsPullback sq)).inv
      R(((c.ofIsPullback sq).g)_*[A]) ≫
    (Functor.associator _ _ _).hom

set_option backward.isDefEq.respectTransparency false in
/-- `Ex_!(c)` is an isomorphism if and only if the derived base change map `Ex_*` for the
proper map `c.g` of the compactification, whiskered by `Di_!`, is one: the other factors of
`Ex_!(c)` are isomorphisms. In particular proper base change for `c.g` gives compactly
supported base change for `f`. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_iff
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c) ↔
      IsIso (Functor.whiskerLeft D((c.i)_!open[A])
        (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g g).toCommSq)) := by
  simp only [rightDerivedLowerShriekOfCompactificationBaseChangeMap, isIso_comp_left_iff,
    isIso_comp_right_iff]

/-- If the derived base change map `Ex_*` of the cartesian square `c.Z ×_Y Y' ⟶ c.Z` over `g`
is an isomorphism, then so is `Ex_!(c)`. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f)
    [IsIso (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g g).toCommSq)] :
    IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c) :=
  (isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_iff A sq c).2 inferInstance

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- **The compactly supported base change map** `Ex_! : Lg^* R(f)_! ⟶ R(f')_! Lg'^*` for a
cartesian square `g' ≫ f = f' ≫ g`, for torsion coefficients: the map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap` for the
chosen compactification of `f`, followed by the comparison isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso` between the derived lower shriek of `f'`
computed with its base change and the one computed with the chosen compactification of `f'`.
That comparison is an isomorphism by proper base change, hence the torsion coefficients.
(blueprint: `sk-def-sf-exchanges`) -/
noncomputable def rightDerivedLowerShriekBaseChangeMap [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ] :=
  rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq
      (HasCompactification.compactification f) ≫
    Functor.whiskerLeft _ (rightDerivedLowerShriekIso Λ _).hom

end Etale

end AlgebraicGeometry
