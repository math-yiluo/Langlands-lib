/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# Dual base change

For a Cartesian square of schemes
```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```
and a finite coefficient ring `Λ`, the right adjoint (the conjugate) of the compact-support base
change isomorphism `Ex_! : Lg^* Rf_! ≅ Rf'_! Lg'^*` is an isomorphism `Rf^! Rg_* ≅ Rg'_* Rf'^!`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeMap`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekLowerStarBaseChangeMap`). This file
records it as an isomorphism and, for proper `g`, reads it through `Rg_! ≅ Rg_*` and
`Rg'_! ≅ Rg'_*`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeIso`
  (`definition-trace-morphism--1`): `Rf^! Rg_* ≅ Rg'_* Rf'^!`.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerShriekBaseChangeIso`
  (`definition-trace-morphism--1`): `Rf^! Rg_! ≅ Rg'_! Rf'^!` for proper `g`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- Blueprint `definition-trace-morphism--1`: Dual base change.

For a Cartesian square
```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```
and a finite coefficient ring `Λ`, the canonical isomorphism `Rf^! Rg_* ≅ Rg'_* Rf'^!`, the
right adjoint of the base-change isomorphism `Ex_! : Lg^* Rf_! ≅ Rf'_! Lg'^*`: it is the inverse
of the conjugate of `Ex_!` along the composite adjunctions `Lg^* ∘ Rf_! ⊣ Rf^! ∘ Rg_*` and
`Rf'_! ∘ Lg'^* ⊣ Rg'_* ∘ Rf'^!`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeMap`). -/
noncomputable def rightDerivedUpperShriekLowerStarBaseChangeIso (sq : IsPullback g' f' f g) :
    R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ R(f)^![Λ] ≅
      R(f')^![Λ] ⋙ R((g')_*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_rightDerivedUpperShriekLowerStarBaseChangeMap Λ sq
  (asIso (rightDerivedUpperShriekLowerStarBaseChangeMap Λ sq)).symm

/-- Blueprint `definition-trace-morphism--1`: Dual base change, the proper case.

For a Cartesian square as in
`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeIso` with `g` proper (so that
`g'` is proper as well; both are assumed, since the instances `HasCompactification g` and
`HasCompactification g'` entering `Rg_!` and `Rg'_!` are those of the properness), the
dual base change isomorphism read through the proper coincidences `Rg_! ≅ Rg_*` and
`Rg'_! ≅ Rg'_*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`):

`Rf^! Rg_! ≅ Rg'_! Rf'^!`. -/
noncomputable def rightDerivedUpperShriekLowerShriekBaseChangeIso [IsProper g] [IsProper g']
    (sq : IsPullback g' f' f g) :
    R(g)_![ModuleCat.{u + 1} Λ] ⋙ R(f)^![Λ] ≅
      R(f')^![Λ] ⋙ R(g')_![ModuleCat.{u + 1} Λ] :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar _ g) _ ≪≫
    rightDerivedUpperShriekLowerStarBaseChangeIso Λ sq ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerShriekIsoRightDerivedLowerStar _ g').symm

end Etale

end AlgebraicGeometry
