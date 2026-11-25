/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions

/-!
# Dual base change for the exceptional inverse image

For a cartesian square of schemes
```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```
with `f`, `f'` admitting compactifications and torsion coefficients `Λ`, the compact-support
base change `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). Its conjugate under the
composite adjunctions `Lg^* Rf_! ⊣ Rf^! Rg_*` and `Rf'_! Lg'^* ⊣ Rg'_* Rf'^!` is the exchange
`Rg'_* Rf'^! ⟶ Rf^! Rg_*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeMap`), an isomorphism. Its
inverse is the *dual base change isomorphism*
```
  β^∨ : Rf^! Rg_* ≅ Rg'_* Rf'^!
```
of blueprint `prop-exc-ambient-dual-base-change`. Here the right adjoint `Rf^!` of `Rf_!` exists
unconditionally (`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`), so the
ambient exceptional right adjoint datum of the blueprint is automatic.

The pro-étale analogue is not stated: the pro-étale compact-support base change
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekBaseChangeMap` is only known to be invertible
on complexes of étale origin, not as a natural transformation of functors on the ambient
derived categories, so its conjugate is not known to be invertible.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDualBaseChangeIso`: `β^∨`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- Blueprint `prop-exc-ambient-dual-base-change`: Dual base change for the ambient right
adjoint is formal.

For a cartesian square `g' ≫ f = f' ≫ g` with `f`, `f'` admitting compactifications (and `f'`
quasi-compact) and `g` arbitrary, and torsion coefficients `Λ`, the right-adjoint mate
`β^∨ : Rf^! Rg_* ⟶ Rg'_* Rf'^!` of the inverse of the compact-support base change isomorphism
is an isomorphism. It is the inverse of the exchange isomorphism
`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeMap`, the conjugate of
`Ex_!`. In the diagrammatic order of composition of functors used here, it is
`Rg_* ⋙ Rf^! ≅ Rf'^! ⋙ Rg'_*`. -/
noncomputable def rightDerivedUpperShriekDualBaseChangeIso (sq : IsPullback g' f' f g) :
    R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ R(f)^![Λ] ≅
      R(f')^![Λ] ⋙ R((g')_*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_rightDerivedUpperShriekLowerStarBaseChangeMap Λ sq
  (asIso (rightDerivedUpperShriekLowerStarBaseChangeMap Λ sq)).symm

end Etale

end AlgebraicGeometry
