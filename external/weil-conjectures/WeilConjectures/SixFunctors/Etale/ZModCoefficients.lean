/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# The coefficient ring `ℤ/ℓ` for étale sheaves of modules

The étale sheaves of modules of the six-functor formalism have coefficients in a ring of the
universe `u + 1`. This file fixes the ring `ℤ/n` in that universe, `ULift (ZMod n)`, and the
constant sheaf of `ℤ/n`-modules on a scheme; its underlying abelian sheaf is the constant sheaf
`AlgebraicGeometry.Scheme.constantZMod`.

## Main definitions

- `AlgebraicGeometry.Etale.ZModCoeff`: the ring `ℤ/n` in the universe `u + 1`.
- `AlgebraicGeometry.Etale.constantZModModule`: the constant sheaf of `ℤ/n`-modules.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The ring `ℤ/n` of coefficients, in the universe `u + 1` of the étale sheaves of modules on
schemes of the universe `u`. -/
abbrev ZModCoeff (n : ℕ) : Type (u + 1) := ULift.{u + 1} (ZMod n)

/-- The constant étale sheaf of `ℤ/n`-modules with value `ℤ/n` on a scheme `X`. -/
noncomputable abbrev constantZModModule (X : Scheme.{u}) (n : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZModCoeff.{u} n)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZModCoeff.{u} n))).obj
    (ModuleCat.of (ZModCoeff.{u} n) (ZModCoeff.{u} n))

end AlgebraicGeometry.Etale
