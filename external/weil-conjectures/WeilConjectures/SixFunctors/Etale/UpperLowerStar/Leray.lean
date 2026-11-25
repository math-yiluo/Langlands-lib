/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The Grothendieck spectral sequence for étale direct images

The abstract Grothendieck spectral sequence of
`WeilConjectures/CategoryTheory/SpectralSequence/Grothendieck.lean` is used for sheaves on small
étale sites through the following dictionary: the abelian category is the Grothendieck abelian
category of étale sheaves `Sheaf X.smallEtaleTopology A`, the left exact functors are the étale
direct images `f_*`, with right derived functors `R^n f_*`, and the composable pair is
`(f_*, h_*)` for `X ⟶ Y ⟶ Z`. The acyclicity hypothesis holds because `f_*` is right adjoint to
the exact pullback `f^*`, so it preserves injective objects.

## Main statements

- `AlgebraicGeometry.Etale.isAcyclicComposablePair_lowerStar`: `(f_*, h_*)` is a composable pair
  with acyclicity.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **The étale dictionary for the Grothendieck spectral sequence.** For morphisms
`f : X ⟶ Y` and `h : Y ⟶ Z`, the étale direct images `(f_*, h_*)` on sheaves with values in a
Grothendieck abelian category `A` form a composable pair with acyclicity: `f_*` is right adjoint
to the exact pullback `f^*`, hence sends injective sheaves to injective, so `h_*`-acyclic,
sheaves.

(blueprint: `def-sp-etale-dictionary`) -/
theorem isAcyclicComposablePair_lowerStar {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    (lowerStar A f).IsAcyclicComposablePair (lowerStar A h) :=
  (upperStarLowerStarAdjunction A f).isAcyclicComposablePair _

end AlgebraicGeometry.Etale
