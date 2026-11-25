/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekTriangulated

/-!
# The pro-étale derived functors are triangulated

The derived functors on the unbounded derived categories of pro-étale sheaves are triangulated,
for the commutations with shifts of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift`:

* `Rg_*` is a right derived functor, hence triangulated;
* `Rf_!(c) = D(i_!) ⋙ Rg_*` for a compactification `c = (i, g)` is a composite of two
  triangulated functors
  (`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekTriangulated`);
* `Lg^*` is left adjoint to the triangulated functor `Rg_*`, and its commutation with shifts is
  the one induced by the adjunction, so it is triangulated by
  `Adjunction.isTriangulated_leftAdjoint`.

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.Triangulated`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The total right derived pushforward `Rg_*` is triangulated, as every right derived functor
is. -/
instance isTriangulated_rightDerivedLowerStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (R((g)_*[A])).IsTriangulated :=
  inferInstance

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback `Lg^*` is triangulated, being left adjoint to the triangulated functor
`Rg_*` (`ProEtale.derivedUpperStarLowerStarAdjunction`), compatibly with the shifts. -/
instance isTriangulated_leftDerivedUpperStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).IsTriangulated :=
  (derivedUpperStarLowerStarAdjunction A g).isTriangulated_leftAdjoint

end ProEtale

end AlgebraicGeometry
