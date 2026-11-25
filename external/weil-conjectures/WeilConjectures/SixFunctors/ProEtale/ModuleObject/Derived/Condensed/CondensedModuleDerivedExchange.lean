/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Canonical derived exchange for condensed module objects

Source: blueprint proper-base-change rational proof, paragraph (3), canonical exchange;
literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
def-tw-frobenius-action.md, ordinary transport along the geometric Frobenius.
(blueprint: def-sf-condensed-module-derived-exchange).

The definitions are moved without changing their terms from DerivedExchangeExactNormalization.
They use arbitrary commutative squares and ordinary unbounded derived categories.

## Main definitions

* `moduleObjectDerivedPullbackSquareComparison`: inverse compositor, equality, compositor.
* `moduleObjectDerivedExchange`: the unit--square--counit mate of this comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ambient pullback-square comparison, using the inverse compositor for `(p', g)`,
the square equality, and the compositor for `(g', p)`.
Source: blueprint rational proof (3), canonical exchange
(blueprint: def-sf-condensed-module-derived-exchange). -/
def moduleObjectDerivedPullbackSquareComparison {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) :
    moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ p' ≅
      moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g' :=
  (leftDerivedUpperStarComp Λ p' g).symm ≪≫
    eqToIso (congrArg (moduleObjectDerivedPullback Λ) sq.w.symm) ≪≫
      leftDerivedUpperStarComp Λ g' p

/-- The ambient unit--square--counit exchange map. `mateEquiv` inserts the unit for `p'`,
applies its right adjoint to the square comparison, and contracts the counit for `p`.
Source: blueprint rational proof (3), canonical exchange
(blueprint: def-sf-condensed-module-derived-exchange). -/
def moduleObjectDerivedExchange {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) :
    moduleObjectDerivedPushforward Λ p ⋙ moduleObjectDerivedPullback Λ g ⟶
      moduleObjectDerivedPullback Λ g' ⋙ moduleObjectDerivedPushforward Λ p' :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p')
    (TwoSquare.mk _ _ _ _ (moduleObjectDerivedPullbackSquareComparison Λ sq).hom))

end AlgebraicGeometry.ProEtale.CondensedRing
