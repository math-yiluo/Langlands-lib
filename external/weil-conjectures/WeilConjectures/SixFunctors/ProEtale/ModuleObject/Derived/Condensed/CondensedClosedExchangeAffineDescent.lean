/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeModel
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedExchangeOpenRestriction
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative

/-! # Affine descent for degree-zero condensed closed exchange

Source: Stacks 0D6F and 07A7, and the affine-local final step of
lem-sfb-proper-constructible-closed-exchange-heart.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w₁ w₂

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Choose the published structures so derived-functor arguments share the same data.
attribute [local instance 4000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  CategoryTheory.Mod.instAbelian
attribute [local instance 5000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  condensedAmbientExchange moduleObjectDerivedPushforward moduleObjectDerivedPullback
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor
  ClosedTestDerivedExchangeModel.pull ClosedTestDerivedExchangeModel.sectionsOver
  ClosedTestDerivedExchangeModel.exchange

end AlgebraicGeometry.ProEtale.CondensedRing
