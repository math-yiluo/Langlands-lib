/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeMaps
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance 4000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  CategoryTheory.Mod.instAbelian
attribute [local instance 5000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  condensedAmbientExchange moduleObjectDerivedPushforward moduleObjectDerivedPullback
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ClosedTestDerivedExchangeModel.pull ClosedTestDerivedExchangeModel.exchange

end AlgebraicGeometry.ProEtale.CondensedRing
