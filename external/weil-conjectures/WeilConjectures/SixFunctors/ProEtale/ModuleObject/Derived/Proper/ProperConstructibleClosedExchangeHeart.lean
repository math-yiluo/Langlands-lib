/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperConstructibleLiftedTestRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedExchangeAffineDescent
import WeilConjectures.AlgebraicGeometry.ClosedLiftedTestIsomorphismCriterion.ClosedLiftedTestIsomorphismCriterion
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantStratifiedZariskiLocality

/-! # Proper closed exchange for constructible sheaves in degree zero

Source: blueprint latest, compactification coherence, refinement (2), closed-complement
calculation. This is the sheaf case of the closed lifted-test argument; no Tor bound
is imposed on the sheaf (blueprint: lem-sfb-proper-constructible-closed-exchange-heart).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  condensedAmbientExchange moduleObjectDerivedPushforward moduleObjectDerivedPullback
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ClosedTestDerivedExchangeModel.pull ClosedTestDerivedExchangeModel.sectionsOver
  ClosedTestDerivedExchangeModel.exchange ClosedTestDerivedExchangeModel.testRestriction

end AlgebraicGeometry.ProEtale.CondensedRing
