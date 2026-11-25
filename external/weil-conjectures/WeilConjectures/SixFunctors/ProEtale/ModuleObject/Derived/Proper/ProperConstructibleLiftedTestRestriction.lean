/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper rigidity on a single closed lifted test

Source: degree-zero closed-test calculation of compactification coherence, paragraph (2).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  moduleObjectDerivedPushforward moduleObjectDerivedPullback
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ClosedTestDerivedExchangeModel.pull ClosedTestDerivedExchangeModel.sectionsOver
  ClosedTestDerivedExchangeModel.exchange

end AlgebraicGeometry.ProEtale.CondensedRing
