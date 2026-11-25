/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.PurityRankOneLocalData
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Classical support boundaries and site comparison

Source: Milne, Lectures on Etale Cohomology, Section 14, Proposition 14.3,
and Section 16, Example 16.3; blueprint sk-prop-a1-kummer, Coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

attribute [local implicit_reducible]
  HomologicalComplex.homologyFunctor

open AlgebraicGeometry.ProEtale

end WeilConjectures.PurityFiniteSetting.RankOne
