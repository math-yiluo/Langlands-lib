/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.PurityRankOneLocalData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.RankOneFiniteKummerCohomology
import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.RankOneKummerMonomial
import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.RankOneClassicalSupportComparison
import WeilConjectures.AlgebraicGeometry.AffineSpace.PuncturedLine
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-! # The finite rank-one Kummer residue

Source: Milne, Lectures on Etale Cohomology, Sections 9, 14 and 16;
(blueprint: example-closed-support).
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

end WeilConjectures.PurityFiniteSetting.RankOne
