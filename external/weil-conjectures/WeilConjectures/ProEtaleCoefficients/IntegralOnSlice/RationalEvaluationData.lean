/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.Algebra.Module.TransferInstance

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses

public import WeilConjectures.CategoryTheory.RingedSiteModules

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization

/-!
# Integral and rational evaluation data on slices

Source: Weil blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality,
first proof paragraph, exact functors and preservation of direct summands
(blueprint: lem-sf-rational-thick-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite
namespace WeilConjectures.IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t}) (U : Option X.ProEt)

set_option linter.unusedVariables false in
/-- The coefficient sheaf in degree zero. Source: Stacks 08JD
(blueprint: lem-sf-rational-thick-evaluation). -/
def coefficient : D l E X U := ringedSiteDualityUnit (topology X U) (ring l E X U)

end WeilConjectures.IntegralOnSlice
