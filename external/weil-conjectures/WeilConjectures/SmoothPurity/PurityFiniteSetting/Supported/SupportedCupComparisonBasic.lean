/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import all Mathlib.Logic.Small.Defs

set_option linter.privateModule false

/-! # Basic comparison for supported Hom classes

The three comparison bijections and the two coefficient-source squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupSingle functorialCupSourceObject functorialCupTarget
  functorialCupConstant functorialCupComparisonFunctor constant constantEtale

end WeilConjectures.PurityFiniteSetting
