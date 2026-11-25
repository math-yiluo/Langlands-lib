/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels
import WeilConjectures.SixFunctors.Supporting.FirstRootLinePullback
import WeilConjectures.SmoothPurity.Integral.IntegralRootPowerGenerators

/-! # Extensionality on positive root generators

Source: coefficient-twist conventions, first-line inverse image and scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

section PositiveRootLineConstruction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] PurCompactSupport.completed
  completedIntegralCommRingSheafUnrestricted

end PositiveRootLineConstruction

end WeilConjectures
