/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Scalar multiplication of common-stage pullback representatives

Source: the Weil-structures paragraph of the all-stage open/closed triangle proof.
The finite-stage scalar identity is transported through the actual representative map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  constructibleIntegralPullback integralDerivedPullback
  rationalDerivedPullback commonStageDerivedPullback
  GeneralAlgebraicallyClosedCoefficients.ofHom StageSystem.PairCategory.mkHom

attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] sfIntegralConstructibleLinear

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive

end WeilConjectures
