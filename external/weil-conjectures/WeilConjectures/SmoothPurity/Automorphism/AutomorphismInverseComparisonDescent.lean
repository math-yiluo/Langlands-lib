/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.DeligneLaumon.IsomorphismFieldTransport
import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
import WeilConjectures.PoincareDuality.PullbackIdentitiesScalarExtension

/-! # Normalized inverse comparisons at integral and field coefficient stages

This is the independently compiled inverse-comparison argument from the automorphism
stage-equivalence node, retaining its actual integral, rational and pair components.
(blueprint: lem-sf-automorphism-inverse-comparison-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] constructibleIntegralPullback
attribute [local irreducible] HasDerivedCategory.standard integralDerivedPullback
  integralComparisonComposition integralComparisonUnit AlgebraicGeometry.Scheme.residueField
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

end WeilConjectures
