/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitFoundations
import all WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Effectivity of the specified native compact-support tower

Source: Stacks Tags 0940 and 0941; normalized DVR effectivity applied to the
actual proper/open coefficient sequence.
(blueprint: lem-pur-compact-support-native-effectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.PurStrictScalar

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard

end WeilConjectures.PurStrictScalar
