/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitFoundations
import all WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import WeilConjectures.SixFunctors.Compact.CompactSupportInputTowerCompatibility
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition

/-! # Normalized realization of a specified native support tower

Source: Stacks Tags 0940 and 0941; the native realization construction in
compactSupport_normalized_realization, applied to the supplied reduction calculus.
(blueprint: lem-pur-compact-support-native-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard constantSheaf Padic.coefficientExtensionIdeal
  coefficientSequenceEvaluation coefficientSequenceTransition
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence Functor.objPreimage Functor.objObjPreimageIso

end WeilConjectures
