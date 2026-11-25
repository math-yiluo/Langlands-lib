/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixNormalizedImmersion
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement

/-! # Normalized scalar comparison for locally closed immersions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 20000 in
-- This formal calculation should not unfold the concrete localization model.
set_option maxHeartbeats 20000 in
-- This formal calculation should not unfold the concrete localization model.
attribute [local irreducible] scalarSixChange scalarSixPull scalarSixTower
  scalarSixExtension scalarSixRestriction
  scalarSixImmersion
  scalarSixOpenIso scalarSixClosedIso scalarSixExtensionComp scalarSixPullSection
  Mod.derivedExtendMapDerivedCategoryAdjunction
  Mod.derivedExtendRestrictAdjunction Mod.extendScalars

end AlgebraicGeometry.ProEtale.CondensedRing
