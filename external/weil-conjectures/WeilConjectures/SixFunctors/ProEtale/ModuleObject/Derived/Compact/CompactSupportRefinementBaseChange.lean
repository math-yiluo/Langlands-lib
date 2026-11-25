/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportOpenRefinementPasting
import WeilConjectures.AlgebraicGeometry.Compactification.DenseRefinementMorphisms

/-!
# Pasting compact-support exchange with dense refinements

Source: blueprint proposition-composition-base-change-rf-shriek--4, proof steps 4--7.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.rightDerivedFunctor Functor.mapDerivedCategory Functor.leftDerivedFunctor
  derivedUpperStarLowerStarAdjunction derivedOpenImmersionLowerShriekUpperStarAdjunction
  refinementDerivedLowerStarComp
  leftDerivedUpperStarIsoMapDerivedCategory upperStarLowerStarAdjunction
  condensedAmbientPullbackComparison AlgebraicGeometry.ProEtale.upperStarFromPoint
  Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct
  Sheaf.monoidalCategory DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] compactificationRefinementComponent
  detSfCompactSupportBaseChangeComposite detSfCompactSupportExchangeData
  condensedAmbientExchange detSfOpenBaseChangeMap localizingRefinementMap refinementTheta
  compactSupportPushforwardTriangle compactSupportTrianglePullbackSquare
  compactSupportTrianglePullback detSfProperBaseChangeSquare
  instCategoryDerivedCategory MorphismProperty.instCategoryLocalization

-- Keep the mate abstract so component conversions do not unfold its adjunction data.
end AlgebraicGeometry.ProEtale.CondensedRing
