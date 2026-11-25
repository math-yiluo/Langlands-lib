/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! # Generic coefficient-domain pullback calculus

The generic statement shares coefficient-category instances before finite specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures
attribute [local instance 2000] CommRing.toRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  Etale.upperStar ProEtale.pbcFixedScalarExtension Etale.scalarExtensionRepresentative
  Etale.scalarSheafPullbackComplexIso Etale.scalarGeometricRepresentative

end WeilConjectures
