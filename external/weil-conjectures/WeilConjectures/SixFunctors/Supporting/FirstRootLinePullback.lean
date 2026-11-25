/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement

/-! # Root-normalized first-line inverse image

Source: coefficient-twist conventions, first-line inverse image and scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
set_option synthInstance.maxSize 2048
attribute [local irreducible] AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.purTwistZlOne
  AlgebraicGeometry.Scheme.proEtaleRootsOfUnityTower
  WeilConjectures.PurCompactSupport.completed
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

end WeilConjectures
