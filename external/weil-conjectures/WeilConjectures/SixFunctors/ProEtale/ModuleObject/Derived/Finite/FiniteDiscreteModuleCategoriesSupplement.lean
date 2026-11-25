/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteModuleCategories

/-! # Categories for finite discrete coefficients, before bounded constructibility

These are the unchanged ordinary internal module and module-valued sheaf categories.
(blueprint: def-sfb-finite-discrete-module-categories)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- The bounded below etale category for these coefficients. -/
abbrev FiniteDiscreteEtalePlus (T : Scheme.{u}) :=
  DerivedCategory.Plus (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} B)))

variable (T : Scheme.{u})
  (E : FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T)

end AlgebraicGeometry.ProEtale.CondensedRing
