/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixOpenScalarRestriction
import WeilConjectures.SixFunctors.ScalarSixDefinitions

/-! # Normalized scalar comparisons for individual immersions

Source: blueprint latest, det-prop-scalar-six-pullback.proof.md, (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing
