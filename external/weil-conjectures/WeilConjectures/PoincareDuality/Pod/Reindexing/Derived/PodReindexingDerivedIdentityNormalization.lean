/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

set_option linter.privateModule false

/-! # Derived identity normalization

Source: blueprint dual-Tate compatibility, Step 6; localization universal property
(blueprint: lem-pod-reindexing-derived-identity-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derived_eqToIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    Functor.mapDerivedCategoryNatIso (eqToIso h) =
      eqToIso (by cases h; rfl) := by
  subst h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

end WeilConjectures
