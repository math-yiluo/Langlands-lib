/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Perfect complexes on the coefficient site

Source: current Weil conjectures blueprint, `chap-Smooth-purity`,
`sk-lem-sp-tower/def-weil-site-perfect-complex.md`, order 2959
(blueprint: def-weil-site-perfect-complex).

The same definition applies to every commutative condensed coefficient ring, including
finite discrete coefficients, integral and rational coefficients, and the finite-subextension
condensed algebraic closure. Restriction is the exact module pullback applied termwise.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
