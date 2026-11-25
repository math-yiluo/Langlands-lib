/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

/-!
# Linearity of the comparison functors

For a coefficient category `A` which is `Λ`-linear, the restriction
`ν_* : Sh(X_proét, A) ⥤ Sh(X_ét, A)` is `Λ`-linear, being computed objectwise, and so is its left
adjoint `ν^*` (`AlgebraicGeometry.ProEtale.linear_comparisonUpperStar`). For instance, for a
commutative ring `R`, `ν^*` is `R`-linear on sheaves of `R`-modules.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type*) [Ring Λ] [Linear Λ A] (X : Scheme.{u})

/-- The restriction `ν_*` on sheaves with values in a `Λ`-linear category is `Λ`-linear: it acts
on morphisms by whiskering. -/
instance linear_comparisonLowerStar : ν_*(X)[A].Linear Λ where

/-- The comparison functor `ν^*` on sheaves with values in a `Λ`-linear category is `Λ`-linear,
being left adjoint to the `Λ`-linear restriction `ν_*`. -/
instance linear_comparisonUpperStar : ν^*(X)[A].Linear Λ :=
  (comparisonAdjunction A X).left_adjoint_linear

end AlgebraicGeometry.ProEtale
