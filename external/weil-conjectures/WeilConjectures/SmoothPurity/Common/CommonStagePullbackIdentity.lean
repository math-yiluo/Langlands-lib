/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.Rational.RationalCoefficientCategoryComparison
import WeilConjectures.SmoothPurity.Supporting.CoherentRationalPullbackIdentity

set_option linter.privateModule false

/-! # Identity comparison for common-stage pullback

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 099N.
(blueprint: lem-sf-common-stage-pullback-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] ScalarLocalization.category
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients

private theorem transport_heq {C : Type*} [Category C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  subst A'
  subst B'
  simpa using eq_of_heq h

end WeilConjectures
