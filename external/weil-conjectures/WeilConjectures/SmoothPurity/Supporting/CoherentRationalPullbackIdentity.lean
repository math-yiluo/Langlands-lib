/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.Rational.RationalCoefficientCategoryComparison

set_option linter.privateModule false

/-! # Scalar-compatible identity maps before common-stage descent

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 099N.
(blueprint: lem-sf-coherent-rational-pullback-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 10000
universe u v
open CategoryTheory AlgebraicGeometry TensorProduct
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients

section Rationalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
private theorem transport_heq {C : Type*} [Category C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  subst A'
  subst B'
  simpa using eq_of_heq h
private theorem map_heq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'}
    (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst A'
  subst B'
  cases h
  rfl

variable (L : Type u) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

end Rationalization


end WeilConjectures
