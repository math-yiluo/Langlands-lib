/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarPullbackStrictConeData
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

set_option linter.privateModule false

/-! # Unique derived descent of a supplied scalar pullback chain map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] integralOperationsGoodLocalization
  integralOperationsPullbackOnGood
attribute [local instance 5000] integralTowerHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u, t, t + 1} _

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} W

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

end WeilConjectures
