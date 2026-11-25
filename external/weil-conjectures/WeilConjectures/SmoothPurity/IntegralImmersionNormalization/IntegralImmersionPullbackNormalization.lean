/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralImmersionNormalization.IntegralImmersionPullbackNormalizationData
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.IntegralImmersionNormalization.IntegralImmersionCoefficientLinearity
import WeilConjectures.SmoothPurity.IntegralImmersionNormalization.IntegralImmersionShiftCompatibility
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.CharP.CharAndCard

/-! # Assembly of normalized integral immersion pullbacks

The normalized coefficient presentations and comparison clauses are reexported from
`IntegralImmersionPullbackNormalizationData`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.IntegralImmersionNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures.IntegralImmersionNormalization
