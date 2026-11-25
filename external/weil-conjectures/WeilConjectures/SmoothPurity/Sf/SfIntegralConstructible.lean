/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The integral bounded constructible predicate over arbitrary base fields

Source: Weil blueprint, order 1459
(blueprint: def-weil-derived-complete-integral-detailed).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The same integral constructible category: completeness and constructible reductions
with one common finite cohomological interval. No finite-field datum enters this notion.
Source: Weil blueprint, order 1459
(blueprint: def-weil-derived-complete-integral-detailed). -/
noncomputable def sfIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty (DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
  fun K ↦ IsSfDerivedComplete l E X K ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) X
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) ∧
        proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) ⊆ Set.Icc a b

/-- The full subcategory of bounded constructible derived-complete integral objects.
Source: Weil blueprint, order 1459
(blueprint: def-weil-derived-complete-integral-detailed). -/
noncomputable abbrev sfIntegralConstructibleCategory (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{u}) :=
  (sfIntegralConstructible l E X).FullSubcategory

end WeilConjectures
