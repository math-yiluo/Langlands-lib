/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Karoubian

/-!
# The Weil category is idempotent complete

In the notation of `definition-weil-structure`, the common-stage Weil category is idempotent
complete and the canonical functor into its Karoubi envelope is an exact equivalence
(`AlgebraicGeometry.WeilComplex.isIdempotentComplete`,
`AlgebraicGeometry.WeilComplex.isEquivalence_toKaroubi_and_isTriangulated`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- Pointer to the properties of the Weil category.

In the notation of `definition-weil-structure`, the common-stage Weil category
`D^b_{c,W}(Y, ℚ̄_ℓ)` (`AlgebraicGeometry.WeilComplex`) is idempotent complete, and the canonical
functor into its Karoubi envelope is an exact equivalence. -/
theorem isIdempotentComplete_and_isEquivalence_toKaroubi :
    IsIdempotentComplete (WeilComplex k₀ l Y) ∧
      (Idempotents.toKaroubi (WeilComplex k₀ l Y)).IsEquivalence ∧
      (Idempotents.toKaroubi (WeilComplex k₀ l Y)).IsTriangulated :=
  ⟨inferInstance, isEquivalence_toKaroubi_and_isTriangulated k₀ l Y⟩

end AlgebraicGeometry.WeilComplex
