/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityThomDescent
public import WeilConjectures.WeilSheaf.SmoothPurityNativeTateDescent

/-! # The trivial-line Thom isomorphism from absolute Tate purity -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)]

/-- Absolute purity and compact projection give the trivial-line Thom functor. -/
theorem purity_nonempty_trivialLineThom
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (s : Y ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (upperStar π ⋙ derivedLowerShriek k₀ ℓ π ≅
      tateTwist k₀ ℓ X (-1) ⋙ shiftFunctor _ (-2 : ℤ)) := by
  obtain ⟨e⟩ := WeilSheaf.purity_nonempty_toCondensedTateDescentIso k₀ ℓ (affineLine k₀) 1
  exact nonempty_trivialLineThom_of_tate_encoding e π s hπ

end AlgebraicGeometry.WeilComplex
