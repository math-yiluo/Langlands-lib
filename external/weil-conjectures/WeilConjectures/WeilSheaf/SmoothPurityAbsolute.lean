/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityAbsoluteDescent
public import WeilConjectures.WeilSheaf.SmoothPurityNativeTateDescent

/-! # Absolute smooth purity for native Weil complexes -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The right adjoint of compactly supported image to the finite field carries the
constant object to the shifted Tate object on a smooth scheme. -/
theorem purity_nonempty_shriekRightAdjoint_adicConstant_iso
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    {R : WeilComplex k₀ ℓ (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ ℓ X}
    (adj : derivedLowerShriek k₀ ℓ (X ↘ Spec (CommRingCat.of k₀)) ⊣ R) :
    Nonempty (R.obj (WeilSheaf.toComplex.obj
        (WeilSheaf.adicConstant k₀ ℓ (Spec (CommRingCat.of k₀)))) ≅
      ((tateTwist k₀ ℓ X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ ℓ X)))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨e⟩ := WeilSheaf.purity_nonempty_toCondensedTateDescentIso k₀ ℓ X d
  exact nonempty_shriekRightAdjoint_adicConstant_iso_of_tate_encoding d e adj

end AlgebraicGeometry.WeilComplex
