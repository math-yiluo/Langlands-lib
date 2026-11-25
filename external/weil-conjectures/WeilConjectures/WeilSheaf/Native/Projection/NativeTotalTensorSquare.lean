/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeSheafTensorSquare
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorSquareOfSheaf

/-! # The totalized native pullback tensor square -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The native tensor square commutes after totalization. -/
lemma condensedRealizationTotalTensor_pull_square
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) :
    TotalPullTensorSquare k₀ l g P T :=
  condensedRealizationTotalTensor_pull_square_of_sheaf k₀ l g
    (condensedRealizationSheafTensor_pull_square k₀ l g) P T

end AlgebraicGeometry.ProEtaleWeilSheaf
