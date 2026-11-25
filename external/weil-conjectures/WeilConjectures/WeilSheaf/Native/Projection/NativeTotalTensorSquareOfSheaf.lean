/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorCore
import WeilConjectures.Tactic.ExactModProofs

/-! # The totalized native pullback tensor square -/

@[expose] public noncomputable section

set_option Elab.async false

-- Match the coefficient-category instance used by the total comparison.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

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

variable (hsheaf : ∀ M N : ProEtaleWeilSheaf k₀ l Y, SheafPullTensorSquare k₀ l g M N)

include hsheaf in
/-- Equality of the two total-complex tensor squares, checked on each tensor summand. -/
lemma condensedRealizationTotalTensor_pull_square_of_sheaf
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) :
    TotalPullTensorSquare k₀ l g P T := by
  have : (upperStar k₀ l g).IsLeftAdjoint := (upperStarLowerStarAdjunction k₀ l g).isLeftAdjoint
  have h := projection_totalTensorSquare_of_sheaf k₀ l _ _
    (nativePullSheafTensor k₀ l g) (nativePullTotalTensor k₀ l g)
    (condensedRealizationUpperStarIso k₀ l g)
    (by cast_proofs nativePullTotalTensor_summands k₀ l g)
    (by
      intro M N
      have hs := hsheaf M N
      dsimp only [SheafPullTensorSquare] at hs
      exact_mod_proofs hs) P T
  dsimp only [ProjectionTotalTensorSquare] at h
  dsimp only [TotalPullTensorSquare, condensedRealizationPullComplexIso]
  exact_mod_proofs h

end AlgebraicGeometry.ProEtaleWeilSheaf
