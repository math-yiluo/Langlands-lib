/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeSheafTensorCore
import WeilConjectures.Tactic.ExactModProofs

/-! # Specialization of the native sheaf tensor square -/

@[expose] public section

set_option Elab.async false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The inverse square is the adic square on the underlying carriers. -/
lemma condensedRealizationSheafTensor_inverse_square (M N : ProEtaleWeilSheaf k₀ l Y) :
    SheafPullTensorInverseSquare k₀ l g M N := by
  have h := projection_inverse_square_of_frobenius k₀ l _ _
    (nativePullSheafTensor k₀ l g) (by
      intro A B
      cast_proofs projection_nativePullSheafTensor_carrier_eq k₀ l g A B) M N
  dsimp only [SheafPullTensorInverseSquare, upperStar, condensedRealizationUpperStarIso]
  exact_mod_proofs h

/-- The native pullback tensor comparison and the condensed realization tensor comparison
commute with the pullback comparison. -/
lemma condensedRealizationSheafTensor_pull_square (M N : ProEtaleWeilSheaf k₀ l Y) :
    SheafPullTensorSquare k₀ l g M N :=
  sheafPullTensorSquare_of_inverse k₀ l g M N
    (condensedRealizationSheafTensor_inverse_square k₀ l g M N)

end AlgebraicGeometry.ProEtaleWeilSheaf
