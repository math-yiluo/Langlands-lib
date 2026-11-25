/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.WeilFourierTransform
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
public import WeilConjectures.WeilSheaf.TateTwist

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

noncomputable section

variable (k₀ : Type u) [Field k₀] [Finite k₀]
  (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (n : Type u) [Fintype n]

abbrev affineFourierBase := Spec (CommRingCat.of k₀)
abbrev affineFourierV := AffineSpace n (affineFourierBase k₀)
abbrev affineFourierPlane :=
  pullback (affineFourierV k₀ n ↘ affineFourierBase k₀)
    (affineFourierV k₀ n ↘ affineFourierBase k₀)
abbrev affineFourierTriple :=
  pullback (pullback.snd (affineFourierV k₀ n ↘ affineFourierBase k₀)
      (affineFourierV k₀ n ↘ affineFourierBase k₀))
    (pullback.fst (affineFourierV k₀ n ↘ affineFourierBase k₀)
      (affineFourierV k₀ n ↘ affineFourierBase k₀))
abbrev affineFourierR₁₂ : affineFourierTriple k₀ n ⟶ affineFourierPlane k₀ n :=
  pullback.fst _ _
abbrev affineFourierR₂₃ : affineFourierTriple k₀ n ⟶ affineFourierPlane k₀ n :=
  pullback.snd _ _
abbrev affineFourierDiagonal : affineFourierV k₀ n ⟶ affineFourierPlane k₀ n :=
  pullback.diagonal (affineFourierV k₀ n ↘ affineFourierBase k₀)

end

end AlgebraicGeometry.WeilComplex
