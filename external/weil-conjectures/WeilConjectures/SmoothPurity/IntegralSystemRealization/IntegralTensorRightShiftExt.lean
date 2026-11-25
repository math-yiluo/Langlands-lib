/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorShiftProperties

/-! # Extensionality of normalized completed right shifts -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Equality of completed right-slot comparisons with the same representative normalization.
Source: Stacks 011G, 014E, 06YU, 0941; blueprint purity transport, Step 2
(blueprint: lem-pur-integral-tensor-right-shift-ext).

Proof: for each good pair, the finite generator formula determines the tower
comparison, since the pure tensors generate the sheafified tensor and the
summands generate totalization. The two prescribed cone coordinates determine
the cone map, so the induced shifted Roos comparisons are equal. Cancel the
input quotient-shift map and the good-model comparison in the normalization
equations. The components of the two natural isomorphisms are therefore equal
on every good pair. Every derived object is isomorphic to the localization of
a good complex. Naturality along these isomorphisms transports the component
equality to every derived pair. Extensionality of natural transformations and
of isomorphisms proves the asserted equality. -/
theorem integralTensorRightShift_ext (W : Scheme.{u}) (r : ℤ)
    (σ τ : completedTensorShiftSecond (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r)
    (hσ : integralCompletedTensorRightShiftProperty l E W r σ)
    (hτ : integralCompletedTensorRightShiftProperty l E W r τ) : σ = τ := by sorry

end WeilConjectures.IntegralSystemRealization
