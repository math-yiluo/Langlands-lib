/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
public import WeilConjectures.SixFunctors.Supporting.PurSequenceAdjointResolutionShifts

/-! # Resolution-normalized sequence-site adjoints

Source: blueprint main-20261015, `sec-six-functors/sk-thm-sf-package/`
`fix-prop-coherence.proof.md`, coefficient-comparison sentence; Stacks 0940,
0941, 03D7, 06YY, 07A6 and 0D6E
(blueprint: def-sf-sequence-adjoint-shift-interfaces).

The constructions of this node are the published declarations of
`WeilConjectures.SixFunctors.Supporting.PurSequenceAdjointResolutionShifts`, reexported here
unchanged:
`purSequenceShiftedReplacement` (the ordinary shift comparison followed by the shifted given
replacement map), the left and right shift models `PurSequenceLeftShiftModels` and
`PurSequenceRightShiftModels` (coherent integer shifts, reduction and total-limit comparison
squares, shifted quasi-isomorphism and signed degreewise equations), the predicates
`purSequenceRightResolutionCompatibility` and `purSequenceShiftedDegreeCompatibility`, and the
record `PurSequenceAdjointShifts` with the shift compatibility of the same unit and counit.
They are not redeclared, so that one definition per notion is kept.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

end WeilConjectures
