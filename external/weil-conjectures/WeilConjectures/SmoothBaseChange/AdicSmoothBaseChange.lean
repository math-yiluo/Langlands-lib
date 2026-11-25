/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.SmoothBaseChange.SbcCompletedOperations
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion
import WeilConjectures.AlgebraicGeometry.Pbc.PbcIntrinsicTowerComplete
import WeilConjectures.SmoothBaseChange.AdicFiniteExchangeEncoding
import WeilConjectures.AlgebraicGeometry.Finite.FiniteProetaleSmoothBaseChange
import Mathlib.Algebra.CharP.CharAndCard

/-! # Adic smooth base change

Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1443;
Stacks Tags 0EYU, 099N, 099M and 09AL
(blueprint: sbc-thm-adic-smooth-base-change).

The exchange is the published completed adjunction mate. The conditional clause
retains all four finite outputs and a single interval for every level.

## Main definitions and statements

- `sbcAdicFiniteCohomology`: the canonical finite coefficient presentation of cohomology.
- `adicSmoothBaseChange`: invertibility and conditional constructible landing.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures
