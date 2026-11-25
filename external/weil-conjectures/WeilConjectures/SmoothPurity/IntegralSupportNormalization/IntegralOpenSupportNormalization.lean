/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.IntegralSupportNormalization.IntegralSupportNormalizationData
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportFiniteComparison
import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralOpenAdjunctionTransposeNormalization
import all WeilConjectures.SmoothPurity.Sf.SfIntegralCompactSupportConstructible
import all WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulCompleteness
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenDvrRingedIdentification

import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization

/-! # Open support comparison and strict-system adjunction maps

Source: smooth-purity localization support paragraphs; Stacks 03DI, 0GL1, 0A07
(blueprint: lem-sf-open-support-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures.IntegralSupportNormalization
