/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralCoherenceData
import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralStrictPullbackComparisons
import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralGoodQuotientPresentation
import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralStrictExpressionRealization

/-! # Strict expression models before derived inverse limit

Source: Stacks 07A4 and 0941; integral coherence, strict-model step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] SheafOfModules.monoidalCategory

universe t u s i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} {W : S → Scheme.{t}}

end WeilConjectures.IntegralCoherence
