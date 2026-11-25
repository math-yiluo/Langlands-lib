/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackModels
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackModels
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure

set_option linter.privateModule false

/-!
# The unit and Roos augmentation for canonical coefficient pullback

Source: Stacks Tags 03D6 and 08TC; the regular-unit and Roos APIs in
`WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure`.
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).

This module contains proved comparison results and private helpers for the coefficient comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] regularExtensionIso regularExtensionPresheafIso
  identityRestrictionIso scalarReductionExistence HasDerivedCategory.standard
  unrestrictedIntegralReductionExistence limit finiteRegularIso finiteSingleRegularIso
  finitePullbackRegularIso pullbackLevelRegularIso pullbackUnitLevel chainUnitCandidate
  integralDerivedPullback integralDerivedPullbackComparison
  constantWeilIntegralRoosComparison
  constantWeilIntegralLambda constantWeilDerivedCoefficientComparison
  SheafOfModules.monoidalCategory constantSheaf
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] canonicalCoefficientIntegralComparison
  canonicalCoefficientInverseImageTransport
  canonicalCoefficientLambda canonicalCoefficientKappa canonicalCoefficientLambdaFinite
  canonicalCoefficientFiniteComparison canonicalCoefficientPullbackReductionIso
  canonicalCoefficientRho canonicalCoefficientProjection canonicalCoefficientInverseProjection
  canonicalCoefficientTheta canonicalCoefficientPullbackTransition canonicalCoefficientTransition
  canonicalCoefficientInverseTransition

attribute [local irreducible] canonicalCoefficientIntegralUnit
  canonicalCoefficientFiniteUnit canonicalCoefficientFiniteKappaComplex
  coefficientFiniteInverseIso coefficientFinitePullIso

private theorem coefficientReductionComplex_eq (W : Scheme.{u}) (n : ℕ) :
    canonicalCoefficientReductionComplex l E W n = (finiteSingleRegularIso l E W n).hom := by
  unfold canonicalCoefficientReductionComplex finiteSingleRegularIso
  rw [coefficientReduction_eq]
  rfl

end WeilConjectures
