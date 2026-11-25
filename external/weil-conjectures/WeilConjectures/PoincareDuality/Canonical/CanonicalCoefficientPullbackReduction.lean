/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackModels
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientUnitNormalization
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientChainNormalization
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientFiniteCompatibility
public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure

/-!
# Canonical coefficient pullback and its finite quotient projections

Source: Stacks Tags 03D6 and 08TC; blueprint prop-cohomological-finiteness, Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).

The sectionwise inverse image used by the specified kappa is compared with the
normalized constant Weil structure through the actual regular-module coefficient
maps. Finite multiplication and projection from the strict Roos cone are retained
as morphisms, including their transition maps before localization. Level n means
positive exponent n+1 throughout.

## Main definitions

* `canonicalCoefficientKappa`: the recorded comparison on the regular good complex.
* `canonicalCoefficientLambda`, `canonicalCoefficientLambdaFinite`: the normalized
  integral comparison and finite multiplication, with coefficient-model transport.
* `canonicalCoefficientRho`: the actual quotient-cone projection and reduction.
* `canonicalCoefficientProjection`, `canonicalCoefficientInverseProjection`: the
  two coefficient projections in the same integral derived category.
* `canonicalCoefficientPullbackTransition`, `canonicalCoefficientInverseTransition`:
  the strict finite quotient transitions.

## Main statements

* `canonicalCoefficientModelMaps_isIso`: the regular coefficient identifications.
* `canonicalCoefficientPullbackReduction`: inverse and projection identities,
  strict transition compatibility, and the published constant-Weil normalization.
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
end WeilConjectures
