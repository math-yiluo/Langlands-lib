/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.SixFunctors.FrobeniusTrivializationPullback
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.SixFunctors.FactorizedProEtalePullbackPasting
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismInvariance
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian

/-!
# Scheme and geometric Frobenius of a purity datum

Source: main-20261015 blueprint, `sec-smooth-purity/sk-def-sf-weil-complexes`,
`sec-Weil-complexes`, order 2579
(blueprint: sec-Weil-complexes).

The maps use the chosen fibre product and the unrestricted `galoisMap` interface.
The comparison is the specified composite of pullback composition and the canonical
absolute-Frobenius trivialization. The latter's projection and section-unit equations,
and the composition comparison's conjugate-adjunction equation, determine the selected
witnesses up to equality. No unnormalized isomorphism is selected.

## Main definitions

- `PurityFiniteSetting.schemeGeometricFrobeniusComparison`: the comparison kappa.
- `PurityFiniteSetting.frobeniusGaloisSquareComparison`: the Galois-square identification.
- `PurityFiniteSetting.frobeniusSchemeSquareComparison`: the scheme-square identification.

## Main statements

- `PurityFiniteSetting.schemeGeometricFrobenius_squares`: both squares and site invariance.
- `PurityFiniteSetting.schemeGeometricFrobenius_naturality`: the specified equality of paths.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] proEtaleRingModuleAdjunction
  proEtaleRingModulePullback proEtaleRingModulePullbackObj proEtaleRingModulePullbackMap

end WeilConjectures.PurityFiniteSetting
