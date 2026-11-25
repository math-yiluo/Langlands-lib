/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-!
# Compatibility predicates for the former coefficient model

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-pf-reduction`,
order 1881. These declarations retain their original meanings for existing consumers.
They do not define perfectness for condensed coefficients.
(blueprint: def-weil-legacy-site-perfect-compatibility).

## Main definitions

- `IsFiniteCoefficientSitePerfect`
- `IsIntegralCoefficientSitePerfect`
- `IsRationalCoefficientSitePerfect`
- `IsAlgebraicallyClosedCoefficientSitePerfect`
-/

@[expose] public section

set_option autoImplicit false

universe d t u v

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

end WeilConjectures
