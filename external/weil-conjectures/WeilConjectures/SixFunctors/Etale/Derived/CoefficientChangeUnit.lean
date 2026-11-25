/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitRefinement

/-!
# Coefficient comparisons, units of derived adjunctions and the exchange maps

Let `ρ : Λ →+* Λ'` be a morphism of coefficient rings. The coefficient comparison
`Res ⋙ Rf_* ≅ Rf_* ⋙ Res` of the unbounded derived direct image is the mate of the coefficient
comparison of the derived pullback, both for `Lf^* ⊣ Rf_*` and for `D(f^*) ⊣ Rf_*`
(`WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar`). Consequently:

- the derived base change map `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is compatible with the
  coefficient comparisons (`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_restrictScalars`);
- for finite `Λ`, the comparison of derived lower shrieks along a refinement of
  compactifications is compatible with the coefficient comparisons, see
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison_app_restrictScalars`.
-/
