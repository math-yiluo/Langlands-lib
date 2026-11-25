/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity

/-! # Canonical integral reduction adjunction and quotient transitions

Source: Weil conjectures blueprint, order 2132, coherent coefficient comparisons;
main-20261015, thm-pur-adic-reconstruction, normalized-system transitions.
(blueprint: def-pur-integral-reduction-transitions).

The two constructions of this node are the published declarations
`normalizedDVRIntegralAdjunction` (the tensor-unit-normalized derived adjunction
`L_n ⊣ Res_n`, the `.choose` of the published normalized adjunction) and
`normalizedDVRReductionTransition` (the inverse Hom-adjunction image under `𝔞_m` of
`η_n` followed by the inverse restriction comparison `e_{m,n}⁻¹`) of
`WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity`, reexported here unchanged.
They are not redeclared, so that one definition per notion is kept.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

end WeilConjectures
