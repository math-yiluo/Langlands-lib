/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenQuotientScalarComparisonAssembly

/-! # Existence of the strict scalar comparison for an open quotient

Source: Stacks Project, Tags 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-comparison-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- A normalized finite tensor comparison lifts to an isomorphism of strict scalar
quotient towers once scalar compatibility data are fixed.

The lift is obtained degreewise by composing the finite comparison with the finite
scalar restriction maps. Generator formulas make the components natural and preserve
all quotient transitions, so they assemble into the displayed strict-tower
isomorphism. This statement supplies only the comparison object; the scalar-adjunction
unit equation is a separate step.
Source: Stacks Tags 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-comparison-existence). -/
theorem openQuotientScalarComparisonExistence
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o) :
    Nonempty (ScalarComparison l E j o sc tc) := by
  obtain ⟨d⟩ := openQuotientScalarComparisonLevelData l E j o tc sc
  exact openQuotientScalarComparisonAssembly l E j o tc sc d

end WeilConjectures.OpenTensorQuotient
