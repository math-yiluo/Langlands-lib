/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensor
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryStrictTensorNormalization

/-! # Strict reduction tensor comparison and its representative normalization

Source: Stacks 06YS, 06YY, 07A4 and 0941.
(blueprint: lem-coef-strict-reduction-tensor-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The strict reduction comparison supplied by the strict pullback construction
has the simultaneous representative normalization square. The finite projections
are the prescribed scalar tensor maps on every flat-term K-flat pair.
The comparison is asserted to exist, not quantified over: an arbitrary comparison
need not be normalized (its negative has the same type but not the square).
Source: Stacks 06YS, 06YY, 07A4 and 0941, representative tensor descent.
(blueprint: lem-coef-strict-reduction-tensor-normalization-fixed). -/
theorem coefficientStrictReductionTensorNormalization_of
    (R : CoefficientDerivedSystemReduction l E W) :
    ∃ μ : R.integralClosed.tensor ⋙ R.reduction ≅
      R.reduction.prod R.reduction ⋙ R.systemClosed.tensor,
      CoefficientReductionTensorNormalization l E W { R with reductionTensor := μ } := by
  obtain ⟨M⟩ := OrdinaryQuotient.ordinaryModel_exists l E W
  obtain ⟨b, hb⟩ := OrdinaryQuotient.OrdinaryModel.quotientTensor_exists l E W M
  refine OrdinaryQuotient.reductionTensorNormalization_of_quotientTensor l E W M R b
    (fun n P Q ↦ ?_) (OrdinaryQuotient.OrdinaryModel.quotient_isKFlat l E W M)
  have h := hb n P Q
  unfold CoefficientComparisonEquation at h
  exact h

end WeilConjectures
