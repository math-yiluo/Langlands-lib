/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.CoefficientStrictReductionTensorComparison

/-! # Strict representative tensor comparison for reduction

Source: Stacks 06YS, 06YY, 07A4 and 0941.
(blueprint: lem-coef-strict-reduction-tensor-normalization).
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

/-- Reduction admits a tensor comparison computed by a single strict chain map.
Source: Stacks 07A4, proof of lemma-pullback-tensor-product, with the sequence
projection construction of 0941 and the K-flat resolution of 06YS.
Proof: first choose the strict comparison supplied by the sequence projection,
then apply its simultaneous representative normalization on arbitrary flat-term
K-flat inputs. This gives precisely the defining clauses of the conclusion.
(blueprint: lem-coef-strict-reduction-tensor-normalization). -/
theorem coefficientStrictReductionTensorNormalization
    (R : CoefficientDerivedSystemReduction l E W) :
    ∃ μ : R.integralClosed.tensor ⋙ R.reduction ≅
      R.reduction.prod R.reduction ⋙ R.systemClosed.tensor,
      CoefficientReductionTensorNormalization l E W { R with reductionTensor := μ } := by
  exact coefficientStrictReductionTensorNormalization_of l E W R

end WeilConjectures
