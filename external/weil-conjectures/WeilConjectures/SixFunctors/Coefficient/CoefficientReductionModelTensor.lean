/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensor
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorDescent
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison

/-! # Tensor comparison from the strict K-flat reduction model

Source: Stacks 06YS, 06YY, 07A4 and 0941.
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

/-- The simultaneous strict K-flat reduction model is compatible with tensor,
for a left adjoint of the specified total limit, before choosing tensor maps.
Source: Stacks 07A4, lemma-pullback-tensor-product, and 0941.

Proof: use flat-term K-flat representatives for both arguments. The strict model
identifies reduction on these representatives with ordinary extension to the
sequence ring. Ordinary extension has a natural total-tensor comparison, obtained
by sheafifying the formula b tensor (x tensor y) maps to (b tensor x) tensor
(1 tensor y). Its inverse multiplies the two coefficient sections. These are
inverse maps on pure tensors, hence on the sheafified tensor and every total-degree
summand, with the same signs in the two differentials. Extension to the sequence
ring preserves K-flatness and flat terms: the tensor/restriction adjunction proves
the acyclic tensor test, and the ordinary tensor comparison proves termwise
flatness. Apply tensorComparisonDescent to the two prescribed tensor models and
the universal left-derived sequence extension counit. Flat-term K-flat resolutions
make restriction to representatives fully faithful, so this gives an isomorphism
on all derived objects. Identify the resulting sequence extension with L by
uniqueness of left adjoints
to coefficientSequenceLimit; the sequence projection theorem gives the adjunction
for the constructed extension. Conjugate its derived tensor comparison by this
natural isomorphism. No unit/counit projection equation or normalized-object
assertion is needed. The construction
uses no invertibility of quotient ring maps and treats zero and equal levels too.
(blueprint: lem-coef-reduction-model-tensor)
-/
theorem coefficientReductionModelTensor_exists
    (T : CoefficientDerivedSystemTensors l E W)
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W)
    (ρ : ∀ n : ℕ, L ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n)
    (_hL : CoefficientReductionModels l E W L ρ) :
    Nonempty (T.integralClosed.tensor ⋙ L ≅ L.prod L ⋙ T.systemClosed.tensor) := by
  obtain ⟨M⟩ := OrdinaryQuotient.ordinaryModel_exists l E W
  obtain ⟨b, -⟩ := OrdinaryQuotient.OrdinaryModel.quotientTensor_exists l E W M
  obtain ⟨ε, -, hε, -⟩ := OrdinaryQuotient.reductionComparison_exists l E W M L adj
  obtain ⟨μ, -⟩ := OrdinaryQuotient.reductionTensor_descent l E W M T L ε hε b
    (OrdinaryQuotient.OrdinaryModel.quotient_isKFlat l E W M)
  exact ⟨μ⟩

end WeilConjectures
