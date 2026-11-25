/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionCore
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionNormalizations

/-! # Normalized coefficient reduction and quotient tensors

Source: Stacks 06YS, 06YY, 07A4, 07A6 and 0941
(blueprint: lem-coef-normalized-reduction-models).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The three tensor models retain the ordinary associator, unit and symmetry formulas.
These are the coherence witnesses of the existing ringed-site tensor theorem.
Source: Stacks 0FPT, 07A4 and 08J9
(blueprint: lem-coef-normalized-reduction-models). -/
def CoefficientDerivedSystemTensorCoherence (T : CoefficientDerivedSystemTensors l E W) :
    Prop :=
  (∃ β : @SymmetricCategory (DerivedCategory (scalarReductionSource l E W))
      _ T.integralClosed.monoidal,
    Nonempty (RingedDerivedTensorCoherence.{t+1, t, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      T.integralClosed T.integralTensorModel β)) ∧
  (∃ β : @SymmetricCategory (coefficientSequenceDerived l E W) _ T.systemClosed.monoidal,
    Nonempty (RingedDerivedTensorCoherence.{t+1, t, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) T.systemClosed T.systemTensorModel β)) ∧
  ∀ n : ℕ, ∃ β : @SymmetricCategory (normalizedDVRDerived l E W n)
      _ (T.finiteClosed n).monoidal,
    Nonempty (RingedDerivedTensorCoherence.{t+1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) (T.finiteClosed n) (T.finiteTensorModel n) β)

attribute [local irreducible] CoefficientDerivedSystemTensorCoherence

/-- Reduction with its normalized tensor comparisons, before internal Hom or sections.
Source: Stacks, sites-cohomology.tex, Tags 06YS, 06YY, 07A4, 07A6 and 0941;
resolution-model construction, steps 1--2
(blueprint: lem-coef-normalized-reduction-models).

Proof:
Apply SequenceProjection.pushforwardLimitProjections to the completed coefficient
ring and its finite quotient tower. Its ordinary pullback has components B_n tensor M
and its pushforward is the limit of the exact scalar-restricted tower. Identify the
strict systems with sequence-site modules using strictSystemSequenceEquivalence.
The universal right-derived comparison identifies its right adjoint with the specified
coefficientSequenceLimit, preserving the actual limit projections. Transport the
adjunction, giving the displayed unit and counit projection equations. Its left-derived
comparison on one flat-term K-flat complex gives reductionModel and the strict
horizontal quotient maps. Finite evaluation identifies reduction with the prescribed
finite scalar-extension functor by uniqueness of the normalized left-derived pair.
For the given tensor models, canonical tensor pullback supplies reductionTensor,
finiteTensor and evaluationTensor. On simultaneous K-flat representatives their maps
are ordinary pure-tensor maps. The uniquely specified coefficientScalarTensorIso and
coefficientEvaluationTensorIso therefore give all three representative normalization
squares; evaluating the strict reduction square gives reductionTensor_evaluation.
Iterated scalar extension B_n tensor over B_m (B_m tensor over A P) is canonically
B_n tensor over A P. Its associativity isomorphism is the actual transition adjunct,
so every reduction is normalized. Apply the same scalar-extension construction to
B_m to B_n. Retain its ordinary unit 1 tensor x and its localized derived counit,
and the pure-tensor comparison on every pair of K-flat complexes, to obtain Q.
The tensor models are retained verbatim: the first equality records this fact.
No internal-Hom fiber, global sections, or total-sections comparison is asserted. -/
theorem coefficientNormalizedReductionModels (T : CoefficientDerivedSystemTensors l E W) :
    ∃ R : CoefficientDerivedSystemReduction l E W,
      R.toCoefficientDerivedSystemTensors = T ∧
      CoefficientReductionTensorNormalization l E W R ∧
      CoefficientFiniteTensorNormalization l E W R ∧
      CoefficientEvaluationTensorNormalization l E W R ∧
      CoefficientReductionTensorEvaluation l E W R ∧
      Nonempty (CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) :=
  by
  obtain ⟨R, hRT, hQ⟩ := coefficientNormalizedReductionCore l E W T
  obtain ⟨S, hSR, hR, hF, hE, hRE⟩ :=
    coefficientNormalizedReductionNormalizations l E W R
  have hST : S.toCoefficientDerivedSystemTensors = R.toCoefficientDerivedSystemTensors :=
    congrArg CoefficientDerivedSystemReductionModel.toCoefficientDerivedSystemTensors hSR
  exact ⟨S, hST.trans hRT, hR, hF, hE, hRE, hST.symm ▸ hQ⟩

end WeilConjectures
