/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModelExistence
import WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteQuotientCalculusExistence

/-! # Core normalized coefficient reduction witness

Source: Stacks 06YS, 06YY, 07A4, 07A6 and 0941
(blueprint: lem-coef-normalized-reduction-models-core).
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/--
The sequence projection and scalar-extension constructions produce the core reduction
record with its prescribed tensor subrecord and finite quotient calculus.  This is the
construction part of the normalized reduction argument; the four representative
normalization identities are recorded separately.
Source: Stacks 06YS, 06YY, 07A6 and 0941; the first and third proof steps of
`lem-coef-normalized-reduction-models`.

Proof plan: apply the sequence projection derived adjunction to the completed
coefficient ring and its quotient tower, transport it across the strict-system
sequence equivalence, and use the actual derived scalar-extension pairs at each
finite level.  The transported unit and counit give the projection equations and
one-flat-term K-flat models.  Apply the same change-of-rings construction to every
finite quotient and retain its ordinary unit, derived counit and tensor comparison;
these data form the finite quotient calculus.
(blueprint: lem-coef-normalized-reduction-models-core)
-/
theorem coefficientNormalizedReductionCore (T : CoefficientDerivedSystemTensors l E W) :
    ∃ R : CoefficientDerivedSystemReduction l E W,
      R.toCoefficientDerivedSystemTensors = T ∧
      Nonempty (CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) := by
  obtain ⟨R, hR⟩ := coefficientNormalizedReductionModel_exists l E W T
  obtain ⟨Q⟩ := coefficientFiniteQuotientCalculus_exists l E W T
  exact ⟨R, hR, ⟨hR.symm ▸ Q⟩⟩

end WeilConjectures
