/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemGammaProjectionTransport
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemHomProjectionTransport

/-! # Actual finite projections of coefficient gamma

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08JA, 0D6E and 0941;
the evaluated enriched projection formula and its normalized degree-zero calculation
(blueprint: lem-coef-derived-system-projection-formulas).
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

/-- Gamma has the actual finite mapping-limit projections and the specified H-zero action.
This is an identity for any calculus with the two recorded projection-model equations,
rather than a new choice
of a mapping equivalence or a construction of the calculus itself.
Source: Stacks 07A6, 08JA, 0D6E, 0941; the proved
SheafOfModules.EnrichedSequenceProjection.enrichedSequenceProjectionFormula;
node lem-coef-derived-system-evaluation-calculus, step 5, final projection calculation
(blueprint: lem-coef-derived-system-projection-formulas).

Proof:
1. Use the actual quotient ring sequence, completed coefficient sheaf and the strict
   system equivalence. Transport the calculus's reduction adjunction, finite evaluations,
   tensors, internal-Hom fibers and sections comparisons to the generic sequence-site
   notation of EnrichedSequenceProjection. The pure-tensor model normalizations identify
   the transported finite tensor comparisons with its normalized scalar comparisons.
   S.unit_projection is its unit condition and S.reductionTensor_evaluation is its
   tensor condition. S.reduction_normalized supplies the first normalized input.
2. Apply enrichedSequenceProjectionFormula. Its finite uncurrying equality says that
   the enriched adjunct followed by the nth total-limit projection and the Hom-fiber
   identification is the scalar adjunct of reduced evaluation followed by the evaluated
   counit. The scalar and closed Hom bijections are injective. Consequently that map
   equals the finite scalar enriched map after Hom of coefficientSequenceProjection,
   with the S.reductionEvaluation transport in its first input.
3. Transport the theorem's right-derived sections and limit pairs to the specified
   coefficient functors. Their universal comparison units determine the transports.
   D.globalLimit_model identifies the transported global comparison with S.globalLimit;
   D.globalEvaluation_model identifies the finite map with S.globalEvaluation, and
   D.scalarSections_model identifies the scalar sections map. Thus the generic global
   projection formula is CoefficientGammaProjection for the actual S.gamma.
   H.sections_projection fixes the system-sections projection used in this transport;
   arbitrary evaluation isomorphisms without this equation would not suffice.
4. Apply H-zero to this equality. The coefficientHomZeroEquiv normalizations identify
   Hom of the total-limit projection with postcomposition by that projection. The
   normalized scalar adjunction takes h to its scalar extension followed by the
   finite counit. This is also the last clause of enrichedSequenceProjectionFormula;
   the ordinary and derived section normalizations in D fix its H-zero transports.
   Rewrite the finite counit by S.counit_projection and naturality of
   S.reductionEvaluation. This yields exactly CoefficientHomProjection for the composite
   coefficientGammaZeroMap; no unrelated Hom equivalence is substituted.
The argument applies to the empty scheme, the zero object and every positive coefficient
level. It never asserts that evaluation preserves K-injective systems, or that reducing
an integral mapping complex computes finite internal Hom. -/
theorem coefficientDerivedSystemProjectionFormulas
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (H : CoefficientDerivedSystemProjectionModels l E W S D) :
    CoefficientGammaProjection l E W S D ∧ CoefficientHomProjection l E W S := by
  exact ⟨coefficientDerivedSystemGammaProjectionTransport l E W S D H,
    coefficientDerivedSystemHomProjectionTransport l E W S D H⟩

end WeilConjectures
