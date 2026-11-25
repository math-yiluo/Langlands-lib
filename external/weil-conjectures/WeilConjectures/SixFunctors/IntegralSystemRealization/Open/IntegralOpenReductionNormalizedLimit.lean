/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenReductionIso
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenLimitComplete

/-! # Canonical integral model construction steps

Source: blueprint fix-prop-coherence, strict-system realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Open reduction and the output reconstruction unit at a good total limit.
Only invertibility of these specified maps is asserted; the realization isomorphism
and its counit/unit normalization are not part of this statement.
Source: Stacks 03DI, 0941, 07A7, 09BP and 0A0E; blueprint fix-prop-coherence,
open reconstruction step of the strict-system realization
(blueprint: lem-sf-integral-open-reduction-normalized-limit).

Proof: write the open immersion as its open slice of the pro-etale site. The ordinary
quotient-tensor/open-extension comparison is invertible by the direct-sum description
of extension by zero, including the empty sum. Its mate under the exact open
adjunction is the ordinary restriction comparison. On flat-term K-flat complexes
this is the reductionPullComplex of m, because the latter is the left-adjoint
conjugate of the identity-section direct-image/limit comparison. The model equation
for m.reductionPull and uniqueness through K-flat localization therefore identify
the derived open mate with m.openReduction. The ordinary inverse comparison
localizes as its inverse, proving the second assertion. Normalized reconstruction
makes L(N) complete. Quasi-compact open extension preserves this completeness:
its exact termwise slice extension preserves countable products and the uniformizer
scalar map, hence the principal-completion triangle; transport from this triangle
to the quotient-tower completeness predicate. Normalized reconstruction now makes
the actual unit at this complete extension invertible, proving the first assertion.
These arguments concern the completed coefficient sheaves and their projections;
they do not require l to be invertible on the scheme or a finite-field base.
The recorded Good input and output conditions retain exactly the ambient theorem domain. -/
theorem integralOpenReductionNormalizedLimit (o : Operations l E)
    (m : RealizationModel l E o) {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] [QuasiCompact j] (N : System l E U)
    (hN : Good l E U N)
    (hJ : Good l E V ((Operations.shriek l E o j).obj N)) :
    IsIso ((calculus l E V).adjunction.unit.app
      ((ringedOpen l E j).obj ((coefficientSequenceLimit l E U).obj N))) ∧
      IsIso ((m.openReduction l E j).app ((coefficientSequenceLimit l E U).obj N)) := by
  refine ⟨?_, ?_⟩
  · have hcomplete := integralOpenLimitComplete l E o j N hN hJ
    exact (purNormalizedReconstructionOfScheme l E V (calculus l E V)).2 _ hcomplete
  · exact integralOpenReductionIso l E o m j _

end WeilConjectures.IntegralSystemRealization
