/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenTransportCore
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenTransportPasting

/-! # Transport of intrinsic proper/open pasting

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941, 03DI, 07A7;
blueprint fix-prop-coherence, strict-system realization.
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

/-- Transport the intrinsic proper/open map to any section-normalized operation
models. This assertion has no tensor comparison conclusion.
Source: Stacks 0F7B--0F7F and 07A7; fix-prop-coherence,
strict-system realization step 3
(blueprint: lem-sf-integral-system-proper-open-transport).

Proof: conjugate the intrinsic semilinear gamma by the direct and open isomorphisms
of the bridge. This defines a natural transformation on whole systems and makes
the canonical field hold by cancellation. The bridge pull comparison is ordinary
left-adjoint uniqueness for its section identity, and the push and open comparisons
are its adjunction conjugates. The section normalization of the direct compositor
therefore identifies both ordinary compositors under the bridge. Localization of
its representative equation identifies their derived pull compositors, and adjoint
conjugation identifies the direct and open compositors. The beta inverse and the
clopen map agree under the bridge because their specified transposes agree.
Consequently the cartesian conjugate, restriction factor and clopen/direct factors
of properOpenLambda transport to the intrinsic lambda. Transport the intrinsic
gamma adjunct equation to obtain the adjunct field. Substitute the transported
gamma in each of the vertical, horizontal and base-change equations of
semilinearProperOpenMatePasting. Move bridge isomorphisms through the functors by
naturality; adjacent inverse pairs cancel. The compositor, beta and exchange
identifications just established leave precisely the three required equations.
These are equations in the derived system category, without detection of equality
by finite evaluation. Identity maps and empty opens use the same cancellation. -/
theorem integralSystemProperOpenTransport (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o) :
    Nonempty (ProperOpenCoherence l E o c a b) := by
  obtain ⟨hc⟩ := integralSystemProperOpenTransportCore l E o c a b
  obtain ⟨hp⟩ := integralSystemProperOpenTransportPasting l E o c a hc.gamma b hc.canonical
  exact ⟨{
    gamma := hc.gamma
    adjunct := hc.adjunct
    canonical := hc.canonical
    vertical := hp.vertical
    horizontal := hp.horizontal
    baseChange := hp.baseChange
  }⟩

end WeilConjectures.IntegralSystemRealization
