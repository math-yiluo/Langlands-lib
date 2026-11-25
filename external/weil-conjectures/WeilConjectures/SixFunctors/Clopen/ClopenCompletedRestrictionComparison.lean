/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
public import WeilConjectures.SmoothPurity.OpenCompletedRestriction.OpenCompletedRestrictionIdentification
import WeilConjectures.SixFunctors.Supporting.OrdinaryIntegralNestedOpenRestriction
import WeilConjectures.SixFunctors.Clopen.ClopenIntegralCompletionRestriction
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion

/-!
# Ordinary restriction of a completed chart to a smaller clopen

Source: Stacks Project, Tags 03D8, 06YY and 08TC; proetale.tex,
lemma-local-structure-constructible-complex (Tag 09C3).
(blueprint: lem-fix-clopen-completed-restriction-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.ordinaryIntegralDerivedPull WeilConjectures.integralDerivedPullback

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- On nested clopens, exact unit-preserving module restriction identifies the
completed chart of a complete complex with its ordinary restriction to the smaller open.
The restriction functor is the existing normalized open restriction, with its
published exactness instances. There is no boundedness, projectivity,
constructibility or affineness hypothesis.

Source: Stacks Project, Tags 03D8, 06YY and 08TC; the restriction step in
proetale.tex, lemma-local-structure-constructible-complex (Tag 09C3).
(blueprint: lem-fix-clopen-completed-restriction-comparison).

Proof: let j be the inclusion A into U. Restrict sheaves by precomposition with
composition of pro-etale objects along j. Identify the completed coefficient rings
by the inverse limit of the constant finite-quotient identifications; their limit
projection equations fix this scalar identification. This gives a module functor F.
It is additive and exact because restriction to an open subtopos preserves kernels
and sheafified cokernels. The coefficient identification identifies F of the unit
with the local unit. A clopen splits the topos as a product with its complement;
its restriction is a coordinate projection and preserves all products. Apply it
to the augmented quotient tower and its Roos triangle. Consequently restriction
of a complete complex stays complete, and the ordinary-to-completed comparison
for the inclusion U into V is invertible on the given complex. The ordinary
derived restriction along j is F.mapDerivedCategory, since F is exact. Apply it
to this comparison and use the ordinary pullback compositor, first for A into U
into V and then for A into V into W. These give the asserted derived isomorphism.
All constructions allow empty clopens and the zero coefficient module. -/
theorem clopen_completed_restriction_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W V : Scheme.{u}) (f : V ⟶ W) (U A : V.Opens)
    (_hU : IsClosed (U : Set V)) (_hA : IsClosed (A : Set V)) (hAU : A ≤ U)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (_hK : IntegralOnSlice.IsComplete l E V none ((ordinaryIntegralDerivedPull l E f).obj K)) :
    Nonempty ((ordinaryIntegralDerivedPull l E (A.ι ≫ f)).obj K ≅
      (OpenCompletedRestriction.derivedRestriction l E (V.homOfLE hAU)).obj
        ((integralDerivedPullback l E U.ι).obj
          ((ordinaryIntegralDerivedPull l E f).obj K))) := by
  obtain ⟨ordinary⟩ := ordinaryIntegralNestedOpenRestriction l E W V f U A hAU
  obtain ⟨completed⟩ := clopenIntegralCompletionRestriction l E V U _hU
  let M := (ordinaryIntegralDerivedPull l E f).obj K
  have hu : IsIso ((IntegralOnSlice.completionUnit l E V none).app M) :=
    (IntegralOnSlice.canonicalCompletionUnitCriterion l E V M).mpr _hK
  let rU := OpenCompletedRestriction.derivedRestriction l E U.ι
  let rA := OpenCompletedRestriction.derivedRestriction l E (V.homOfLE hAU)
  let unitIso := asIso ((IntegralOnSlice.completionUnit l E V none).app M)
  exact ⟨ordinary.app K ≪≫
    rA.mapIso (rU.mapIso unitIso ≪≫ completed.app M)⟩

end WeilConjectures
