/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces

/-! # Realization of the reconstructed exceptional adjunction
Source: Zheng, Section 5; integral reconstruction, steps 3--9.
(blueprint: lem-sf-exceptional-integral-realization-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Realize a specified normalized system adjunction by the actual integral
proper/open comparisons, choosing compatible transport shifts on its same functors.
Source: Zheng, Construction 5.25 and Proposition 5.24; integral reconstruction,
steps 3--9, especially the single proper/open word and its primitive comparisons.
(blueprint: lem-sf-exceptional-integral-realization-assembly).

Proof: choose the canonical system operations and their ordinary-limit comparison
model. Rebuild only the transport record on the same ordinary adjoint, site maps
and proper/open comparison, using their localized cochain shifts. Its geometric
and evaluation equations are unchanged; exactness and the signed cochain models
supply the new shift fields. This choice is necessary because an arbitrary
transport record does not assert that its shift fields have this normalization.
Coordinate change, the site inverse image and the ordinary proper/open construction
give systemLeft. Its evaluation square is the scalar-unit, site,
etale compact-support and proper/open mate composite supportProjection: this
identifies the map itself, before using any finite-level conservativity.
The finite-operation bounds, transported by the evaluation comparisons, give
leftBounds and rightBounds independently of the positive coefficient exponent.
Exact open extension retains the input intervals at the intermediate object, so
the single proper/open word has the required finite-Tor realization domain.

The two reconstruction equivalences and the normalized system adjunction give
integralAdjunction by composition. K-flat reduction is additive and exact, while
the K-injective total limit is additive and exact. Restrict their coherent shifts
to the full finite-Tor subcategories and paste with the transported system shifts.
The reduction/limit unit and counit shift equations make the composed unit and
counit shift compatible. Give the right adjoint its adjoint shift; uniqueness
identifies it with the composite right shift, and the triangulated adjoint theorem
makes it exact. This gives the exactness fields and rightShift_adjoint.

For the left realization, follow leftComposite by total limit of systemLeft,
the projection-normalized proper direct-image/limit comparison, and the inverse
open-adjunction mate of reduction pullback followed by the inverse completion
unit. The open reduction theorem makes that unit invertible. This defines the
isomorphism realization and proves primitive in its written order. The direct
and recursive realization comparisons for the one proper/open word agree.
Consequently the prescribed reduction-tower functor lands in the finite-Tor
subcategory. Full faithfulness of its inclusion lifts the composite realization
followed by prescribedRealization inverse to identification, proving normalization
on actual integral maps. This uses whole towers and quotient transitions, and
never asserts faithfulness of finite evaluation on derived morphisms.

Finally the exact open, proper derived, termwise quotient and signed Roos-cone
shift comparisons paste on this same word. They give systemLeftShift,
leftCompositeShift, rightCompositeShift, realizationShift and
prescribedRealizationShift. Transport the latter shift to the finite-Tor lift;
its inclusion comparison and identification then commute with shifts by faithful
inclusion. Cochain signs multiply under addition of all integer shifts, including
negative shifts. The empty source has zero functors; for the identity word the
normalization is the reconstruction triangle identity. -/
theorem exceptionalIntegralRealizationAssembly
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
    (s : Systems l E c) (a : SystemAdjunction l E c s) :
    ∃ t : ExceptionalSystemTransport s.right s.siteX s.siteY s.siteZ
      s.properOpen s.comparison,
      Nonempty (Realization l E c D hl rX rY { s with transport := t }
        (a.withTransport l E c s t)) := by sorry

end WeilConjectures.ExceptionalIntegralReconstruction
