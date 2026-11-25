/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientStages
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalLeftRefinements

/-! # Normalized coefficient adjunction construction before coherence

The coefficient records retain the literal localization and common representative-arrow
normalizations supplied by coefficient-stage construction; the assembly preserves them. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Construct the normalized adjunctions and individual invertible coefficient mates.
No identity or composition law for these comparisons is asserted here.
Source: current blueprint exceptional inverse image paragraph, and Zheng, Lemma 5.22;
steps 1--5 and 7--13 of the constructible coefficient adjunction argument
(blueprint: lem-sf-constructible-exceptional-coefficient-construction).

Proof: At finite coefficients, open extension preserves the original Tor interval and
proper pushforward enlarges its upper endpoint by twice a dimension bound of the fixed
compactification. Restrict the ordinary etale compact-support adjunction to bounded
constructible finite-Tor objects, using the specified etale-origin Hom equivalence and
exceptional preservation. Transport the adjunction to the pro-etale site. Endow its right
adjoint with the adjoint shift structure; the adjunction shift identities and exactness
of the left functor imply exactness of the right functor. On bounded flat models scalar
extension preserves the Tor interval. Define q by the scalar-adjunction mate of the
proper/open restriction square. The etale constant-coefficient projection formula makes
q invertible; the exceptional constant-tensor theorem makes its counit transpose b
invertible, even for nonflat quotients. Their shift identities follow from the derived
adjunction comparisons.

For integral coefficients use the ordinary etale strict-system adjunction of Zheng 5.22,
including its evaluation comparisons. Transport through system site comparison; joint
conservativity of evaluations proves invertibility of the system comparisons. The
reduction--limit equivalence on derived-complete objects and normalized towers descends
the adjunction: the unit is the actual compatible reduction cone, the counit is normalized
DVR effectivity, and both sides retain the uniform finite-level bounds above. Finite-free
completed scalar comparison and cofinality of the ramified en subsequence give the stated
integral comparisons. Localize these linear Hom bijections to obtain rational adjunctions,
then take their common finite-field stages for the closed coefficient category. These
constructions give the displayed realization normalizations and the tensor-normalized
scalar identity and composition isomorphisms, without asserting their q/b cocycles.
For each proper compactification refinement use its open-unit/proper-counit normalized
left comparison and its conjugate right comparison. Conjugation proves both refinement
adjunction equations and transports shifts. At field stages use the localized and common
stage maps, yielding refinementRational and refinementCommon. Empty schemes give the
zero functors and dimension bound zero; no separatedness of X or Y over k is used. -/
theorem exists_coefficient_construction (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (CoefficientConstruction.{u, v} l Ω D hl (f := f)) := by
  obtain ⟨R, F, M, H⟩ := exists_coefficient_stages.{u, v} l Ω D hl f
  obtain ⟨N⟩ := exists_coefficient_left_refinements.{u, v} l Ω D hl f R F M H
  refine ⟨{
    ring := R
    fields := F
    common := M
    localizationIdentity := H.localizationIdentity
    refinements := ?_ }⟩
  exact {
    refinement := fun r s ↦ refinementComparisonOfLeft.{u, v} l Ω
      (R.operation _ s) (R.operation _ s) (N.left r s) (N.leftShift r s)
    refinement_normalized := N.normalized
    refinementRational := N.rational
    refinementCommon := N.common }

end ConstructibleExceptionalCoefficients
end WeilConjectures
