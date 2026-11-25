/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionComparison
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting

/-! # Open and proper/open coefficient squares

Source: blueprint main-20261015, fix-prop-coherence.proof.md, the maps-used sentence
and the open-adjunction/clopen expansion
(blueprint: lem-sf-open-interchange-reduction-squares).

The existing finite-word interface supplies the actual recursive coefficient maps,
independently completed ringed-site maps, and four-factor lambda. The predicates here
select generators in that interface; they introduce no new operations or comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u s i
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction

namespace WeilConjectures.OpenInterchangeReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The structural squares assumed in the assertion, excluding the open comparisons
whose squares are the conclusion. Source: blueprint fix-prop-coherence, maps-used sentence
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def Structural {S : Type s} {W : S → Scheme.{u}} {I : Type i} {location : I → S}
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  match g with
  | .tensorAssociator .. | .tensorLeftUnit .. | .tensorRightUnit ..
  | .pullComposition .. | .pushComposition ..
  | .pullPushUnit .. | .pullPushCounit .. | .openUnit .. | .openCounit .. => True
  | .openBaseChange .. | .openTensor ..
  | .properOpenInterchange .. | .properOpenLambda .. => False

/-- The square for the inverse of a specified isomorphism, using exactly the same
recursive comparisons at its endpoints. The ambient inverse is only used on the
admissible domain where the canonical maps are invertible.
Source: blueprint fix-prop-coherence, proof step 1, inversion of squares
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def InverseAssertion {S : Type s} (W : S → Scheme.{u}) {I : Type i}
    (location : I → S) (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  C.r l E W location o K ≫
    inverseOrZero (g.systemMap l E W location o (inputReduction l E W location K)) =
  (IntegralSystemRealization.calculus l E (W a)).reduction.map
    (inverseOrZero (g.integralMap l E W location o K)) ≫ B.r l E W location o K

/-- Structural-square hypothesis as a family on the stipulated intermediate domain.
There is no length-three bound here: in particular it applies to the length-four
intermediates in the clopen factorization. Each instance is a square of the actual
whole-system maps, not a choice of a lift of an evaluated square.
Source: blueprint fix-prop-coherence, structural-square hypothesis
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def StructuralSquares (D : FiniteFieldDatum.{u}) (o : Operations l E) : Prop :=
  ∀ {S : Type s} (W : S → Scheme.{u}) (_hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C),
    Structural g →
    ∀ (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
      (lo hi torLo torHi : ℤ),
      (∀ k : I, Admissible l E
        (IntegralSystemRealization.calculus l E (W (location k))) (K k)
        lo hi torLo torHi) →
      Word.admissible l E W location o K lo hi torLo torHi B →
      Word.admissible l E W location o K lo hi torLo torHi C →
      Assertion l E W location o K g

end WeilConjectures.OpenInterchangeReduction
