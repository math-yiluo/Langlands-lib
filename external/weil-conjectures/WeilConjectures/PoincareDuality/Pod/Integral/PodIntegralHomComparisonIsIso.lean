/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
import WeilConjectures.PoincareDuality.Pod.Integral.PodIntegralHomComparisonComparisonIdentification

/-! # Invertibility of the integral pullback Hom comparison

Source: Stacks Project, Tag 0GMX; blueprint main-20261015
theorem-poincare-duality-frobenius--2, Steps 8--11
(blueprint: stage3-derived-automorphism-continuation-a-integral-isIso).

The invertibility field of `podIntegralHomComparison_laws`, left as a statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Invertibility component of the integral pullback Hom compatibility.
Source: Stacks 0GMX; node lem-pod-derived-automorphism-hom-evaluation, steps 8--11.
Proof: reindexing along the isomorphism of sites is an exact equivalence that
preserves K-flat and K-injective complexes, and its ambient product-Hom
comparison `c⁰` is an isomorphism for arbitrary inputs
(lem-pod-reindexing-hom-resolution-model); the evaluation calculus identifies
`c⁰` with the evaluation-defined comparison
(lem-pod-reindexing-evaluation-shift-composition). On complete inputs the
completion-unit lemma identifies exact reindexing with the recorded completed
pullback and its tensor comparison with `μ`
(lem-pod-reindexing-completion-unit-tensor), and the reflection lemma extends
ordinary evaluation uniquely along the completion unit and restricts `c⁰` to the
Hom-constructible pairs (lem-pod-reindexing-completed-evaluation-reflection).
Hence `c_P` is the restriction of the isomorphism `c⁰`; a full-subcategory arrow
whose underlying arrow is invertible is invertible.
(blueprint: stage3-derived-automorphism-continuation-a-integral-isIso). -/
theorem podIntegralHomComparison_isIso :
    ∀ P : (constructibleIntegralHomPairs l E Y).FullSubcategory,
      IsIso (podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) P) := by
  intro P
  rw [podIntegralHomComparison_eq_integralComparison l E g P]
  infer_instance

end WeilConjectures
