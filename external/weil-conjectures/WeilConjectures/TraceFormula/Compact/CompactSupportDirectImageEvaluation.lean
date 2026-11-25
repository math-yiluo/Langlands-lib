/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import WeilConjectures.TraceFormula.Compact.CompactSupportDirectImageOrdinaryEvaluation
import WeilConjectures.TraceFormula.Compact.CompactSupportDirectImageDerivedEvaluation

/-! # Direct-image evaluation for compact support

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 03DI, 03DJ, 07A4, 0941.
This module specializes the ordinary system calculus to the actual pro-etale functors.
(blueprint: lem-trf-compact-support-direct-image-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation of the actual direct-image adjunction, including the ordinary
section formula and the derived arbitrary-resolution formula. No open extension or
finite-coefficient transition comparison is asserted.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941 and 07A4.
The ordinary and derived components are supplied by their strictly smaller
component theorems and assembled here.  The final two equations are exactly the
mate unit and counit equations from the derived component.
(blueprint: lem-trf-compact-support-direct-image-evaluation).
-/
theorem compactSupportDirectImageEvaluation
    {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    [(integralComparisonSequenceDirectImage l E p).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E Z)]
    [∀ n : ℕ, (compactSupportLevelDirectImage l E p n).Additive]
    [∀ n : ℕ, Abelian.HasKInjectiveResolutions (normalizedDVRModules l E Z n)]
    [∀ n : ℕ, (compactSupportLevelPullback l E p n).Additive]
    [∀ n : ℕ, PreservesFiniteLimits (compactSupportLevelPullback l E p n)]
    [∀ n : ℕ, PreservesFiniteColimits (compactSupportLevelPullback l E p n)] :
    ∃ (left : ∀ n : ℕ,
        integralComparisonDerivedSequencePullback l E p ⋙
            coefficientSequenceDerivedEvaluation l E Z n ≅
          coefficientSequenceDerivedEvaluation l E Y n ⋙
            (compactSupportLevelPullback l E p n).mapDerivedCategory)
      (right : ∀ n : ℕ,
        (integralComparisonSequenceDirectImage l E p).rightDerivedFunctor ⋙
            coefficientSequenceDerivedEvaluation l E Y n ≅
          coefficientSequenceDerivedEvaluation l E Z n ⋙
            (compactSupportLevelDirectImage l E p n).rightDerivedFunctor)
      (ordinary : ∀ n : ℕ,
        integralComparisonSequenceDirectImage l E p ⋙ coefficientSequenceEvaluation l E Y n ≅
          coefficientSequenceEvaluation l E Z n ⋙ compactSupportLevelDirectImage l E p n),
(∀ (n : ℕ) (N : coefficientSequenceModules l E Z)
              (V : Y.ProEtᵒᵖ)
              (x : ((integralComparisonSequenceDirectImage l E p ⋙
                coefficientSequenceEvaluation l E Y n).obj N).val.obj V),
              HEq (((ordinary n).hom.app N).val.app V x) x) ∧
      (∀ n : ℕ,
        letI := coefficientSequenceEvaluation_additiveInstance l E Z n
        letI := coefficientSequenceEvaluation_additiveInstance l E Y n
        letI := coefficientSequenceEvaluation_limits l E Z n
        letI := coefficientSequenceEvaluation_colimits l E Z n
        letI := coefficientSequenceEvaluation_limits l E Y n
        letI := coefficientSequenceEvaluation_colimits l E Y n
        CompactSupportDerivedSquareNormalization
            (integralComparisonSequenceDirectImage l E p) (compactSupportLevelDirectImage l E p n)
            (coefficientSequenceEvaluation l E Z n) (coefficientSequenceEvaluation l E Y n)
            (ordinary n).symm (right n).symm) ∧
      (∀ (n : ℕ) M,
          (coefficientSequenceDerivedEvaluation l E Y n).map ((compactSupportCanonicalPAdjunction l
            E p).unit.app M) ≫
            (right n).hom.app ((integralComparisonDerivedSequencePullback l E p).obj
              M) ≫
            ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor).map ((left
              n).hom.app M) =
              (compactSupportCanonicalPLevelAdjunction l E p n).unit.app
                ((coefficientSequenceDerivedEvaluation l E Y n).obj M)) ∧
      (∀ (n : ℕ) N,
          ((compactSupportLevelPullback l E p n).mapDerivedCategory).map ((right
            n).hom.app N) ≫
            (compactSupportCanonicalPLevelAdjunction l E p n).counit.app
              ((coefficientSequenceDerivedEvaluation l E Z n).obj N) =
              (left n).inv.app (((integralComparisonSequenceDirectImage l E
                p).rightDerivedFunctor).obj N) ≫
                (coefficientSequenceDerivedEvaluation l E Z n).map
                  ((compactSupportCanonicalPAdjunction l E p).counit.app N)) := by
  obtain ⟨ordinary, hordinary⟩ := compactSupportDirectImageOrdinaryEvaluation l E p
  obtain ⟨left, right, hderived, hunit, hcounit⟩ :=
    compactSupportDirectImageDerivedEvaluation l E p ordinary
  exact ⟨left, right, ordinary, hordinary, hderived, hunit, hcounit⟩

end WeilConjectures
