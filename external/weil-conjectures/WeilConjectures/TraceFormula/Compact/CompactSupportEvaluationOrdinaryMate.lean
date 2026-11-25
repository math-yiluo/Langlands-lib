/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Ordinary evaluation mate for geometric direct image

Source: Zheng, Construction 4.1 and Lemma 4.10.
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

/-- The inverse mate of an ordinary direct-image evaluation is invertible.

Source: Zheng, Construction 4.1 and Lemma 4.10, ordinary inverse-image evaluation.
Apply the sequence-module pullback evaluation theorem to the product of the
pro-etale base-change functor with the identity on the natural-number poset.
Its right coextension to level n has value M at every m with n ≤ m, with scalars
restricted through the horizontal ring map, and zero otherwise. The mate under
the evaluation/coextension adjunctions acts pointwise by the sectionwise bijection
of the supplied ordinary comparison. It is invertible, also below n where both
coextensions are zero. The iterated-mates identity then reflects this invertibility
back to the inverse mate under the two geometric adjunctions. The coefficient
slice identifications are exactly coefficientSequenceEvaluationRing_eq.
(blueprint: lem-trf-compact-support-evaluation-ordinary-mate).
-/
theorem compactSupportEvaluationOrdinaryMate_isIso
    {Z Y : Scheme.{t}} (p : Z ⟶ Y) (n : ℕ)
    (ordinary : integralComparisonSequenceDirectImage l E p ⋙
        coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E Z n ⋙ compactSupportLevelDirectImage l E p n) :
    IsIso (((mateEquiv
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E p))
      (Adjunction.ofIsRightAdjoint (compactSupportLevelDirectImage l E p n))).symm
        (TwoSquare.mk _ _ _ _ ordinary.hom))) := by
  let : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange p)).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology Z)) :=
    ProEtale.VaryingRing.baseChange_continuous p
  exact SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z) (Scheme.proEtaleBaseChange p)
    _ _ n _ _ _
    (coefficientSequenceEvaluationRing_eq l E Y n)
    (coefficientSequenceEvaluationRing_eq l E Z n)
    _ _ _
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E p))
    (Adjunction.ofIsRightAdjoint (compactSupportLevelDirectImage l E p n)) ordinary

end WeilConjectures
