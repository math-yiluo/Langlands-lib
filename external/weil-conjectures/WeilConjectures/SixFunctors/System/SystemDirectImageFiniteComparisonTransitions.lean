/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SixFunctors.Completed.CompletedDirectImageFiniteProjectionTransitions
public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import all WeilConjectures.TraceFormula.Compact.CompactSupportDirectImageRestrictionTransition
import all WeilConjectures.TraceFormula.Compact.CompactSupportFiniteCoefficientPresentation

/-! # Quotient coherence of the finite perfect-projection comparisons

Source: Zheng, Construction 4.1, Lemma 4.10 and Proposition 4.21;
Stacks 0941, 0944 and 099N.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [(integralComparisonSequenceDirectImage l E f).Additive]
  [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
  [∀ n : ℕ, (compactSupportLevelDirectImage l E f n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (normalizedDVRModules l E X n)]

/-- The finite comparison from reduction of completed direct image to actual
system direct image. Its factors are the given reduction evaluations, the
canonical perfect-quotient projection arrow and the given direct-image evaluation.
No choices of objects or morphisms are made here.
Source: Stacks 0944; Zheng Construction 4.1
(blueprint: lem-weil-system-direct-image-finite-comparison-transitions). -/
def systemDirectImageFiniteComparison
    (S : CoefficientDerivedSystemCalculus l E X)
    (T : CoefficientDerivedSystemCalculus l E Y)
    (d : ∀ n : ℕ,
      (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor ⋙
          coefficientSequenceDerivedEvaluation l E Y n ≅
        coefficientSequenceDerivedEvaluation l E X n ⋙
          (compactSupportLevelDirectImage l E f n).rightDerivedFunctor)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E Y n).obj
        (T.reduction.obj ((sfCompletedDerivedDirectImage l E f).obj K)) ⟶
      (coefficientSequenceDerivedEvaluation l E Y n).obj
        ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
          (S.reduction.obj K)) :=
  (T.reductionEvaluation n).hom.app ((sfCompletedDerivedDirectImage l E f).obj K) ≫
    completedDirectImageFiniteProjection l E f n K ≫
      (compactSupportLevelDirectImage l E f n).rightDerivedFunctor.map
        ((S.reductionEvaluation n).inv.app K) ≫ (d n).inv.app (S.reduction.obj K)

/-- The specified finite comparison arrows commute with every actual quotient
transition, in the finite coefficient derived category before completed restriction.
This is solely an equality of the specified arrows; it asserts neither their
invertibility nor normalization of either system.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941, 0944 and 099N.
(blueprint: lem-weil-system-direct-image-finite-comparison-transitions).

Proof: first identify the normalized restriction functor with the native scalar
restriction functor. Their horizontal transformations have the same section
formula. Localization and the derived factorization equations identify their
actual derived transitions. The reduction unit/projection equation then shows
that reduction evaluations carry these transitions to scalar-adjunction quotient
mates. Changing the restriction presentation changes these mates by precisely
the derived comparison isomorphism.

The section-normalized finite direct-image square pastes with the two completed
restriction comparisons. Its arbitrary-resolution normalization identifies this
pasting with the derived square for every pair of quotient levels. Taking scalar
adjunction mates, and using the two unit equations, shows that the canonical
projection arrows commute with quotient mates. Finally the normalized system
direct-image evaluation square intertwines actual transitions. Compose these
three equalities, use naturality of the finite restriction comparison, and cancel
the inverse evaluation factors. Every equality is in the finite derived category;
no faithfulness of derived restriction is used. Equal indices, n = 0, zero
complexes and empty schemes use exactly the same formulas. -/
theorem systemDirectImageFiniteComparison_transitions
    (S : CoefficientDerivedSystemCalculus l E X)
    (T : CoefficientDerivedSystemCalculus l E Y)
    (o : ∀ n : ℕ,
      integralComparisonSequenceDirectImage l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
        coefficientSequenceEvaluation l E X n ⋙ compactSupportLevelDirectImage l E f n)
    (d : ∀ n : ℕ,
      (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor ⋙
          coefficientSequenceDerivedEvaluation l E Y n ≅
        coefficientSequenceDerivedEvaluation l E X n ⋙
          (compactSupportLevelDirectImage l E f n).rightDerivedFunctor)
    (ho : ∀ (n : ℕ) (M : coefficientSequenceModules l E X) (V : Y.ProEtᵒᵖ)
      (x : ((integralComparisonSequenceDirectImage l E f ⋙
        coefficientSequenceEvaluation l E Y n).obj M).val.obj V),
      HEq (((o n).hom.app M).val.app V x) x)
    (hd : ∀ n : ℕ,
      letI := coefficientSequenceEvaluation_additiveInstance l E X n
      letI := coefficientSequenceEvaluation_additiveInstance l E Y n
      letI := coefficientSequenceEvaluation_limits l E X n
      letI := coefficientSequenceEvaluation_colimits l E X n
      letI := coefficientSequenceEvaluation_limits l E Y n
      letI := coefficientSequenceEvaluation_colimits l E Y n
      CompactSupportDerivedSquareNormalization
        (integralComparisonSequenceDirectImage l E f) (compactSupportLevelDirectImage l E f n)
        (coefficientSequenceEvaluation l E X n) (coefficientSequenceEvaluation l E Y n)
        (o n).symm (d n).symm)
    (K : DerivedCategory (scalarReductionSource l E X)) {m n : ℕ} (h : n ≤ m) :
    (coefficientSequenceDerivedTransition l E Y h).app
        (T.reduction.obj ((sfCompletedDerivedDirectImage l E f).obj K)) ≫
      (normalizedDVRRes l E Y h).map (systemDirectImageFiniteComparison l E f S T d K n) =
    systemDirectImageFiniteComparison l E f S T d K m ≫
      (coefficientSequenceDerivedTransition l E Y h).app
        ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
          (S.reduction.obj K)) := by
  obtain ⟨a₀, a, ha, hn⟩ := compactSupportFiniteCoefficientPresentation l E f
  have hsys := derived_transition
    (integralComparisonSequenceDirectImage l E f)
    (compactSupportLevelDirectImage l E f m) (compactSupportLevelDirectImage l E f n)
    (coefficientSequenceEvaluation l E X m) (coefficientSequenceEvaluation l E X n)
    (coefficientSequenceEvaluation l E Y m) (coefficientSequenceEvaluation l E Y n)
    (normalizedDVRModuleRes l E X h) (normalizedDVRModuleRes l E Y h)
    (a h) (a₀ h) (d m) (d n) (o m) (o n) (hn h) (hd m) (hd n)
    (coefficientSequenceTransition l E X h) (coefficientSequenceTransition l E Y h)
    (coefficientSequenceDerivedTransition l E X h) (coefficientSequenceDerivedTransition l E Y h)
    (transition_rep l E X h) (transition_rep l E Y h)
    (ordinary_transition l E f h (a₀ h) (o m) (o n) (ha h) (ho m) (ho n))
    (S.reduction.obj K)
  have hS := systemReductionQuotient_transitions l E X S h K
  have hT := systemReductionQuotient_transitions
    l E Y T h ((sfCompletedDerivedDirectImage l E f).obj K)
  have hP := completedDirectImageFiniteProjection_transitions
    l E f h (a₀ h) (a h) (ha h) (hn h) K
  have hS' : (systemReductionQuotient l E X h).app K ≫
      (normalizedDVRRes l E X h).map ((S.reductionEvaluation n).inv.app K) =
    (S.reductionEvaluation m).inv.app K ≫
      (coefficientSequenceDerivedTransition l E X h).app (S.reduction.obj K) := by
    apply (cancel_epi ((S.reductionEvaluation m).hom.app K)).mp
    rw [← Category.assoc, ← hS]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Iso.hom_inv_id_app_assoc]
    erw [(normalizedDVRRes l E X h).map_id, Category.comp_id]
  apply (cancel_mono ((normalizedDVRRes l E Y h).map
    ((d n).hom.app (S.reduction.obj K)))).mp
  simp only [systemDirectImageFiniteComparison, Functor.map_comp, Category.assoc]
  rw [← (normalizedDVRRes l E Y h).map_comp, Iso.inv_hom_id_app]
  erw [(normalizedDVRRes l E Y h).map_id, Category.comp_id]
  erw [reassoc_of% hT, reassoc_of% hP]
  have hnatur := (a h).hom.naturality ((S.reductionEvaluation n).inv.app K)
  dsimp only [Functor.comp_map] at hnatur
  erw [← hnatur, ← Functor.map_comp_assoc, hS', Functor.map_comp]
  erw [hsys]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

end WeilConjectures
