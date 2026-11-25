/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexSubstitution
import all WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import all WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationComparisons

/-! # Core data for fixed normalized reindexing substitution

This isolates the construction of the completed-operation model and all its
comparison, substitution, and structural laws. The tensor model and canonical
normalization remain supplied by `PodCompletedTensorReindex.Laws`.
(blueprint: lem-pod-reindexing-tensor-substitution-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The fixed-model part of normalized reindexing substitution.

The construction follows the normalized quotient/Roos presentation: use the
specified calculus, completion and pullback data from `D`, transport the
canonical closed tensor realization to the two integral completed tensors, and
prove the primitive comparison, substitution, and structural laws by the
whole-system counit and expression induction. The two tensor-normalization
fields are deliberately omitted and are supplied by the tensor laws of `T`.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-substitution-core). -/
structure PodReindexingTensorSubstitutionCoreData
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) where
  C : CompletedOperations.Models l E (podReindexLocations X Y)
  qY : integralCompletedTensor l E Y ≅
    IntegralOnSlice.completedTensor l E Y none
  qX : integralCompletedTensor l E X ≅
    IntegralOnSlice.completedTensor l E X none
  calculus_false : C.calculus false = podReindexCalculus l E Y
  calculus_true : C.calculus true = podReindexCalculus l E X
  completion_false : HEq (C.completion false) D.completionSource
  completion_true : HEq (C.completion true) D.completionTarget
  roos_false : C.roos false = D.sourceRoos
  roos_true : C.roos true = D.targetRoos
  pullback : HEq (C.pullback (a := true) (b := false) g).realization D.pullback
  tensor_Y : (qY ≪≫ CompletedOperations.tensorRealization l E C false ≪≫
    podReindexTensorCodomainComparison l E C false) = pullbackTensorIntegralTensorModel l E Y
  tensor_X : (qX ≪≫ CompletedOperations.tensorRealization l E C true ≪≫
    podReindexTensorCodomainComparison l E C true) = pullbackTensorIntegralTensorModel l E X
  limit : ∀ N : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y N →
      (podOrdinaryToCompleted l E g D).app
          ((coefficientSequenceLimit l E Y).obj N) ≫
        CompletedOperations.pullbackComparison l E C (a := true) (b := false) g N =
      D.limit.hom.app N
  comparisonLaws : CompletedOperations.ComparisonLaws.{u, u, 0, 0} l E C
  substitutionLaw : CompletedOperations.SubstitutionLaw.{u, u, 0, 0, 0} l E C
  structuralLaw : CompletedOperations.StructuralLaw.{u, u, 0, 0} l E C

-- Preserve the published names of the unused tensor law and existential witness.
set_option linter.unusedVariables false in
/-- Core normalized model construction.

The proof is the construction described in the declaration above. Its remaining
work is strictly below `PodReindexSubstitution`: it constructs the fixed model,
its realization identifications and all three expression laws, while leaving the
already supplied tensor `Model` and `Canonical` assertions to the caller.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-substitution-core). -/
theorem podReindexingTensorSubstitutionCore
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T) :
    ∃ core : PodReindexingTensorSubstitutionCoreData l E g D,
      True := by
  classical
  rcases hD with ⟨hunits, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnormal⟩
  let W := podReindexLocations X Y
  have hl (a : Bool) (x : W a) : IsUnit (l : (W a).residueField x) := by
    cases a <;> exact isUnit_of_invertible _
  let calculus : ∀ a : Bool, CoefficientDerivedSystemCalculus l E (W a) :=
    fun a ↦ match a with
      | false => podReindexCalculus l E Y
      | true => podReindexCalculus l E X
  let completion : ∀ a : Bool, IntegralOnSlice.completion l E (W a) none ≅
      (calculus a).reduction ⋙ coefficientSequenceLimit l E (W a) :=
    fun a ↦ match a with
      | false => D.completionSource
      | true => D.completionTarget
  have completion_unit : ∀ a K,
      (IntegralOnSlice.completionUnit l E (W a) none).app K ≫
        (completion a).hom.app K = (calculus a).adjunction.unit.app K := by
    intro a
    cases a
    · exact hunits.1
    · exact hunits.2
  let roos : ∀ a : Bool, IntegralComparisonRoosModel l E (W a) :=
    fun a ↦ match a with
      | false => D.sourceRoos
      | true => D.targetRoos
  let system (a : Bool) := Classical.choice
    (ringedSiteDualityMaps_exists.{u + 1, u, u, u + 2}
      (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
      (coefficientSequenceCommRingSheaf l E (W a)))
  let fallback {a b : Bool} (f : W a ⟶ W b) :
      IntegralComparisonPullbackModel l E f (calculus b) (roos a) :=
    Classical.choice (primitiveQuotientRealizationComparisons l E E (AlgHom.id _ _)
      f (W b) (hl a) (hl b) (hl b) (calculus b) (calculus b) (roos a) (roos b)).1
  let pullback : ∀ {a b : Bool} (f : W a ⟶ W b),
      IntegralComparisonPullbackModel l E f (calculus b) (roos a) := by
    intro a b f
    cases a
    · exact fallback f
    · cases b
      · exact if hf : f = g then hf.symm ▸ ⟨D.pullback, hnormal⟩
        else fallback f
      · exact fallback f
  let C : CompletedOperations.Models l E W :=
    { calculus := calculus
      system := system
      completion := completion
      completion_unit := completion_unit
      roos := roos
      pullback := pullback }
  have hprimitive : CompletedOperations.PrimitiveLaws l E C :=
    ⟨fun a ↦ CompletedOperations.modelCounit l E C a (hl a),
      fun a ↦ CompletedOperations.modelUnit l E a (hl a),
      fun a ↦ CompletedOperations.modelTensor l E C a (hl a),
      fun {a b} f ↦ CompletedOperations.modelPullback l E C f (hl a) (hl b)⟩
  have hcomparison := CompletedOperations.comparisonLaws_of_primitive.{u, u, 0, 0}
    l E C hprimitive
  have hpullback : (C.pullback (a := true) (b := false) g).realization = D.pullback := by
    dsimp only [C, pullback]
    simp only [dite_true]
  let qY := pullbackTensorIntegralTensorModel l E Y ≪≫
    (podReindexTensorCodomainComparison l E C false).symm ≪≫
    (CompletedOperations.tensorRealization l E C false).symm
  let qX := pullbackTensorIntegralTensorModel l E X ≪≫
    (podReindexTensorCodomainComparison l E C true).symm ≪≫
    (CompletedOperations.tensorRealization l E C true).symm
  refine ⟨{ C := C, qY := qY, qX := qX
            calculus_false := rfl, calculus_true := rfl
            completion_false := HEq.rfl, completion_true := HEq.rfl
            roos_false := rfl, roos_true := rfl
            pullback := heq_of_eq hpullback
            tensor_Y := ?_, tensor_X := ?_, limit := ?_
            comparisonLaws := hcomparison
            substitutionLaw := ?_, structuralLaw := ?_ }, trivial⟩
  · simp only [qY, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  · simp only [qX, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  · intro N _
    dsimp only [CompletedOperations.pullbackComparison]
    rw [hpullback]
    change (podOrdinaryToCompleted l E g D).app
        ((coefficientSequenceLimit l E Y).obj N) ≫
      D.pullback.hom.app ((coefficientSequenceLimit l E Y).obj N) ≫
        (coefficientSequenceLimit l E X).map
          ((integralComparisonDerivedSequencePullback l E g).map
            ((podReindexCalculus l E Y).adjunction.counit.app N)) = D.limit.hom.app N
    dsimp only [podOrdinaryToCompleted, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    have hn := D.limit.hom.naturality ((podReindexCalculus l E Y).adjunction.counit.app N)
    change (podOrdinaryReindex l E g).map
        ((coefficientSequenceLimit l E Y).map
          ((podReindexCalculus l E Y).adjunction.counit.app N)) ≫ D.limit.hom.app N =
      D.limit.hom.app ((podReindexCalculus l E Y).reduction.obj
        ((coefficientSequenceLimit l E Y).obj N)) ≫ (coefficientSequenceLimit l E X).map
        ((integralComparisonDerivedSequencePullback l E g).map
          ((podReindexCalculus l E Y).adjunction.counit.app N)) at hn
    rw [← hn, ← Category.assoc, ← Functor.map_comp,
      (podReindexCalculus l E Y).adjunction.right_triangle_components]
    exact (congrArg (· ≫ D.limit.hom.app N)
      ((podOrdinaryReindex l E g).map_id _)).trans (Category.id_comp _)
  · intro I J location location' σ a P N _
    exact CompletedOperations.comparison_substitution l E C σ P N
  · apply CompletedOperations.structuralLaw_of_invertible l E C
    intro I location a P N hN
    exact (hcomparison.invertible P N hN).1

end WeilConjectures
