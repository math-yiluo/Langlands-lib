/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionPure
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionReduction
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionLimit

/-! # Core scalar/reindexing transition data

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core).

This is the normalized transition construction through the pure-tensor, reduction,
and limit squares.  The completed tensor square is isolated in the next theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The normalized coefficient transition through its pure, reduction and limit squares.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core).

Proof: retain the supplied normalized completion data at both coefficient fields.
The finite-free scalar extension comparison is assembled on the actual quotient
systems; balanced tensor associativity fixes the pure-tensor map and its inverse.
The same strict-system map descends through the normalized Roos realizations, so
its reduction and limit squares are the displayed counit formulas.  The remaining
completed tensor square is proved separately from these normalized data.
-/
def PodReindexCoefficientTransition.Core
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D : PodCompletionReindex l E g) (D' : PodCompletionReindex l L g)
    (S : PodReindexCoefficientTransition l E L ι g D D') : Prop :=
   (∀ (M : scalarReductionSource l E Y) (U : X.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
        (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (S.ordinary.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((isoReductionIntegralInverse l E g).obj M) (op U)
            ((isoReductionCompletedMap l L g).hom.hom.app (op U) a) x) =
          integralOrdinaryTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) a x) ∧
      (∀ K : DerivedCategory (scalarReductionSource l E Y),
        (podScalarReduction l E L ι X D'.targetRoos S.target).app
            ((podOrdinaryReindex l E g).obj K) ≫
          (integralComparisonDerivedSequenceScalar l E L ι X).map
            (D.reduction.inv.app K) ≫
          (integralComparisonSystemScalarPullback l E L ι g).hom.app
            ((podReindexCalculus l E Y).reduction.obj K) =
        (podReindexCalculus l L X).reduction.map
            ((S.derived l E L ι g D D').hom.app K) ≫
          D'.reduction.inv.app
            ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
          (integralComparisonDerivedSequencePullback l L g).map
            ((podScalarReduction l E L ι Y D'.sourceRoos S.source).app K)) ∧
      (∀ N : coefficientSequenceDerived l E Y,
        (integralOrdinaryDerivedScalar l E L ι X).map (D.limit.hom.app N) ≫
          podScalarLimit l E L ι X D'.targetRoos S.target
            ((integralComparisonDerivedSequencePullback l E g).obj N) ≫
          (coefficientSequenceLimit l L X).map
            ((integralComparisonSystemScalarPullback l E L ι g).hom.app N) =
        (S.derived l E L ι g D D').hom.app
            ((coefficientSequenceLimit l E Y).obj N) ≫
          (podOrdinaryReindex l L g).map
            (podScalarLimit l E L ι Y D'.sourceRoos S.source N) ≫
          D'.limit.hom.app
            ((integralComparisonDerivedSequenceScalar l E L ι Y).obj N))

/-- The normalized core transition exists through the pure, reduction, and limit squares.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core).

Proof: construct the ordinary scalar/reindexing isomorphism as the mate of the
restriction-of-scalars square, with its pure section formula, and choose normalized
primitive quotient scalar models. Apply the reduction-square component to this
transition. The limit square follows from reduction by the reduction/limit
adjunction and the counit laws of the supplied reindexing data. Package these
three clauses into Core. -/
theorem podReindexingTensorCoefficientTransition_core
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (hT' : PodCompletedTensorReindex.Laws l L g D' T') :
    ∃ S : PodReindexCoefficientTransition l E L ι g D D',
      PodReindexCoefficientTransition.Core l E g L ι D D' S := by
  obtain ⟨S, hpure⟩ := podReindexingTensorCoefficientTransition_pure
    l E g D hD T hT L ι D' hD' T' hT'
  have hred := podReindexingTensorCoefficientTransition_reduction
    l E g D hD T hT L ι D' hD' T' hT' S hpure
  have hlim := podReindexingTensorCoefficientTransition_limit
    l E g D hD T hT L ι D' hD' T' hT' S hpure hred
  exact ⟨S, hpure, hred, hlim⟩
end WeilConjectures
