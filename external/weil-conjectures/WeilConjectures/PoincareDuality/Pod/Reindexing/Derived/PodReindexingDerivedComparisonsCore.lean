/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingStrictData.PodReindexingStrictComparisons
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCoreDataExistence
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedReductionEvaluation
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedLimitProjection
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedUnit
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedFiniteModel
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedLimitModel

/-! # Localization of the normalized strict reindexing comparisons

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4, 0941 (blueprint: lem-pod-reindexing-derived-comparisons).
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
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

/-! # Core data and normalized laws for derived reindexing comparisons

Source: blueprint Steps 1 and 5 (blueprint: lem-pod-reindexing-derived-comparisons).
-/

/-- Quotient normalization on local scalar-tensor generators.
Source: blueprint Step 1 (blueprint: lem-pod-reindexing-derived-comparisons). -/
def podReindexingQuotientGenerators
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P)) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((β P hP n).hom.f i).val.app (op U))
        (unrestrictedTowerTensorSection l E Y n (P.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) a x) =
      unrestrictedTowerTensorSection l E X n
        (((isoReductionIntegralComplex l E g).obj P).X i) (op U)
        ((isoSectionwiseConstantMap g (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
            (op U) a) x

/-- Compatibility with each consecutive quotient arrow.
Source: blueprint Step 1 (blueprint: lem-pod-reindexing-derived-comparisons). -/
def podReindexingQuotientTransition
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P)) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (z : ((unrestrictedTowerFiniteComplex l E Y (n + 1) P).X i).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))),
    (((β P hP n).hom.f i).val.app (op U))
        (((unrestrictedTowerTransition l E Y P n).f i).val.app
          (op ((proEtaleIsoPostcompose g).obj U)) z) =
      (((unrestrictedTowerTransition l E X
        ((isoReductionIntegralComplex l E g).obj P) n).f i).val.app (op U))
          ((((β P hP (n + 1)).hom.f i).val.app (op U)) z)

/-- The derived comparisons to be descended from the strict comparisons.
Source: blueprint Steps 1 and 5 (blueprint: lem-pod-reindexing-derived-comparisons). -/
structure PodReindexingDerivedData where
  /-- Reindex the strict coherent reduction system. -/
  reduction : (podReindexCalculus l E Y).reduction ⋙
      integralComparisonDerivedSequencePullback l E g ≅
    podOrdinaryReindex l E g ⋙ (podReindexCalculus l E X).reduction
  /-- Reindex the specified total derived limit, for every ambient system. -/
  limit : coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ≅
    integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X
  /-- Finite evaluation uses ordinary finite coefficient reindexing. -/
  evaluation : ∀ n : ℕ, integralComparisonDerivedSequencePullback l E g ⋙
      coefficientSequenceDerivedEvaluation l E X n ≅
    coefficientSequenceDerivedEvaluation l E Y n ⋙ isoReductionFiniteDerived l E g n
  /-- Reindexing commutes with restriction through the actual quotient projection. -/
  restriction : ∀ n : ℕ, coefficientFiniteDerivedRestriction l E Y n ⋙
      podOrdinaryReindex l E g ≅
    isoReductionFiniteDerived l E g n ⋙ coefficientFiniteDerivedRestriction l E X n
  /-- The scalar reduction comparison, simultaneously for all quotient levels. -/
  finite : ∀ n : ℕ, coefficientFiniteDerivedExtension l E Y n ⋙
      isoReductionFiniteDerived l E g n ≅
    podOrdinaryReindex l E g ⋙ coefficientFiniteDerivedExtension l E X n
  /-- The total-limit models are the actual K-injective-normalized models. -/
  sourceRoos : IntegralComparisonRoosModel l E Y
  /-- The actual K-injective model at the target. -/
  targetRoos : IntegralComparisonRoosModel l E X
  /-- The existing completed pullback, with its whole quotient/Roos realization. -/
  pullback : integralDerivedPullback l E g ≅ (podReindexCalculus l E Y).reduction ⋙
    integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X

/-- Assemble the strict chain maps and the derived comparisons without choosing any data.
Source: blueprint Steps 1 and 5 (blueprint: lem-pod-reindexing-derived-comparisons). -/
def PodReindexingDerivedData.assemble
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (S : PodReindexingStrictData l E g)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P))
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (R : PodReindexingDerivedData l E g) : PodCompletionReindex l E g where
  completionSource := CY
  completionTarget := CX
  reduction := R.reduction
  limit := R.limit
  evaluation := R.evaluation
  restriction := R.restriction
  finite := R.finite
  good := S.good l E g
  quotient := β
  roos := S.roos
  shiftSource := SY
  shiftTarget := SX
  sourceRoos := R.sourceRoos
  targetRoos := R.targetRoos
  restricted := S.restricted
  pullback := R.pullback

/-- The localization assertions except pullback normalization.
Source: blueprint Steps 1 and 5 (blueprint: lem-pod-reindexing-derived-comparisons).
-/
def PodReindexingDerivedData.CoreLaws
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (S : PodReindexingStrictData l E g)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P))
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (R : PodReindexingDerivedData l E g) : Prop :=
  let D := R.assemble l E g SY SX S β CY CX
  PodCompletionReindex.ReductionEvaluation l E g D ∧
  PodCompletionReindex.LimitProjection l E g D ∧
  PodCompletionReindex.Unit l E g D ∧
  PodCompletionReindex.FiniteModel l E g D ∧
  PodCompletionReindex.LimitModel l E g D

/-- The full localization assertions, including pullback normalization.
Source: blueprint Steps 1 and 5 (blueprint: lem-pod-reindexing-derived-comparisons).
-/
def PodReindexingDerivedData.Laws
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (S : PodReindexingStrictData l E g)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P))
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (R : PodReindexingDerivedData l E g) : Prop :=
  let D := R.assemble l E g SY SX S β CY CX
  PodCompletionReindex.ReductionEvaluation l E g D ∧
  PodCompletionReindex.LimitProjection l E g D ∧
  PodCompletionReindex.Unit l E g D ∧
  PodCompletionReindex.FiniteModel l E g D ∧
  PodCompletionReindex.LimitModel l E g D ∧
  PodCompletionReindex.PullbackNormalization l E g D

/-- The core package of derived comparisons, omitting only pullback normalization.
Source: blueprint Steps 1 and 5; strict quotient, evaluation and Roos-limit descent.
(blueprint: lem-pod-reindexing-derived-comparisons-core) -/
theorem podReindexingDerivedComparisonsCore
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingQuotientGenerators l E g β)
    (htransition : podReindexingQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X) :
    ∃ R : PodReindexingDerivedData l E g,
      R.CoreLaws l E g SY SX S β CY CX := by
  obtain ⟨Q₀⟩ := podReindexingDerivedCoreData_exists l E g SY SX S hS β hβ htransition CY CX
  obtain ⟨finite, hFinite⟩ := podReindexingDerivedCoreData_finiteModel
    l E g SY SX S hS β hβ htransition CY CX Q₀
  obtain ⟨L, hLimit⟩ := podReindexingDerivedCoreData_limitModel
    l E g SY SX S hS β CY CX { Q₀ with finite := finite }
  obtain ⟨α, hUnit⟩ := podReindexingDerivedCoreData_unit
    l E g SY SX S hS β hβ htransition CY CX { Q₀ with finite := finite, limit := L }
  let Q : PodReindexingDerivedCoreData l E g :=
    { Q₀ with finite := finite, limit := L, reduction := α }
  let R : PodReindexingDerivedData l E g :=
    { reduction := Q.reduction
      limit := Q.limit
      evaluation := Q.evaluation
      restriction := Q.restriction
      finite := Q.finite
      sourceRoos := Q.sourceRoos
      targetRoos := Q.targetRoos
      pullback := Q.pullback }
  have hReduction := podReindexingDerivedCoreData_reductionEvaluation
    l E g SY SX S hS β hβ htransition CY CX Q
  have hProjection := podReindexingDerivedCoreData_limitProjection
    l E g SY SX S hS β hβ htransition CY CX Q
  have hFinite' : PodCompletionReindex.FiniteModel l E g
      (Q.assemble l E g SY SX S β CY CX) := hFinite
  have hLimit' : PodCompletionReindex.LimitModel l E g
      (Q.assemble l E g SY SX S β CY CX) := hLimit
  refine ⟨R, ?_⟩
  change PodCompletionReindex.ReductionEvaluation l E g (R.assemble l E g SY SX S β CY CX) ∧
    PodCompletionReindex.LimitProjection l E g (R.assemble l E g SY SX S β CY CX) ∧
    PodCompletionReindex.Unit l E g (R.assemble l E g SY SX S β CY CX) ∧
    PodCompletionReindex.FiniteModel l E g (R.assemble l E g SY SX S β CY CX) ∧
    PodCompletionReindex.LimitModel l E g (R.assemble l E g SY SX S β CY CX)
  simpa [R, PodReindexingDerivedData.assemble,
    PodReindexingDerivedCoreData.assemble, Q] using
    And.intro hReduction (And.intro hProjection (And.intro hUnit (And.intro hFinite' hLimit')))

end WeilConjectures
