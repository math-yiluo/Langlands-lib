/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionDescentData

/-! # Completed tensor square for scalar/reindexing transitions

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: def-pod-tensor-descent-diagram).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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

attribute [local instance] podTensorReindexAdditive podTensorScalarZero podTensorMixedLeftZero
  podTensorMixedRightZero
  podTensorReindexLimits podTensorReindexColimits
attribute [local irreducible] integralCompletedTensor integralOrdinaryScalar
  integralOperationsTensorTowerFunctor scalarTensorChain scalarTensorOrdinary
  integralOperationsRoos completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor SheafOfModules.monoidalCategory
attribute [local implicit_reducible] podOrdinaryReindex podGoodReindex
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor integralOperationsTensorOnGood
  scalarReductionSourceDerived integralTowerHasDerivedCategory
  integralOperationsCommHasDerivedCategory
  podTensorScalarGoodFunctor podTensorScalarGoodComparison podTensorReindexGoodComparison
  podTensorGoodConstructibleLocalization
  podTensorGoodConstructible podTensorMixedTensorIso podTensorGoodCoefficientTransition
  podTensorTensorReindexDerivedChain
  podTensorTensorScalarDerivedChain podTensorTensorMixedDerivedChain

/-- The InputInclusion component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramInputInclusion
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := (sfIntegralConstructible l E Y).ι

/-- The ReindexFunctor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramReindexFunctor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := podOrdinaryReindex l E g

/-- The ScalarFunctor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramScalarFunctor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := integralOrdinaryDerivedScalar l E L ι X

/-- The MixedFunctor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramMixedFunctor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := integralOrdinaryDerivedScalar l E L ι Y ⋙ podOrdinaryReindex l L g

/-- The SourceLocalization component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramSourceLocalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := podTensorGoodConstructibleLocalization l E Y

/-- The ReindexLocalization component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramReindexLocalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := integralOperationsGoodLocalization l E X

/-- The TargetLocalization component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramTargetLocalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := integralOperationsGoodLocalization l L X

/-- The GoodInclusion component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramGoodInclusion
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := (podTensorGoodConstructible l E Y).ι

/-- The GoodReindex component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramGoodReindex
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := (podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      podGoodReindex
      l E g D

/-- The GoodScalar component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramGoodScalar
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := podTensorScalarGoodFunctor l E L ι X

/-- The GoodMixed component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramGoodMixed
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := (podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      podTensorScalarGoodFunctor l E L ι Y ⋙ podGoodReindex l L g D'

/-- The GoodTransition component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramGoodTransition
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : (podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      (podTensorDiagramGoodScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
        (podTensorDiagramGoodMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) :=
    isoWhiskerLeft (podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)
      (podTensorGoodCoefficientTransition l E g L ι D D' S)

/-- The PairReindex component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramPairReindex
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := ((podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      (podTensorDiagramReindexFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)).prod
        ((podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
          (podTensorDiagramReindexFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore))

/-- The PairScalar component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramPairScalar
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := (podTensorDiagramScalarFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
      (podTensorDiagramScalarFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)

/-- The PairMixed component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramPairMixed
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := ((podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      (podTensorDiagramMixedFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)).prod
        ((podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
          (podTensorDiagramMixedFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore))

/-- The DerivedTransition component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramDerivedTransition
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := S.derived l E L ι g D D'

/-- The PairTransition component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramPairTransition
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : (podTensorDiagramPairReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      (podTensorDiagramPairScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
        (podTensorDiagramPairMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) := NatIso.prod
          (isoWhiskerLeft (podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S
            _hcore) (podTensorDiagramDerivedTransition l E g D _hD T _hT L ι D' _hD' T' _hT' S
              _hcore)) (isoWhiskerLeft (podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD'
                T' _hT' S _hcore) (podTensorDiagramDerivedTransition l E g D _hD T _hT L ι D'
        _hD' T'
                  _hT' S _hcore))

/-- The SourceTensor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramSourceTensor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := ((podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
      (podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
        integralCompletedTensor l E Y

/-- The ReindexTensor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramReindexTensor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := integralCompletedTensor l E X

/-- The TargetTensor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramTargetTensor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := integralCompletedTensor l L X

/-- The SourceRepresentative component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramSourceRepresentative
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := ((podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
      (podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
        integralOperationsTensorOnGood l E Y

/-- The ReindexRepresentative component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramReindexRepresentative
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := integralOperationsTensorOnGood l E X

/-- The TargetRepresentative component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramTargetRepresentative
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := integralOperationsTensorOnGood l L X

/-- The SourceComparison component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramSourceComparison
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : ((podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
      (podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
        (podTensorDiagramSourceTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
          (podTensorDiagramSourceRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) :=
    isoWhiskerLeft ((podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S
      _hcore).prod (podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore))
        (integralCompletedTensorComparison l E Y)

/-- The ReindexComparison component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramReindexComparison
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : ((podTensorDiagramReindexLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
      (podTensorDiagramReindexLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
        (podTensorDiagramReindexTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
          (podTensorDiagramReindexRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) :=
            integralCompletedTensorComparison l E X

/-- The TargetComparison component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramTargetComparison
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : ((podTensorDiagramTargetLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
      (podTensorDiagramTargetLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
        (podTensorDiagramTargetTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
          (podTensorDiagramTargetRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) :=
            integralCompletedTensorComparison l L X

/-- The ReindexFactor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramReindexFactor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := isoWhiskerLeft (podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)
      (podTensorReindexGoodComparison l E g D)

/-- The PairReindexFactor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramPairReindexFactor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : ((podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
      (podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
        (podTensorDiagramPairReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
          ((podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
            (podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
              ((podTensorDiagramReindexLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S
                _hcore).prod (podTensorDiagramReindexLocalization l E g D _hD T _hT L ι D' _hD' T'
                  _hT' S _hcore)) := NatIso.prod (podTensorDiagramReindexFactor l E g D _hD T _hT
        L ι
                    D' _hD' T' _hT' S _hcore) (podTensorDiagramReindexFactor l E g D _hD T _hT L
        ι D'
                      _hD' T' _hT' S _hcore)

/-- The ScalarFactor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramScalarFactor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    := podTensorScalarGoodComparison l E L ι X

/-- The PairScalarFactor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramPairScalarFactor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : ((podTensorDiagramReindexLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
      (podTensorDiagramReindexLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
        (podTensorDiagramPairScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
          ((podTensorDiagramGoodScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
            (podTensorDiagramGoodScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
              ((podTensorDiagramTargetLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S
                _hcore).prod (podTensorDiagramTargetLocalization l E g D _hD T _hT L ι D' _hD' T'
        _hT'
                  S _hcore)) := NatIso.prod (podTensorDiagramScalarFactor l E g D _hD T _hT L ι D'
                    _hD' T' _hT' S _hcore) (podTensorDiagramScalarFactor l E g D _hD T _hT L ι D'
        _hD'
                      T' _hT' S _hcore)

/-- The MixedFactor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramMixedFactor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : (podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      (podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
        (podTensorDiagramMixedFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
          (podTensorDiagramGoodMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
            (podTensorDiagramTargetLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) :=
    isoWhiskerRight (isoWhiskerLeft (podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T'
      _hT' S _hcore) (podTensorScalarGoodComparison l E L ι Y))
        (podOrdinaryReindex l L g) ≪≫
      isoWhiskerLeft ((podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S
        _hcore) ⋙
        podTensorScalarGoodFunctor l E L ι Y) (podTensorReindexGoodComparison l
        L g D')

/-- The PairMixedFactor component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramPairMixedFactor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : ((podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
      (podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
        (podTensorDiagramPairMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
          ((podTensorDiagramGoodMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
            (podTensorDiagramGoodMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)) ⋙
              ((podTensorDiagramTargetLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S
                _hcore).prod (podTensorDiagramTargetLocalization l E g D _hD T _hT L ι D' _hD' T'
        _hT'
                  S _hcore)) := NatIso.prod (podTensorDiagramMixedFactor l E g D _hD T _hT L ι D'
                    _hD' T' _hT' S _hcore) (podTensorDiagramMixedFactor l E g D _hD T _hT L ι D'
        _hD'
                      T' _hT' S _hcore)

/-- The ReindexChain component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramReindexChain
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : ∀ P, (podTensorDiagramReindexFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).obj
      ((podTensorDiagramSourceRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).obj
        P) ⟶
        (podTensorDiagramReindexRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).obj
          (((podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
            (podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)).obj P) :=
              fun P ↦
    podTensorTensorReindexDerivedChain l E g D T P.1.obj P.2.obj

/-- The ScalarChain component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramScalarChain
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : ∀ P, (podTensorDiagramScalarFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).obj
      ((podTensorDiagramReindexRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).obj
        P) ⟶
        (podTensorDiagramTargetRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).obj
          (((podTensorDiagramGoodScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
            (podTensorDiagramGoodScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)).obj P)
        := fun
              P ↦
    podTensorTensorScalarDerivedChain l E L ι X P.1 P.2

/-- The MixedChain component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramMixedChain
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : ∀ P, (podTensorDiagramMixedFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).obj
      ((podTensorDiagramSourceRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).obj
        P) ⟶
        (podTensorDiagramTargetRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).obj
          (((podTensorDiagramGoodMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
            (podTensorDiagramGoodMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)).obj P) :=
        fun
              P ↦
    podTensorTensorMixedDerivedChain l E g L ι D' T' P.1.obj P.2.obj

/-- The ReindexComparisonIso component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramReindexComparisonIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : (podTensorDiagramSourceTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      (podTensorDiagramReindexFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
        (podTensorDiagramPairReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
          (podTensorDiagramReindexTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) :=
    (Functor.associator ((podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S
      _hcore).prod (podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore))
        (integralCompletedTensor l E Y) (podTensorDiagramReindexFunctor l E g D _hD T _hT L ι D'
        _hD'
          T' _hT' S _hcore)) ≪≫
      podTensorTensorReindexIso l E g D T _hT.2.2.2.1

/-- The ScalarComparisonIso component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramScalarComparisonIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : (podTensorDiagramReindexTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      (podTensorDiagramScalarFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
        (podTensorDiagramPairScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
          (podTensorDiagramTargetTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) :=
            scalarTensorOrdinary l E L ι X

/-- The MixedComparisonIso component of the fixed scalar/reindexing tensor diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
def podTensorDiagramMixedComparisonIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    : (podTensorDiagramSourceTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
      (podTensorDiagramMixedFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ≅
        (podTensorDiagramPairMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) ⋙
          (podTensorDiagramTargetTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) :=
    (Functor.associator ((podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S
      _hcore).prod (podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore))
        (integralCompletedTensor l E Y) (podTensorDiagramMixedFunctor l E g D _hD T _hT L ι D' _hD'
          T' _hT' S _hcore)) ≪≫
      podTensorMixedTensorIso l E g L ι D D' T' _hT'.2.2.2.1 S

end WeilConjectures
