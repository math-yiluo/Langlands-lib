/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorDescentDiagram
public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionChainSquareDiagramAux
public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionChainSquareDiagramUnfold
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelTower
import all WeilConjectures.SmoothPurity.Supporting.AdditiveRoosHorizontal

/-! # Completed tensor square for scalar/reindexing transitions

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-tensor-chain-square-diagram).
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
  scalarTensorChain scalarTensorOrdinary
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

attribute [local irreducible] integralOrdinaryTensorSection
  integralCompletedScalarMap scalarAdjunction
attribute [local implicit_reducible] integralOperationsTensorLevel
  integralOperationsTensorComposite integralOperationsRestrict
  integralOperationsTensorTowerFunctor
  Functor.ofOpSequence Functor.ofSequence isoSectionwiseModuleInverseImage
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
attribute [local instance 2001] integralOperationsFiniteHasMap
attribute [local irreducible] integralOperationsTensorTowerFunctor

attribute [local implicit_reducible] podTensorDiagramReindexFunctor
  podTensorDiagramReindexRepresentative podTensorDiagramSourceRepresentative
  podTensorDiagramTargetRepresentative podTensorDiagramScalarFunctor
  podTensorDiagramMixedFunctor podTensorDiagramGoodReindex podTensorDiagramGoodScalar
  podTensorDiagramGoodMixed podTensorDiagramGoodInclusion podTensorDiagramGoodTransition
  podTensorDiagramPairReindex podTensorDiagramPairScalar podTensorDiagramPairMixed
  podTensorDiagramDerivedTransition podTensorDiagramPairTransition

-- The diagram wrappers involve several large exact-derived comparison types.
/-- The mixed tensor square on the fixed good Roos representative diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: lem-pod-tensor-chain-square-diagram).

Proof: on each finite quotient and homogeneous tensor summand, scalar extension
sends a tensor generator a tensor (x tensor y) to (a tensor x) tensor (1 tensor y).
Reindexing relabels the section object. The pure-tensor clause for S and the
generator clauses for T and T' identify the two paths. Balancing gives equality
on each tensor summand. Their signed total differentials and quotient-transition
maps agree. The two product-coordinate equations of the Roos comparisons then
give the chain equation before localization. Apply podCoefficientExactSquareChain:
naturality moves its localization factors through the chain maps, and the
exact-derived comparison formula identifies the initial factor with S.derived.
Unfolding the named representative maps and the tensor functor's map of the
termwise S comparison gives the displayed equation. This is the representative
chain square, before any tensor normalization or faithful descent is applied. -/
theorem podTensorMixedRepresentativeChainSquareDiagram
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
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S) :
  ∀ P, (podTensorDiagramScalarFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).map
    ((podTensorDiagramReindexChain l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) P) ≫
      (podTensorDiagramScalarChain l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)
        (((podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
          (podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)).obj P) ≫
      (podTensorDiagramTargetRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).map
        ((NatIso.prod (podTensorDiagramGoodTransition l E g D _hD T _hT L ι D' _hD' T' _hT' S
        _hcore)
          (podTensorDiagramGoodTransition l E g D _hD T _hT L ι D' _hD' T' _hT' S
        _hcore)).hom.app P)
            = (podTensorDiagramDerivedTransition l E g D _hD T _hT L ι D' _hD' T' _hT' S
              _hcore).hom.app ((podTensorDiagramSourceRepresentative l E g D _hD T _hT L ι D'
        _hD' T'
                _hT' S _hcore).obj P) ≫ (podTensorDiagramMixedChain l E g D _hD T _hT L ι D' _hD' T'
                  _hT' S _hcore) P := by
  intro P
  rw [podTensorDiagramScalarFunctor_map l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore,
    podTensorDiagramReindexChain_unfold l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore P,
    podTensorDiagramScalarChain_unfold l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore P,
    podTensorDiagramTargetRepresentative_map_transition l E g D _hD T _hT L ι D' _hD' T' _hT' S
      _hcore P,
    podTensorDiagramDerivedTransition_app_source l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore P,
    podTensorDiagramMixedChain_unfold l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore P,
    Category.assoc]
  exact podTensorMixedChainSquareCore l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
    P.1.obj P.2.obj

end WeilConjectures
