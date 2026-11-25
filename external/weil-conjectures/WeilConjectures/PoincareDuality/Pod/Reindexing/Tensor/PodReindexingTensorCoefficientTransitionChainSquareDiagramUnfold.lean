/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorDescentDiagram

/-! # Unfolding the fixed scalar/reindexing tensor diagram on representatives

The chains and transitions of the fixed tensor diagram, rewritten as the explicit derived maps
of their representative chain maps.
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

attribute [local irreducible] integralOperationsTensorTowerFunctor

attribute [local implicit_reducible] podTensorDiagramReindexFunctor
  podTensorDiagramReindexRepresentative podTensorDiagramSourceRepresentative
  podTensorDiagramTargetRepresentative podTensorDiagramScalarFunctor
  podTensorDiagramMixedFunctor podTensorDiagramGoodReindex podTensorDiagramGoodScalar
  podTensorDiagramGoodMixed podTensorDiagramGoodInclusion podTensorDiagramGoodTransition
  podTensorDiagramPairReindex podTensorDiagramPairScalar podTensorDiagramPairMixed
  podTensorDiagramDerivedTransition podTensorDiagramPairTransition


/-- The scalar functor of the diagram acts by the derived scalar extension.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
theorem podTensorDiagramScalarFunctor_map
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
    {M N : DerivedCategory (scalarReductionSource l E X)} (x : M ⟶ N) :
    (podTensorDiagramScalarFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).map x =
      (integralOrdinaryScalar l E L ι X).mapDerivedCategory.map x := rfl

/-- The reindexing chain of the diagram on a pair of representatives.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
theorem podTensorDiagramReindexChain_unfold
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
    (P : (podTensorGoodConstructible l E Y).FullSubcategory ×
      (podTensorGoodConstructible l E Y).FullSubcategory) :
    (podTensorDiagramReindexChain l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) P =
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app
        ((integralOperationsTensorComplexFunctor l E Y).obj (P.1.obj.obj, P.2.obj.obj)) ≫
      DerivedCategory.Q.map (podReindexTensorChain l E g D T P.1.obj P.2.obj) := rfl

/-- The scalar chain of the diagram on the reindexed pair of representatives.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
theorem podTensorDiagramScalarChain_unfold
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
    (P : (podTensorGoodConstructible l E Y).FullSubcategory ×
      (podTensorGoodConstructible l E Y).FullSubcategory) :
    (podTensorDiagramScalarChain l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)
      (((podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
        (podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)).obj P) =
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
        ((integralOperationsTensorComplexFunctor l E X).obj
          (((podGoodReindex l E g D).obj P.1.obj).obj,
          ((podGoodReindex l E g D).obj P.2.obj).obj)) ≫
      DerivedCategory.Q.map (scalarTensorChain l E L ι X ((podGoodReindex l E g D).obj P.1.obj).obj
        ((podGoodReindex l E g D).obj P.2.obj).obj) := rfl

/-- The target representative of the pair of good coefficient transitions.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
theorem podTensorDiagramTargetRepresentative_map_transition
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
    (P : (podTensorGoodConstructible l E Y).FullSubcategory ×
      (podTensorGoodConstructible l E Y).FullSubcategory) :
    (podTensorDiagramTargetRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S
      _hcore).map ((NatIso.prod (podTensorDiagramGoodTransition l E g D _hD T _hT L ι D' _hD' T'
        _hT' S _hcore) (podTensorDiagramGoodTransition l E g D _hD T _hT L ι D' _hD' T' _hT' S
        _hcore)).hom.app P) =
      DerivedCategory.Q.map ((integralOperationsTensorComplexFunctor l L X).map (Prod.mkHom
        ((S.complex l E g L ι D D').hom.app P.1.obj.obj)
        ((S.complex l E g L ι D D').hom.app P.2.obj.obj))) := rfl

/-- The derived transition of the diagram at a source representative.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
theorem podTensorDiagramDerivedTransition_app_source
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
    (P : (podTensorGoodConstructible l E Y).FullSubcategory ×
      (podTensorGoodConstructible l E Y).FullSubcategory) :
    (podTensorDiagramDerivedTransition l E g D _hD T _hT L ι D' _hD' T' _hT' S
      _hcore).hom.app ((podTensorDiagramSourceRepresentative l E g D _hD T _hT L ι D' _hD' T'
        _hT' S _hcore).obj P) =
      (((isoReductionIntegralInverse l E g).mapDerivedCategoryCompIso
          (integralOrdinaryScalar l E L ι X)) ≪≫
        mapDerivedCategoryNatIso S.ordinary ≪≫
        ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryCompIso
          (isoReductionIntegralInverse l L g)).symm).hom.app
          (DerivedCategory.Q.obj
            ((integralOperationsTensorComplexFunctor l E Y).obj (P.1.obj.obj, P.2.obj.obj))) :=
  rfl

/-- The mixed chain of the diagram on a pair of representatives.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: def-pod-tensor-descent-diagram). -/
theorem podTensorDiagramMixedChain_unfold
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
    (P : (podTensorGoodConstructible l E Y).FullSubcategory ×
      (podTensorGoodConstructible l E Y).FullSubcategory) :
    (podTensorDiagramMixedChain l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) P =
      (isoReductionIntegralInverse l L g).mapDerivedCategory.map
        ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E Y).obj (P.1.obj.obj, P.2.obj.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E L ι Y P.1.obj.obj P.2.obj.obj)) ≫
      (isoReductionIntegralInverse l L g).mapDerivedCategoryFactors.hom.app
          ((integralOperationsTensorComplexFunctor l L Y).obj
            (((podTensorScalarGoodFunctor l E L ι Y).obj P.1.obj).obj,
              ((podTensorScalarGoodFunctor l E L ι Y).obj P.2.obj).obj)) ≫
        DerivedCategory.Q.map (podReindexTensorChain l L g D' T'
          ((podTensorScalarGoodFunctor l E L ι Y).obj P.1.obj)
          ((podTensorScalarGoodFunctor l E L ι Y).obj P.2.obj)) := rfl

end WeilConjectures
