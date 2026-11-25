/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingReductionTensorSquare
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoosAux6
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexUnaryModel

/-! # The strict Roos normalization of the coherent tensor comparison

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The natural comparison constructed from the coherent system tensor and limit maps.
It uses no chosen completed tensor reindexing comparison.
Source: Stacks 07A4 and 0941
(blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
@[irreducible] def podReindexingLimitTensorComparisonHom
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (M N : podReindexingDerived l E Y none) :
    let q := podReindexingTensorFrame l E g A hA M N
    q.F.obj q.CY ⟶ q.CX :=
  let q := podReindexingTensorFrame l E g A hA M N
  q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map q.w₁ ≫ q.RX.map q.w₂ ≫ q.dX.inv

-- The proof assembles several large strict and derived equations.
/-- On good complexes, the coherent tensor comparison is the prescribed strict Roos map.
This is a calculation before descent: there is no constructibility assumption and
neither `T.tensor`, its Model law, nor its derived naturality occurs in the equation.

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC, 0941.
Proof: expand the representative normalizations of the two tensor realizations.
Their reduction models identify the coherent system tensor with the total tensor of
the two ordinary quotient complexes, and their strict tower comparisons identify
its restriction with the finite tensor tower. Apply A's LimitModel equation to
this coherent total tensor. The naturality of its Roos comparison moves the strict
tower identifications across that equation. The whole-system unit law fixes
A.reduction as the mate of A.limit. The FiniteModel and QuotientGenerators laws
therefore identify its two quotient factors with A.quotient on every scalar-tensor
generator. The normalized system tensor comparison takes a total-tensor generator
to the tensor of its two inverse images. Consequently the induced tower arrow
agrees with T.tower by hGenerators: use the balanced tensor universal property on
each summand, the total direct-sum universal property in each degree, and then
natural-transformation extensionality on the tower. These are equalities of entire
chain maps; quotient transitions are retained. Applying the Roos functor and Q,
and cancelling the intermediate realization isomorphisms, gives the displayed
identity. The target factor is the ordinary inverse-image localization comparison
on each of P and Q, followed by the specified tensor realization. The argument
also applies to zero complexes and the empty scheme.
(blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem podReindexing_tensor_roos_normalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (_hGenerators : PodCompletedTensorReindex.Generators l E g A T)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    letI : (isoReductionIntegralInverse l E g).Additive :=
      isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
    HEq (podReindexingLimitTensorComparisonHom l E g A hA
        (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj) ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj)
          ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
      (integralCompletedTensorComparison l E X).hom.app
        ((podGoodReindex l E g A).obj P, (podGoodReindex l E g A).obj Q))
      ((podOrdinaryReindex l E g).map
        ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map
        ((A.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).hom ≫
          integralOperationsRoosFunctor.map (T.tower P Q).hom)) := by
  have h := podReindexingDerivedFunctor_none_eq l E g
  have hP := PodReductionRepresentatives.unary_model l E g A hA h P
  have hQ := PodReductionRepresentatives.unary_model l E g A hA h Q
  let hFP := hP.choose
  let hFQ := hQ.choose
  let βP := hP.choose_spec.choose
  let βQ := hQ.choose_spec.choose
  have hβP := hP.choose_spec.choose_spec.1
  have hβQ := hQ.choose_spec.choose_spec.1
  have hUP := hP.choose_spec.choose_spec.2
  have hUQ := hQ.choose_spec.choose_spec.2
  have hσ := podReindexing_systemTensor_chainModel l E g A P Q _ _
    (podReductionUnary_transport l E g A h P hFP βP hUP)
    (podReductionUnary_transport l E g A h Q hFQ βQ hUQ)
  have hτ := podCoherentTower_eq l E g A T hA _hGenerators P Q βP βQ hβP hβQ
  have hroos := (podReindexing_tensor_roos_of_strict l E g A hA P Q (T.tower P Q)
    ((PodReductionRepresentatives.systemChain l E g).hom.app
      (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj,
        ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj Q.obj) ≫
      (coefficientTotalTensor.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)).map (Prod.mkHom
          (βP ≪≫ ((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).mapIso
            (podReindexComplexIso l E g P.obj)).hom
          (βQ ≪≫ ((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).mapIso
            (podReindexComplexIso l E g Q.obj)).hom)) hσ hτ)
  apply heq_of_eq
  unfold podReindexingLimitTensorComparisonHom
  refine Eq.trans ?_ hroos
  simp only [Category.assoc]
  rfl

end WeilConjectures
