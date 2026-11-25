/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionDescentSystem
public import WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionRepresentativeModels
import all WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionRepresentativeModels
import WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionRepresentativeAssembly
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexUnaryModel

/-! # The reduction tensor square on good representatives

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: lem-pod-reduction-good-representative-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance 1000000] SheafOfModules.instAbelian

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh CoefficientClosedStructure.tensor
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
  pullbackTensorReductionModel pullbackTensorSystemModel
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite
  derivedInternalHomOfUniverses coefficientSequenceCommRingSheaf
  pullbackTensorSequenceInverse integralComparisonSequencePullback
  pullbackTensorSystemComparison PodReductionRepresentatives.systemChain
attribute [local implicit_reducible] CategoryTheory.uniformProd
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  coefficientIntegralInternalHom coefficientSequenceInternalHom coefficientFiniteInternalHom
  podReindexCalculus pullbackTensorCalculus
  integralTowerHasDerivedCategory coefficientSequenceHasDerived
  pullbackTensorSequenceDerived
  integralComparisonDerivedSequencePullback

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open PodReductionRepresentatives

set_option quotPrecheck false in
set_option hygiene false in
local notation "R[" W "]" =>
  (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "I[" g "]" =>
  (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "F[" g "]" => podReindexingComplexFunctor l E g none
set_option quotPrecheck false in
set_option hygiene false in
local notation "T[" W "]" => PodReindexingCoherence.total l E W none
set_option quotPrecheck false in
set_option hygiene false in
local notation "S[" W "]" => coefficientTotalTensor.{u, u + 1, u}
  (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)

attribute [local instance 10000000] HasDerivedCategory.standard
attribute [local irreducible] podOrdinaryReindex PodReductionRepresentatives.factor
set_option allowUnsafeReducibility true in
attribute [local irreducible] podReindexingDerivedFunctor podReindexingDerivedFactors
open PodReindexingCoherence

/-- The reduction/reindexing tensor square on flat-term K-flat representatives.
Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 07A4 and 0941.
The proof pastes the unary models with the strict tensor identity and cancels the
model isomorphisms. No finite-evaluation faithfulness is used.
(blueprint: lem-pod-reduction-good-representative-square). -/
theorem podReduction_representative_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g)
    (hA : PodCompletionReindex.Laws l E g A)
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (hPure : ∀ (P L : PodReindexingCoherence.K l E Y none) (p q k : ℤ)
      (hk : p + q = k) (U : X.ProEt)
      (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (L.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((c.tensorChain P L).hom.f k).val.app (op U))
        (coefficientTensorGenerator.{u, u + 1, u}
          (ProEt.topology Y) (podReindexingRing l E Y none) P L p q k hk
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      coefficientTensorGenerator.{u, u + 1, u}
        (ProEt.topology X) (podReindexingRing l E X none)
        ((podReindexingComplexFunctor l E g none).obj P)
        ((podReindexingComplexFunctor l E g none).obj L) p q k hk
        (op U) x y)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (integralComparisonDerivedSequencePullback l E g).map
        ((podReindexCalculus l E Y).reductionTensor.hom.app ((podReindexingQ l E Y none).obj P.obj,
          (podReindexingQ l E Y none).obj Q.obj)) ≫
      (podReindexingSystemTensor l E g).hom.app
        ((podReindexCalculus l E Y).reduction.obj ((podReindexingQ l E Y none).obj P.obj),
          (podReindexCalculus l E Y).reduction.obj ((podReindexingQ l E Y none).obj Q.obj)) ≫
      (podReindexCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          (A.reduction.hom.app ((podReindexingQ l E Y none).obj P.obj))
          (A.reduction.hom.app ((podReindexingQ l E Y none).obj Q.obj))) =
    A.reduction.hom.app
        ((podReindexCalculus l E Y).integralClosed.tensor.obj
          ((podReindexingQ l E Y none).obj P.obj,
          (podReindexingQ l E Y none).obj Q.obj)) ≫
      (podReindexCalculus l E X).reduction.map
        ((reductionOrdinaryTensor l E g c h).hom.app
          ((podReindexingQ l E Y none).obj P.obj, (podReindexingQ l E Y none).obj Q.obj)) ≫
      (podReindexCalculus l E X).reductionTensor.hom.app
        ((podOrdinaryReindex l E g).obj ((podReindexingQ l E Y none).obj P.obj),
          (podOrdinaryReindex l E g).obj ((podReindexingQ l E Y none).obj Q.obj)) := by
  let T0 := (T[Y]).obj (P.obj, Q.obj)
  have hT := total_good l E Y P Q
  obtain ⟨hFP, βP, hβP, hUP⟩ := unary_model l E g A hA h P
  obtain ⟨hFQ, βQ, hβQ, hUQ⟩ := unary_model l E g A hA h Q
  obtain ⟨hFT, βT, hβT, hUT⟩ := unary_model l E g A hA h ⟨T0, hT⟩
  exact podReduction_assemble_representative l E g A c h hPure P Q hT
    hFP βP hβP hUP hFQ βQ hβQ hUQ hFT βT hβT hUT

end WeilConjectures
