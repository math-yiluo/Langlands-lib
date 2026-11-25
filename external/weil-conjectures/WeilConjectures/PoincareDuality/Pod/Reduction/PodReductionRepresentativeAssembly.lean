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
import all WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionDescentSystem
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexUnaryModel
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexStrictTensor
import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictDerivedSquare
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.Coefficient.CoefficientReductionTensorEvaluationPasting

/-! # Pasting the reduction tensor square on specified representatives

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: lem-pod-reduction-representative-assembly)
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

private theorem map_three {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P Q R S Q' R' : C}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S}
    {d : P ⟶ Q'} {e : Q' ⟶ R'} {f : R' ⟶ S}
    (h : a ≫ b ≫ c = d ≫ e ≫ f) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e ≫ F.map f := by
  simpa only [Functor.map_comp] using congrArg (fun z ↦ F.map z) h

/-- The reduction/reindexing tensor square on flat-term K-flat representatives.
Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 07A4 and 0941.
The proof pastes the unary models with the strict tensor identity and cancels the
model isomorphisms. No finite-evaluation faithfulness is used.
(blueprint: lem-pod-reduction-representative-assembly). -/
theorem podReduction_assemble_representative
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g)
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
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hT : integralOperationsGoodComplex l E Y ((T[Y]).obj (P.obj, Q.obj)))
    (hFP : integralOperationsGoodComplex l E X ((F[g]).obj P.obj))
    (βP : (I[g]).obj ((R[Y]).obj P.obj) ≅ (R[X]).obj ((F[g]).obj P.obj))
    (hβP : Generators l E g P.obj βP)
    (hUP : (integralComparisonDerivedSequencePullback l E g).map
        ((pullbackTensorReductionModel l E Y).hom.app P) ≫
      (systemFactor l E g).hom.app ((R[Y]).obj P.obj) ≫
        (systemQ l E X).map βP.hom =
      A.reduction.hom.app ((podReindexingQ l E Y none).obj P.obj) ≫
        (podReindexCalculus l E X).reduction.map ((factor l E g h).hom.app P.obj) ≫
        (pullbackTensorReductionModel l E X).hom.app ⟨((F[g]).obj P.obj), hFP⟩)
    (hFQ : integralOperationsGoodComplex l E X ((F[g]).obj Q.obj))
    (βQ : (I[g]).obj ((R[Y]).obj Q.obj) ≅ (R[X]).obj ((F[g]).obj Q.obj))
    (hβQ : Generators l E g Q.obj βQ)
    (hUQ : (integralComparisonDerivedSequencePullback l E g).map
        ((pullbackTensorReductionModel l E Y).hom.app Q) ≫
      (systemFactor l E g).hom.app ((R[Y]).obj Q.obj) ≫
        (systemQ l E X).map βQ.hom =
      A.reduction.hom.app ((podReindexingQ l E Y none).obj Q.obj) ≫
        (podReindexCalculus l E X).reduction.map ((factor l E g h).hom.app Q.obj) ≫
        (pullbackTensorReductionModel l E X).hom.app ⟨((F[g]).obj Q.obj), hFQ⟩)
    (hFT : integralOperationsGoodComplex l E X ((F[g]).obj ((T[Y]).obj (P.obj, Q.obj))))
    (βT : (I[g]).obj ((R[Y]).obj ((T[Y]).obj (P.obj, Q.obj))) ≅
      (R[X]).obj ((F[g]).obj ((T[Y]).obj (P.obj, Q.obj))))
    (hβT : Generators l E g ((T[Y]).obj (P.obj, Q.obj)) βT)
    (hUT : (integralComparisonDerivedSequencePullback l E g).map
        ((pullbackTensorReductionModel l E Y).hom.app ⟨((T[Y]).obj (P.obj, Q.obj)), hT⟩) ≫
      (systemFactor l E g).hom.app ((R[Y]).obj ((T[Y]).obj (P.obj, Q.obj))) ≫
        (systemQ l E X).map βT.hom =
      A.reduction.hom.app ((podReindexingQ l E Y none).obj ((T[Y]).obj (P.obj, Q.obj))) ≫
        (podReindexCalculus l E X).reduction.map
          ((factor l E g h).hom.app ((T[Y]).obj (P.obj, Q.obj))) ≫
        (pullbackTensorReductionModel l E X).hom.app
          ⟨((F[g]).obj ((T[Y]).obj (P.obj, Q.obj))), hFT⟩) :
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
  let CY := podReindexCalculus l E Y
  let CX := podReindexCalculus l E X
  let G := integralComparisonDerivedSequencePullback l E g
  let D := podOrdinaryReindex l E g
  let T0 := (T[Y]).obj (P.obj, Q.obj)
  let FP : (integralOperationsGoodComplex l E X).FullSubcategory := ⟨_, hFP⟩
  let FQ : (integralOperationsGoodComplex l E X).FullSubcategory := ⟨_, hFQ⟩
  let FT : (integralOperationsGoodComplex l E X).FullSubcategory := ⟨_, hFT⟩
  let TX := (T[X]).obj (FP.obj, FQ.obj)
  let hTX := total_good l E X FP FQ
  let bY := ordinaryModel l E Y CY.integralClosed CY.integralTensorModel
    P.obj Q.obj P.property.1 Q.property.1
  let bX := ordinaryModel l E X CX.integralClosed CX.integralTensorModel
    FP.obj FQ.obj hFP.1 hFQ.1
  let fP := (factor l E g h).app P.obj
  let fQ := (factor l E g h).app Q.obj
  let fT := (factor l E g h).app T0
  let rP := (pullbackTensorReductionModel l E Y).app P
  let rQ := (pullbackTensorReductionModel l E Y).app Q
  let rT := (pullbackTensorReductionModel l E Y).app ⟨T0, hT⟩
  let rFP := (pullbackTensorReductionModel l E X).app FP
  let rFQ := (pullbackTensorReductionModel l E X).app FQ
  let rFT := (pullbackTensorReductionModel l E X).app FT
  let rTX := (pullbackTensorReductionModel l E X).app ⟨TX, hTX⟩
  let RP := (R[Y]).obj P.obj
  let RQ := (R[Y]).obj Q.obj
  let sY := systemModel l E Y RP RQ
    (pullbackTensorReductionGood l E Y P) (pullbackTensorReductionGood l E Y Q)
  let sX := systemModel l E X _ _
    (pullbackTensorReductionGood l E X FP) (pullbackTensorReductionGood l E X FQ)
  let iP := (systemFactor l E g).hom.app RP
  let iQ := (systemFactor l E g).hom.app RQ
  let iT := (systemFactor l E g).hom.app
    ((R[Y]).obj T0)
  let iS := (systemFactor l E g).hom.app
    ((S[Y]).obj (RP, RQ))
  let ψY := tensorReductionStrictMap l E Y P.obj Q.obj
  let ψX := tensorReductionStrictMap l E X FP.obj FQ.obj
  let t := c.tensorChain P.obj Q.obj
  let w := podReindexingSystemTensor l E g
  let hIP := sequence_good l E g RP (pullbackTensorReductionGood l E Y P)
  let hIQ := sequence_good l E g RQ (pullbackTensorReductionGood l E Y Q)
  have hS := system_model l E g RP RQ
    (pullbackTensorReductionGood l E Y P) (pullbackTensorReductionGood l E Y Q) hIP hIQ
  let sI := systemModel l E X _ _ hIP hIQ
  have hY := reduction_model l E Y P Q hT
  have hX := reduction_model l E X FP FQ hTX
  have hO := ordinary_model l E g c h P Q hFP hFQ
  have hN := system_naturality l E X _ _ _ _ hIP hIQ
    (pullbackTensorReductionGood l E X FP) (pullbackTensorReductionGood l E X FQ)
    βP.hom βQ.hom
  have hi := (systemFactor l E g).hom.naturality
    ψY
  have hr := (pullbackTensorReductionModel l E X).hom.naturality
    (X := FT) (Y := ⟨TX, hTX⟩) (ObjectProperty.homMk t.hom)
  have hc := strict_tensor l E g P.obj Q.obj t (hPure P.obj Q.obj)
    βP βQ βT hβP hβQ hβT
  have hc' := map_three (systemQ l E X) hc
  exact reduction_pasting CY.reduction CX.reduction D G
    CY.integralClosed.tensor CX.integralClosed.tensor
    CY.systemClosed.tensor CX.systemClosed.tensor
    A.reduction.hom (reductionOrdinaryTensor l E g c h).hom w.hom
    CY.reductionTensor.hom CX.reductionTensor.hom
    ((podReindexingQ l E Y none).obj P.obj) ((podReindexingQ l E Y none).obj Q.obj)
    ((podReindexingQ l E Y none).obj T0) ((podReindexingQ l E X none).obj FP.obj)
    ((podReindexingQ l E X none).obj FQ.obj) ((podReindexingQ l E X none).obj FT.obj)
    ((podReindexingQ l E X none).obj TX) bY bX fP fQ fT
    ((systemQ l E Y).obj RP) ((systemQ l E Y).obj RQ)
    ((systemQ l E Y).obj ((R[Y]).obj T0))
    ((systemQ l E Y).obj ((S[Y]).obj (RP, RQ)))
    ((systemQ l E X).obj ((I[g]).obj RP)) ((systemQ l E X).obj ((I[g]).obj RQ))
    ((systemQ l E X).obj ((I[g]).obj ((R[Y]).obj T0)))
    ((systemQ l E X).obj ((I[g]).obj ((S[Y]).obj (RP, RQ))))
    ((systemQ l E X).obj ((S[X]).obj (((I[g]).obj RP, (I[g]).obj RQ))))
    ((systemQ l E X).obj ((R[X]).obj FP.obj))
    ((systemQ l E X).obj ((R[X]).obj FQ.obj))
    ((systemQ l E X).obj ((R[X]).obj FT.obj))
    ((systemQ l E X).obj ((R[X]).obj TX))
    ((systemQ l E X).obj ((S[X]).obj (((R[X]).obj FP.obj, (R[X]).obj FQ.obj))))
    rP rQ rT rFP rFQ rFT rTX sY sI sX iP iQ iT iS
    ((systemQ l E Y).map ψY) ((systemQ l E X).map ((I[g]).map ψY))
    ((systemQ l E X).map ((systemChain l E g).hom.app (RP, RQ)))
    ((systemQ l E X).map βP.hom) ((systemQ l E X).map βQ.hom)
    ((systemQ l E X).map βT.hom)
    ((systemQ l E X).map ((S[X]).map (Prod.mkHom βP.hom βQ.hom)))
    ((podReindexingQ l E X none).map t.hom) ((systemQ l E X).map ((R[X]).map t.hom))
    ((systemQ l E X).map ψX) hUP hUQ hUT hY hX hO hS hN hi hr hc'

end WeilConjectures
