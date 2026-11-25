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
import all WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionDescentSystem
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
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

/-! # Representative comparison models for reduction descent

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: def-pod-reduction-representative-models)
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

private theorem component_normalize {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) (F G : C ⥤ D) (e : F ≅ G)
    (c : T ⋙ F ≅ F.prod F ⋙ U)
    {P Q V : C} {P' Q' : D} (b : V ⟶ T.obj (P, Q))
    (fP : G.obj P ⟶ P') (fQ : G.obj Q ⟶ Q')
    (r : F.obj V ⟶ U.obj (P', Q'))
    (h : F.map b ≫ c.hom.app (P, Q) ≫
      U.map (Prod.mkHom (e.hom.app P ≫ fP) (e.hom.app Q ≫ fQ)) = r) :
    G.map b ≫ ((e.app (T.obj (P, Q))).symm ≪≫ c.app (P, Q) ≪≫
      U.mapIso ((e.app P).prod (e.app Q))).hom ≫
      U.map (Prod.mkHom fP fQ) = e.inv.app V ≫ r := by
  simp only [Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
    Functor.mapIso_hom, Iso.prod_hom, Category.assoc]
  rw [← U.map_comp]
  change G.map b ≫ e.inv.app _ ≫ c.hom.app _ ≫
    U.map (Prod.mkHom (e.hom.app P ≫ fP) (e.hom.app Q ≫ fQ)) = _
  rw [reassoc_of% (e.inv.naturality b), h]

private theorem ordinary_normalize
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    (q : C₀ ⥤ C) (r : D₀ ⥤ D) (T₀ : C₀ × C₀ ⥤ C₀)
    (T : C × C ⥤ C) (U : D × D ⥤ D)
    (F₀ : C₀ ⥤ D₀) (F G : C ⥤ D) (e : F ≅ G)
    (a : q ⋙ F ≅ F₀ ⋙ r) (c : T ⋙ F ≅ F.prod F ⋙ U)
    (P Q : C₀) (Z : D₀) (t : F₀.obj (T₀.obj (P, Q)) ⟶ Z)
    (bY : q.obj (T₀.obj (P, Q)) ≅ T.obj (q.obj P, q.obj Q))
    (bX : r.obj Z ≅ U.obj (r.obj (F₀.obj P), r.obj (F₀.obj Q)))
    (hm : F.map bY.hom ≫ c.hom.app (q.obj P, q.obj Q) ≫
      U.map (Prod.mkHom (a.hom.app P) (a.hom.app Q)) =
      a.hom.app (T₀.obj (P, Q)) ≫ r.map t ≫ bX.hom) :
    G.map bY.hom ≫ ((e.app (T.obj (q.obj P, q.obj Q))).symm ≪≫
      c.app (q.obj P, q.obj Q) ≪≫
      U.mapIso ((e.app (q.obj P)).prod (e.app (q.obj Q)))).hom ≫
      U.map (Prod.mkHom
        ((reductionFactorOfIso q r F₀ F G e a).hom.app P)
        ((reductionFactorOfIso q r F₀ F G e a).hom.app Q)) =
    (reductionFactorOfIso q r F₀ F G e a).hom.app (T₀.obj (P, Q)) ≫
      r.map t ≫ bX.hom := by
  have hc := component_normalize T U F G e c bY.hom
    ((reductionFactorOfIso q r F₀ F G e a).hom.app P)
    ((reductionFactorOfIso q r F₀ F G e a).hom.app Q)
    (a.hom.app (T₀.obj (P, Q)) ≫ r.map t ≫ bX.hom) (by
      simpa only [reductionFactorOfIso_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
        Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
        Category.assoc, Iso.hom_inv_id_app_assoc] using hm)
  simpa only [reductionFactorOfIso_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] using hc

private def ordinaryModel (W : Scheme.{u}) (S : Closed l E W none)
    (T : Models l E W none S) (P Q : K l E W none)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology W) (R := podReindexingRing l E W none) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology W) (R := podReindexingRing l E W none) Q) :
    (podReindexingQ l E W none).obj ((total l E W none).obj (P, Q)) ≅
      S.tensor.obj ((podReindexingQ l E W none).obj P,
        (podReindexingQ l E W none).obj Q) :=
  T.comparison.app (⟨P, hP⟩, ⟨Q, hQ⟩)

private theorem ordinary_model_base {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (SX : Closed l E X none) (SY : Closed l E Y none)
    (TX : Models l E X none SX) (TY : Models l E Y none SY)
    (c : Comparison l E g none SX SY TX TY)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (P Q : K l E Y none)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := podReindexingRing l E Y none) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := podReindexingRing l E Y none) Q)
    (hFP : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := podReindexingRing l E X none)
      ((podReindexingComplexFunctor l E g none).obj P))
    (hFQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := podReindexingRing l E X none)
      ((podReindexingComplexFunctor l E g none).obj Q)) :
    (podOrdinaryReindex l E g).map (ordinaryModel l E Y SY TY P Q hP hQ).hom ≫
      (((eqToIso h).app (SY.tensor.obj
        ((podReindexingQ l E Y none).obj P, (podReindexingQ l E Y none).obj Q))).symm ≪≫
        c.tensor.app ((podReindexingQ l E Y none).obj P,
          (podReindexingQ l E Y none).obj Q) ≪≫
        SX.tensor.mapIso (((eqToIso h).app ((podReindexingQ l E Y none).obj P)).prod
          ((eqToIso h).app ((podReindexingQ l E Y none).obj Q)))).hom ≫
      SX.tensor.map (Prod.mkHom ((factor l E g h).hom.app P)
        ((factor l E g h).hom.app Q)) =
    (factor l E g h).hom.app ((total l E Y none).obj (P, Q)) ≫
      (podReindexingQ l E X none).map (c.tensorChain P Q).hom ≫
      (ordinaryModel l E X SX TX _ _ hFP hFQ).hom := by
  obtain ⟨hFP', hFQ', hm⟩ := c.tensor_model P Q hP hQ
  change (podReindexingDerivedFunctor l E g none).map
      (ordinaryModel l E Y SY TY P Q hP hQ).hom ≫ c.tensor.hom.app _ ≫
      SX.tensor.map (Prod.mkHom ((podReindexingDerivedFactors l E g none).hom.app P)
        ((podReindexingDerivedFactors l E g none).hom.app Q)) =
    (podReindexingDerivedFactors l E g none).hom.app ((total l E Y none).obj (P, Q)) ≫
      (podReindexingQ l E X none).map (c.tensorChain P Q).hom ≫
      (ordinaryModel l E X SX TX _ _ hFP hFQ).hom at hm
  unfold factor
  exact ordinary_normalize (podReindexingQ l E Y none) (podReindexingQ l E X none)
    (total l E Y none) SY.tensor SX.tensor (podReindexingComplexFunctor l E g none)
    (podReindexingDerivedFunctor l E g none) (podOrdinaryReindex l E g) (eqToIso h)
    (podReindexingDerivedFactors l E g none) c.tensor P Q _ (c.tensorChain P Q).hom
    (ordinaryModel l E Y SY TY P Q hP hQ) (ordinaryModel l E X SX TX _ _ hFP hFQ) hm

private theorem sequence_good {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E Y) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E X) ((I[g]).obj P) := by
  let e := NatIso.mapHomologicalComplex (eqToIso (inverse_eq l E g)) (.up ℤ)
  exact SheafOfModules.kFlat_iso_independent _ (e.app P)
    (pullbackTensorSequenceGood l E g P hP)

private theorem total_eq (W : Scheme.{u}) : (T[W]) =
    SheafOfModules.KFlatTotalTensorModel.total
      (completedIntegralCommRingSheafUnrestricted l E W) := by
  unfold PodReindexingCoherence.total coefficientTotalTensor
    SheafOfModules.KFlatTotalTensorModel.total SheafOfModules.KFlatTotalTensorModel.tensor
    SheafOfModules.KFlatTotalTensorModel.monoidal
  rfl

private theorem total_good (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    integralOperationsGoodComplex l E W ((T[W]).obj (P.obj, Q.obj)) := by
  have ht := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (completedIntegralCommRingSheafUnrestricted l E W) P.obj Q.obj
    P.property.1 Q.property.1 P.property.2 Q.property.2
  rw [total_eq l E W]
  exact ⟨ht.1, ht.2.1⟩

/-- Conjugate a tensor comparison componentwise along a functor isomorphism.
Source: naturality of composition of natural isomorphisms, Stacks 05RU.
(blueprint: def-pod-reduction-representative-models). -/
@[irreducible] def reductionObjectConjugate {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) (F G : C ⥤ D) (e : F ≅ G)
    (c : T ⋙ F ≅ F.prod F ⋙ U) : T ⋙ G ≅ G.prod G ⋙ U :=
  NatIso.ofComponents (fun Z ↦ (e.app (T.obj Z)).symm ≪≫ c.app Z ≪≫
    U.mapIso ((e.app Z.1).prod (e.app Z.2))) (by
    intro P Q f
    have hn := (Functor.isoWhiskerLeft T e.symm ≪≫ c ≪≫
      Functor.isoWhiskerRight (NatIso.prod e e) U).hom.naturality f
    simpa only [Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatIso.prod, NatTrans.prod, Iso.prod_hom, Functor.mapIso_hom] using hn)

/-- The ordinary tensor comparison with its objectwise equality transport.
Source: the canonical normalized tensor arrow, Stacks 07A4.
(blueprint: def-pod-reduction-representative-models). -/
@[irreducible] def reductionOrdinaryTensorRaw {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g) :=
  reductionObjectConjugate (podReindexCalculus l E Y).integralClosed.tensor
    (podReindexCalculus l E X).integralClosed.tensor
    (podReindexingDerivedFunctor l E g none) (podOrdinaryReindex l E g) (eqToIso h) c.tensor

/-- The transported comparison has the original normalized ordinary tensor component.
Source: the component construction, Stacks 07A4.
(blueprint: def-pod-reduction-representative-models). -/
theorem reductionOrdinaryTensorRaw_hom {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (M N : podReindexingDerived l E Y none) :
    (reductionOrdinaryTensorRaw l E g c h).hom.app (M, N) =
      podReindexingIntegralTensorHom l E g c h M N := by
  unfold reductionOrdinaryTensorRaw reductionObjectConjugate podReindexingIntegralTensorHom
  rfl

/-- Retain an isomorphism inverse while fixing its hom by a proved equality.
Source: the isomorphism laws, Stacks 05RU.
(blueprint: def-pod-reduction-representative-models). -/
def reductionIsoWithHom {C : Type*} [Category C] {X Y : C}
    (e : X ≅ Y) (f : X ⟶ Y) (h : f = e.hom) : X ≅ Y where
  hom := f
  inv := e.inv
  hom_inv_id := by rw [h]; exact e.hom_inv_id
  inv_hom_id := by rw [h]; exact e.inv_hom_id

/-- Componentwise ordinary tensor comparison, with the canonical arrow as its hom.
Source: equality transport and naturality, Stacks 07A4 and 05RU.
(blueprint: def-pod-reduction-representative-models). -/
@[irreducible] def reductionOrdinaryTensor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g) :=
  NatIso.ofComponents
    (fun Z ↦ reductionIsoWithHom ((reductionOrdinaryTensorRaw l E g c h).app Z)
      (podReindexingIntegralTensorHom l E g c h Z.1 Z.2)
      (reductionOrdinaryTensorRaw_hom l E g c h Z.1 Z.2).symm)
    (by
      intro P Q f
      change (podOrdinaryReindex l E g).map
          ((podReindexCalculus l E Y).integralClosed.tensor.map f) ≫
          podReindexingIntegralTensorHom l E g c h Q.1 Q.2 =
        podReindexingIntegralTensorHom l E g c h P.1 P.2 ≫ _
      rw [← reductionOrdinaryTensorRaw_hom, ← reductionOrdinaryTensorRaw_hom]
      exact (reductionOrdinaryTensorRaw l E g c h).hom.naturality f)

private theorem reductionOrdinaryTensor_hom {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (M N : podReindexingDerived l E Y none) :
    (reductionOrdinaryTensor l E g c h).hom.app (M, N) =
      podReindexingIntegralTensorHom l E g c h M N := by
  unfold reductionOrdinaryTensor
  rfl

private theorem ordinary_model {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hFP : integralOperationsGoodComplex l E X ((F[g]).obj P.obj))
    (hFQ : integralOperationsGoodComplex l E X ((F[g]).obj Q.obj)) :
    (podOrdinaryReindex l E g).map
        (ordinaryModel l E Y (podReindexCalculus l E Y).integralClosed
          (podReindexCalculus l E Y).integralTensorModel
          P.obj Q.obj P.property.1 Q.property.1).hom ≫
      (reductionOrdinaryTensor l E g c h).hom.app
        ((podReindexingQ l E Y none).obj P.obj, (podReindexingQ l E Y none).obj Q.obj) ≫
      (podReindexCalculus l E X).integralClosed.tensor.map
        (Prod.mkHom ((factor l E g h).hom.app P.obj) ((factor l E g h).hom.app Q.obj)) =
    (factor l E g h).hom.app ((T[Y]).obj (P.obj, Q.obj)) ≫
      (podReindexingQ l E X none).map (c.tensorChain P.obj Q.obj).hom ≫
      (ordinaryModel l E X (podReindexCalculus l E X).integralClosed
        (podReindexCalculus l E X).integralTensorModel
        ((F[g]).obj P.obj) ((F[g]).obj Q.obj) hFP.1 hFQ.1).hom := by
  rw [reductionOrdinaryTensor_hom, ← reductionOrdinaryTensorRaw_hom]
  unfold reductionOrdinaryTensorRaw reductionObjectConjugate
  exact ordinary_model_base l E g _ _ _ _ c h P.obj Q.obj
    P.property.1 Q.property.1 hFP.1 hFQ.1

private theorem reduction_model (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (hT : integralOperationsGoodComplex l E W ((T[W]).obj (P.obj, Q.obj))) :
    (podReindexCalculus l E W).reduction.map
        (ordinaryModel l E W (podReindexCalculus l E W).integralClosed
          (podReindexCalculus l E W).integralTensorModel
          P.obj Q.obj P.property.1 Q.property.1).hom ≫
      (podReindexCalculus l E W).reductionTensor.hom.app
        ((podReindexingQ l E W none).obj P.obj, (podReindexingQ l E W none).obj Q.obj) ≫
      (podReindexCalculus l E W).systemClosed.tensor.map
        (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
          ((pullbackTensorReductionModel l E W).hom.app Q)) =
    (pullbackTensorReductionModel l E W).hom.app ⟨(T[W]).obj (P.obj, Q.obj), hT⟩ ≫
      (systemQ l E W).map (tensorReductionStrictMap l E W P.obj Q.obj) ≫
      (systemModel l E W _ _
        (pullbackTensorReductionGood l E W P) (pullbackTensorReductionGood l E W Q)).hom := by
  exact tensorReductionStrictMap_derived_square l E W P Q hT

private theorem good_representative (W : Scheme.{u})
    (K : podReindexingDerived l E W none) :
    ∃ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      Nonempty ((podReindexingQ l E W none).obj P.obj ≅ K) := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E W none)
  let q : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      podReindexingDerived l E W none :=
    (integralOperationsGoodComplex l E W).ι ⋙ podReindexingQ l E W none
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  let : q.IsLocalization V := goodComplexes_isLocalization
    (completedIntegralCommRingSheafUnrestricted l E W)
    (integralOperationsGoodComplex l E W) (fun _ ↦ Iff.rfl)
  let : q.EssSurj := Localization.essSurj q V
  exact ⟨q.objPreimage K, ⟨q.objObjPreimageIso K⟩⟩

private theorem tensor_isIso {C D : Type*} [Category C] [Category D]
    (U : C × C ⥤ D) {P Q P' Q' : C} (eP : P ≅ P') (eQ : Q ≅ Q') :
    IsIso (U.map (Prod.mkHom eP.hom eQ.hom)) := by
  change IsIso ((U.mapIso (eP.prod eQ)).hom)
  infer_instance

private theorem reduction_pasting
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (R : C ⥤ A) (S : D ⥤ B) (F : C ⥤ D) (G : A ⥤ B)
    (T : C × C ⥤ C) (W : D × D ⥤ D)
    (U : A × A ⥤ A) (V : B × B ⥤ B)
    (a : R ⋙ G ⟶ F ⋙ S) (v : T ⋙ F ⟶ F.prod F ⋙ W)
    (w : U ⋙ G ⟶ G.prod G ⋙ V)
    (τY : T ⋙ R ⟶ R.prod R ⋙ U) (τX : W ⋙ S ⟶ S.prod S ⋙ V)
    (P Q T₀ : C) (PX QX FT TX : D)
    (bY : T₀ ≅ T.obj (P, Q)) (bX : TX ≅ W.obj (PX, QX))
    (fP : F.obj P ≅ PX) (fQ : F.obj Q ≅ QX) (fT : F.obj T₀ ≅ FT)
    (RP RQ RT SY : A) (IP IQ IT IS SI RFP RFQ RFT RTX SX : B)
    (rP : R.obj P ≅ RP) (rQ : R.obj Q ≅ RQ) (rT : R.obj T₀ ≅ RT)
    (rFP : S.obj PX ≅ RFP) (rFQ : S.obj QX ≅ RFQ)
    (rFT : S.obj FT ≅ RFT) (rTX : S.obj TX ≅ RTX)
    (sY : SY ≅ U.obj (RP, RQ)) (sI : SI ≅ V.obj (IP, IQ))
    (sX : SX ≅ V.obj (RFP, RFQ))
    (iP : G.obj RP ⟶ IP) (iQ : G.obj RQ ⟶ IQ)
    (iT : G.obj RT ⟶ IT) (iS : G.obj SY ⟶ IS)
    (ψY : RT ⟶ SY) (IψY : IT ⟶ IS) (systemt : IS ⟶ SI)
    (βP : IP ⟶ RFP) (βQ : IQ ⟶ RFQ) (βT : IT ⟶ RFT)
    (tensorβ : SI ⟶ SX) (t : FT ⟶ TX) (Rt : RFT ⟶ RTX) (ψX : RTX ⟶ SX)
    (hUP : G.map rP.hom ≫ iP ≫ βP = a.app P ≫ S.map fP.hom ≫ rFP.hom)
    (hUQ : G.map rQ.hom ≫ iQ ≫ βQ = a.app Q ≫ S.map fQ.hom ≫ rFQ.hom)
    (hUT : G.map rT.hom ≫ iT ≫ βT = a.app T₀ ≫ S.map fT.hom ≫ rFT.hom)
    (hY : R.map bY.hom ≫ τY.app (P, Q) ≫ U.map (Prod.mkHom rP.hom rQ.hom) =
      rT.hom ≫ ψY ≫ sY.hom)
    (hX : S.map bX.hom ≫ τX.app (PX, QX) ≫ V.map (Prod.mkHom rFP.hom rFQ.hom) =
      rTX.hom ≫ ψX ≫ sX.hom)
    (hO : F.map bY.hom ≫ v.app (P, Q) ≫ W.map (Prod.mkHom fP.hom fQ.hom) =
      fT.hom ≫ t ≫ bX.hom)
    (hS : G.map sY.hom ≫ w.app (RP, RQ) ≫ V.map (Prod.mkHom iP iQ) =
      iS ≫ systemt ≫ sI.hom)
    (hN : tensorβ ≫ sX.hom = sI.hom ≫ V.map (Prod.mkHom βP βQ))
    (hi : G.map ψY ≫ iS = iT ≫ IψY)
    (hr : S.map t ≫ rTX.hom = rFT.hom ≫ Rt)
    (hc : IψY ≫ systemt ≫ tensorβ = βT ≫ Rt ≫ ψX) :
    G.map (τY.app (P, Q)) ≫ w.app (R.obj P, R.obj Q) ≫
      V.map (Prod.mkHom (a.app P) (a.app Q)) =
    a.app (T.obj (P, Q)) ≫ S.map (v.app (P, Q)) ≫
      τX.app (F.obj P, F.obj Q) := by
  have hw := w.naturality (Prod.mkHom rP.hom rQ.hom)
  have ha := a.naturality bY.hom
  have hd := τX.naturality (Prod.mkHom fP.hom fQ.hom)
  dsimp only [Functor.comp_map, Functor.prod_map] at hw ha hd
  let pre := G.map (R.map bY.hom)
  let post := V.map (Prod.mkHom (S.map fP.hom ≫ rFP.hom)
    (S.map fQ.hom ≫ rFQ.hom))
  have : IsIso post := tensor_isIso V (S.mapIso fP ≪≫ rFP) (S.mapIso fQ ≪≫ rFQ)
  apply (cancel_epi pre).1
  apply (cancel_mono post).1
  have hL : pre ≫ G.map (τY.app (P, Q)) ≫ w.app (R.obj P, R.obj Q) ≫
        V.map (Prod.mkHom (a.app P) (a.app Q)) ≫ post =
      G.map rT.hom ≫ iT ≫ IψY ≫ systemt ≫ tensorβ ≫ sX.hom := by
    dsimp only [pre, post]
    conv_lhs =>
      rhs; rhs; rhs
      rw [tensor_comp]
    rw [← hUP, ← hUQ]
    rw [← tensor_comp V (G.map rP.hom) (G.map rQ.hom) (iP ≫ βP) (iQ ≫ βQ)]
    rw [← reassoc_of% hw, ← G.map_comp_assoc, ← G.map_comp_assoc]
    simp only [Category.assoc]
    rw [hY]
    simp only [Functor.map_comp, Category.assoc]
    rw [← tensor_comp V iP iQ βP βQ]
    rw [reassoc_of% hS, reassoc_of% hi, ← hN]
  have hR : pre ≫ a.app (T.obj (P, Q)) ≫ S.map (v.app (P, Q)) ≫
        τX.app (F.obj P, F.obj Q) ≫ post =
      G.map rT.hom ≫ iT ≫ βT ≫ Rt ≫ ψX ≫ sX.hom := by
    dsimp only [pre, post]
    rw [← tensor_comp V (S.map fP.hom) (S.map fQ.hom) rFP.hom rFQ.hom]
    rw [← reassoc_of% hd, reassoc_of% ha]
    rw [← S.map_comp_assoc, ← S.map_comp_assoc]
    simp only [Category.assoc]
    rw [hO]
    simp only [Functor.map_comp, Category.assoc]
    rw [hX, reassoc_of% hr, ← reassoc_of% hUT]
  have hc' := congrArg (fun z ↦ G.map rT.hom ≫ iT ≫ z ≫ sX.hom) hc
  simp only [Category.assoc] at hc'
  simpa only [Category.assoc] using hL.trans (hc'.trans hR.symm)

attribute [local instance 10000000] HasDerivedCategory.standard

end WeilConjectures
