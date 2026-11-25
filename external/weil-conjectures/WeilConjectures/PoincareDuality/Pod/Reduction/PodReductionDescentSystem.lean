/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
import all WeilConjectures.SixFunctors.Coefficient.CoefficientReductionTensorEvaluationPasting

/-! # Descent of the strict reduction/tensor representative square

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: lem-pod-reindexing-reduction-tensor-square-descent)
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

/-- The two presentations use the same sequence inverse image.
Source: Stacks 03D2 and 0941
(blueprint: lem-pod-reindexing-reduction-tensor-square-descent). -/
theorem podReindexing_sequence_pullback_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pullbackTensorSequenceDerived l E g = integralComparisonDerivedSequencePullback l E g := by
  exact PodReductionRepresentatives.derived_eq l E g

/-- The existing system tensor comparison, transported only by equality of its functor.
Source: Stacks 07A4 and 0941
(blueprint: lem-pod-reindexing-reduction-tensor-square-descent). -/
def podReindexingSystemTensor {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (podReindexCalculus l E Y).systemClosed.tensor ⋙
        integralComparisonDerivedSequencePullback l E g ≅
      (integralComparisonDerivedSequencePullback l E g).prod
        (integralComparisonDerivedSequencePullback l E g) ⋙
          (podReindexCalculus l E X).systemClosed.tensor :=
  let e := eqToIso (podReindexing_sequence_pullback_eq l E g)
  Functor.isoWhiskerLeft _ e.symm ≪≫ pullbackTensorSystemComparison l E g ≪≫
    Functor.isoWhiskerRight (NatIso.prod e e) _

@[irreducible] private def systemComparison {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (podReindexCalculus l E Y).systemClosed.tensor ⋙ pullbackTensorSequenceDerived l E g ≅
      (pullbackTensorSequenceDerived l E g).prod (pullbackTensorSequenceDerived l E g) ⋙
        (podReindexCalculus l E X).systemClosed.tensor :=
  pullbackTensorSystemComparison l E g

private theorem systemTensor_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    podReindexingSystemTensor l E g =
      Functor.isoWhiskerLeft (podReindexCalculus l E Y).systemClosed.tensor
          (eqToIso (podReindexing_sequence_pullback_eq l E g)).symm ≪≫
        systemComparison l E g ≪≫
          Functor.isoWhiskerRight
            (NatIso.prod (eqToIso (podReindexing_sequence_pullback_eq l E g))
              (eqToIso (podReindexing_sequence_pullback_eq l E g)))
            (podReindexCalculus l E X).systemClosed.tensor := by
  unfold systemComparison
  rfl

/-- The normalized ordinary tensor arrow, with its construction kept behind one name.
Source: Stacks 07A4
(blueprint: lem-pod-reindexing-reduction-tensor-square-descent). -/
@[irreducible] def podReindexingIntegralTensorHom
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (M N : podReindexingDerived l E Y none) :
    (podOrdinaryReindex l E g).obj
        ((podReindexCalculus l E Y).integralClosed.tensor.obj (M, N)) ⟶
      (podReindexCalculus l E X).integralClosed.tensor.obj
        ((podOrdinaryReindex l E g).obj M, (podOrdinaryReindex l E g).obj N) :=
  ((((eqToIso h).app
          ((podReindexCalculus l E Y).integralClosed.tensor.obj (M, N))).symm ≪≫
          c.tensor.app (M, N) ≪≫
          (podReindexCalculus l E X).integralClosed.tensor.mapIso
            (((eqToIso h).app M).prod ((eqToIso h).app N))).hom)

/-- The defining equation of the normalized ordinary tensor arrow.
Source: Stacks 07A4
(blueprint: lem-pod-reindexing-reduction-tensor-square-descent). -/
theorem podReindexingIntegralTensorHom_eq
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (M N : podReindexingDerived l E Y none) :
    podReindexingIntegralTensorHom l E g c h M N =
      ((((eqToIso h).app
          ((podReindexCalculus l E Y).integralClosed.tensor.obj (M, N))).symm ≪≫
          c.tensor.app (M, N) ≪≫
          (podReindexCalculus l E X).integralClosed.tensor.mapIso
            (((eqToIso h).app M).prod ((eqToIso h).app N))).hom) := by
  unfold podReindexingIntegralTensorHom
  rfl

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

private def systemModel (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) Q) :
    (systemQ l E W).obj ((S[W]).obj (P, Q)) ≅
      (podReindexCalculus l E W).systemClosed.tensor.obj
        ((systemQ l E W).obj P, (systemQ l E W).obj Q) :=
  pullbackTensorSystemModel l E W P Q hP hQ

attribute [local irreducible] systemModel

private theorem tensor_comp {C D : Type*} [Category C] [Category D]
    (B : C × C ⥤ D) {P P' P'' Q Q' Q'' : C}
    (a : P ⟶ P') (b : Q ⟶ Q') (a' : P' ⟶ P'') (b' : Q' ⟶ Q'') :
    B.map (Prod.mkHom a b) ≫ B.map (Prod.mkHom a' b') =
      B.map (Prod.mkHom (a ≫ a') (b ≫ b')) := (B.map_comp _ _).symm

private theorem paste_right {C : Type*} [Category C]
    {A B C' D E' : C} {a : A ⟶ B} {b : B ⟶ C'} {c : C' ⟶ D}
    {d : C' ⟶ E'} {e : E' ⟶ D} {f : A ⟶ E'}
    (hc : c = d ≫ e) (hf : a ≫ b ≫ d = f) : a ≫ b ≫ c = f ≫ e := by
  rw [hc]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ e) hf

private theorem tensor_conjugate {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) (F G : C ⥤ D) (e : F ≅ G)
    (c : T ⋙ F ≅ F.prod F ⋙ U)
    {P Q V : C} {P' Q' : D} (b : V ⟶ T.obj (P, Q))
    (fP : G.obj P ⟶ P') (fQ : G.obj Q ⟶ Q')
    (r : F.obj V ⟶ U.obj (P', Q'))
    (h : F.map b ≫ c.hom.app (P, Q) ≫
      U.map (Prod.mkHom (e.hom.app P ≫ fP) (e.hom.app Q ≫ fQ)) = r) :
    G.map b ≫
      (Functor.isoWhiskerLeft T e.symm ≪≫ c ≪≫
        Functor.isoWhiskerRight (NatIso.prod e e) U).hom.app (P, Q) ≫
      U.map (Prod.mkHom fP fQ) = e.inv.app V ≫ r := by
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod, NatTrans.prod,
    Functor.prod_obj, Functor.comp_obj, Category.assoc]
  rw [tensor_comp, reassoc_of% (e.inv.naturality b), h]

private theorem system_naturality (W : Scheme.{u})
    (P Q P' Q' : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) Q)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) P')
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) Q')
    (f : P ⟶ P') (j : Q ⟶ Q') :
    (systemQ l E W).map ((S[W]).map (Prod.mkHom f j)) ≫
        (systemModel l E W P' Q' hP' hQ').hom =
      (systemModel l E W P Q hP hQ).hom ≫
        (podReindexCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom ((systemQ l E W).map f) ((systemQ l E W).map j)) := by
  unfold systemModel pullbackTensorSystemModel systemQ
  exact (tensorModel_naturality (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
    (pullbackTensorCalculus l E W).systemClosed
    (pullbackTensorCalculus l E W).systemTensorModel P Q P' Q' hP hQ hP' hQ' f j).symm

private theorem system_original_model {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E Y) Q) :
    (pullbackTensorSequenceDerived l E g).map (systemModel l E Y P Q hP hQ).hom ≫
      (systemComparison l E g).hom.app
        ((systemQ l E Y).obj P, (systemQ l E Y).obj Q) ≫
      (podReindexCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((rawSystemFactor l E g).hom.app P)
          ((rawSystemFactor l E g).hom.app Q)) =
    (rawSystemFactor l E g).hom.app
        ((S[Y]).obj (P, Q)) ≫
      (systemQ l E X).map ((pullbackTensorSequenceCochain l E g).hom.app (P, Q)) ≫
      (systemModel l E X
        (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj P)
        (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj Q)
        (pullbackTensorSequenceGood l E g P hP)
        (pullbackTensorSequenceGood l E g Q hQ)).hom := by
  unfold rawSystemFactor systemModel systemComparison systemQ
  conv_lhs =>
    rhs
    rhs
    change (pullbackTensorCalculus l E X).systemClosed.tensor.map _
  unfold pullbackTensorSystemComparison pullbackTensorUniqueChoice
  exact (pullbackTensorSystemComparison_existsUnique l E g).exists.choose_spec P Q hP hQ

private theorem system_normalize
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    (q : C₀ ⥤ C) (r : D₀ ⥤ D)
    (T₀ : C₀ × C₀ ⥤ C₀) (U₀ : D₀ × D₀ ⥤ D₀)
    (T : C × C ⥤ C) (U : D × D ⥤ D)
    (F₀ G₀ : C₀ ⥤ D₀) (F G : C ⥤ D) (e₀ : F₀ ≅ G₀) (e : F ≅ G)
    (aF : q ⋙ F ≅ F₀ ⋙ r) (aG : q ⋙ G ≅ G₀ ⋙ r)
    (c₀ : T₀ ⋙ F₀ ≅ F₀.prod F₀ ⋙ U₀) (c : T ⋙ F ≅ F.prod F ⋙ U)
    (P Q : C₀)
    (bY : q.obj (T₀.obj (P, Q)) ≅ T.obj (q.obj P, q.obj Q))
    (bF : r.obj (U₀.obj (F₀.obj P, F₀.obj Q)) ≅
      U.obj (r.obj (F₀.obj P), r.obj (F₀.obj Q)))
    (bG : r.obj (U₀.obj (G₀.obj P, G₀.obj Q)) ≅
      U.obj (r.obj (G₀.obj P), r.obj (G₀.obj Q)))
    (hFac : ∀ Z, e.inv.app (q.obj Z) ≫ aF.hom.app Z ≫ r.map (e₀.hom.app Z) =
      aG.hom.app Z)
    (hOrig : F.map bY.hom ≫ c.hom.app (q.obj P, q.obj Q) ≫
      U.map (Prod.mkHom (aF.hom.app P) (aF.hom.app Q)) =
      aF.hom.app (T₀.obj (P, Q)) ≫ r.map (c₀.hom.app (P, Q)) ≫ bF.hom)
    (hNat : r.map (U₀.map (Prod.mkHom (e₀.hom.app P) (e₀.hom.app Q))) ≫ bG.hom =
      bF.hom ≫ U.map (Prod.mkHom (r.map (e₀.hom.app P)) (r.map (e₀.hom.app Q)))) :
    G.map bY.hom ≫ (Functor.isoWhiskerLeft T e.symm ≪≫ c ≪≫
      Functor.isoWhiskerRight (NatIso.prod e e) U).hom.app (q.obj P, q.obj Q) ≫
      U.map (Prod.mkHom (aG.hom.app P) (aG.hom.app Q)) =
    aG.hom.app (T₀.obj (P, Q)) ≫
      r.map ((Functor.isoWhiskerLeft T₀ e₀.symm ≪≫ c₀ ≪≫
        Functor.isoWhiskerRight (NatIso.prod e₀ e₀) U₀).hom.app (P, Q)) ≫ bG.hom := by
  have hP : e.hom.app (q.obj P) ≫ aG.hom.app P =
      aF.hom.app P ≫ r.map (e₀.hom.app P) := by
    rw [← hFac P, Iso.hom_inv_id_app_assoc]
  have hQ : e.hom.app (q.obj Q) ≫ aG.hom.app Q =
      aF.hom.app Q ≫ r.map (e₀.hom.app Q) := by
    rw [← hFac Q, Iso.hom_inv_id_app_assoc]
  have hProd : U.map (Prod.mkHom (e.hom.app (q.obj P) ≫ aG.hom.app P)
        (e.hom.app (q.obj Q) ≫ aG.hom.app Q)) =
      U.map (Prod.mkHom (aF.hom.app P) (aF.hom.app Q)) ≫
        U.map (Prod.mkHom (r.map (e₀.hom.app P)) (r.map (e₀.hom.app Q))) := by
    exact (congrArg₂ (fun f g ↦ U.map (Prod.mkHom f g)) hP hQ).trans
      (tensor_comp U _ _ _ _).symm
  have hC := paste_right hProd hOrig
  simp only [Category.assoc] at hC
  have hc := tensor_conjugate T U F G e c bY.hom
    (aG.hom.app P) (aG.hom.app Q) _ hC
  rw [← hNat] at hc
  have hcancel := (r.mapIso (e₀.app (T₀.obj (P, Q)))).hom_inv_id
  have hsc : r.map (e₀.hom.app (T₀.obj (P, Q))) ≫
        r.map ((Functor.isoWhiskerLeft T₀ e₀.symm ≪≫ c₀ ≪≫
          Functor.isoWhiskerRight (NatIso.prod e₀ e₀) U₀).hom.app (P, Q)) =
      r.map (c₀.hom.app (P, Q)) ≫
        r.map (U₀.map (Prod.mkHom (e₀.hom.app P) (e₀.hom.app Q))) := by
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod, NatTrans.prod,
      Functor.prod_obj, Functor.comp_obj, Functor.map_comp]
    simpa only [Category.id_comp, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv] using (reassoc_of% hcancel)
      (r.map (c₀.hom.app (P, Q)) ≫
        r.map (U₀.map (Prod.mkHom (e₀.hom.app P) (e₀.hom.app Q))))
  have hR := congrArg (fun z ↦ z ≫ bG.hom) (paste_right hsc.symm (hFac _))
  simp only [Category.assoc] at hR
  exact hc.trans hR

attribute [local irreducible] pullbackTensorSequenceDerived
  integralComparisonDerivedSequencePullback

private theorem system_model {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) Q)
    (hGP : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E X) ((I[g]).obj P))
    (hGQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E X) ((I[g]).obj Q)) :
      (((integralComparisonDerivedSequencePullback l E g).map
          (systemModel l E Y P Q hP hQ).hom ≫
        (podReindexingSystemTensor l E g).hom.app
          ((systemQ l E Y).obj P, (systemQ l E Y).obj Q) ≫
        (podReindexCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            ((systemFactor l E g).hom.app P)
            ((systemFactor l E g).hom.app Q))) :
        (integralComparisonDerivedSequencePullback l E g).obj
          ((systemQ l E Y).obj ((S[Y]).obj (P, Q))) ⟶
        (podReindexCalculus l E X).systemClosed.tensor.obj
          ((systemQ l E X).obj ((I[g]).obj P),
            (systemQ l E X).obj ((I[g]).obj Q))) =
      (systemFactor l E g).hom.app
          ((S[Y]).obj (P, Q)) ≫
        (systemQ l E X).map ((systemChain l E g).hom.app (P, Q)) ≫
        (systemModel l E X ((I[g]).obj P) ((I[g]).obj Q) hGP hGQ).hom := by
  rw [systemTensor_eq]
  unfold systemChain
  exact system_normalize
    (C := coefficientSequenceDerived l E Y) (D := coefficientSequenceDerived l E X)
    (systemQ l E Y) (systemQ l E X) (S[Y]) (S[X])
    (podReindexCalculus l E Y).systemClosed.tensor
    (podReindexCalculus l E X).systemClosed.tensor
    ((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)) (I[g])
    (pullbackTensorSequenceDerived l E g) (integralComparisonDerivedSequencePullback l E g)
    (NatIso.mapHomologicalComplex (eqToIso (inverse_eq l E g)) (.up ℤ))
    (eqToIso (podReindexing_sequence_pullback_eq l E g))
    (rawSystemFactor l E g)
    (systemFactor l E g)
    (pullbackTensorSequenceCochain l E g) (systemComparison l E g) P Q
    (systemModel l E Y P Q hP hQ)
    (systemModel l E X _ _ (pullbackTensorSequenceGood l E g P hP)
      (pullbackTensorSequenceGood l E g Q hQ))
    (systemModel l E X _ _ hGP hGQ)
    (fun Z ↦ by
      unfold systemFactor
      exact (reductionSystemFactorOfIso_hom _ _ _ _ _ _ _ _ _ Z).symm)
    (system_original_model l E g P Q hP hQ)
    (system_naturality l E X _ _ _ _ (pullbackTensorSequenceGood l E g P hP)
      (pullbackTensorSequenceGood l E g Q hQ) hGP hGQ _ _)

end WeilConjectures
