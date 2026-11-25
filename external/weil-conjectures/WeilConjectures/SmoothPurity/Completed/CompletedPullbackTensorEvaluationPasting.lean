/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationFactors
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationModelTransport

/-! # Pasting the normalized tensor-model faces

Source: Stacks Tags 07A4, 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  sfIntrinsicPullback coefficientSequenceEvaluation
  pullbackTensorSequenceInverse pullbackTensorSystemComparison
  pullbackTensorInverseEvaluationComplex finitePullbackTensorConstruction
  coefficientTotalTensor DerivedCategory.Q DerivedCategory instCategoryDerivedCategory
  CochainComplex.IsKFlatIndependentCoefficients
  CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorCalculus pullbackTensorSequenceDerived
  finiteIntrinsicDerivedTensor finiteIntrinsicClosed

-- A cube with tensor models at its four corners.
private theorem tensor_cube_paste
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (F : A ⥤ B) (V : A ⥤ C) (W : B ⥤ D) (G : C ⥤ D)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (mu : TA ⋙ F ⟶ F.prod F ⋙ TB)
    (tau : TA ⋙ V ⟶ V.prod V ⋙ TC)
    (sigma : TB ⋙ W ⟶ W.prod W ⋙ TD)
    (nu : TC ⋙ G ⟶ G.prod G ⋙ TD) (e : F ⋙ W ⟶ V ⋙ G)
    (P Q S : A) (S' P' Q' : B) (R P'' Q'' : C) (R' P''' Q''' : D)
    (r : S ≅ TA.obj (P, Q)) (r' : S' ≅ TB.obj (P', Q'))
    (s : R ≅ TC.obj (P'', Q'')) (s' : R' ≅ TD.obj (P''', Q'''))
    (fp : F.obj P ≅ P') (fq : F.obj Q ≅ Q') (ft : F.obj S ≅ S')
    (vp : V.obj P ≅ P'') (vq : V.obj Q ≅ Q'') (vt : V.obj S ≅ R)
    (wp : W.obj P' ≅ P''') (wq : W.obj Q' ≅ Q''') (wt : W.obj S' ≅ R')
    (gp : G.obj P'' ≅ P''') (gq : G.obj Q'' ≅ Q''') (gt : G.obj R ≅ R')
    (hm : F.map r.hom ≫ mu.app (P, Q) ≫ TB.map (Prod.mkHom fp.hom fq.hom) =
      ft.hom ≫ r'.hom)
    (hv : V.map r.hom ≫ tau.app (P, Q) ≫ TC.map (Prod.mkHom vp.hom vq.hom) =
      vt.hom ≫ s.hom)
    (hw : W.map r'.hom ≫ sigma.app (P', Q') ≫ TD.map (Prod.mkHom wp.hom wq.hom) =
      wt.hom ≫ s'.hom)
    (hg : G.map s.hom ≫ nu.app (P'', Q'') ≫ TD.map (Prod.mkHom gp.hom gq.hom) =
      gt.hom ≫ s'.hom)
    (hep : e.app P ≫ G.map vp.hom ≫ gp.hom = W.map fp.hom ≫ wp.hom)
    (heq : e.app Q ≫ G.map vq.hom ≫ gq.hom = W.map fq.hom ≫ wq.hom)
    (het : e.app S ≫ G.map vt.hom ≫ gt.hom = W.map ft.hom ≫ wt.hom) :
    W.map (mu.app (P, Q)) ≫ sigma.app (F.obj P, F.obj Q) ≫
      TD.map (Prod.mkHom (e.app P) (e.app Q)) =
    e.app (TA.obj (P, Q)) ≫ G.map (tau.app (P, Q)) ≫ nu.app (V.obj P, V.obj Q) := by
  have : IsIso (TD.map (Prod.mkHom
      (G.map vp.hom ≫ gp.hom) (G.map vq.hom ≫ gq.hom))) :=
    (TD.mapIso (Iso.prod (G.mapIso vp ≪≫ gp) (G.mapIso vq ≪≫ gq))).isIso_hom
  apply (cancel_epi (W.map (F.map r.hom))).1
  apply (cancel_mono (TD.map (Prod.mkHom
    (G.map vp.hom ≫ gp.hom) (G.map vq.hom ≫ gq.hom)))).1
  have hsigma := sigma.naturality (Prod.mkHom fp.hom fq.hom)
  have hnu := nu.naturality (Prod.mkHom vp.hom vq.hom)
  have he := e.naturality r.hom
  dsimp only [Functor.comp_map, Functor.prod_map] at hsigma hnu he
  have hp : Prod.mkHom (e.app P) (e.app Q) ≫
      Prod.mkHom (G.map vp.hom ≫ gp.hom) (G.map vq.hom ≫ gq.hom) =
      Prod.mkHom (W.map fp.hom) (W.map fq.hom) ≫
        Prod.mkHom wp.hom wq.hom := by
    apply Prod.hom_ext <;> dsimp <;> assumption
  calc
    _ = W.map (F.map r.hom) ≫ W.map (mu.app (P, Q)) ≫
        sigma.app (F.obj P, F.obj Q) ≫
        TD.map (Prod.mkHom (W.map fp.hom) (W.map fq.hom)) ≫
        TD.map (Prod.mkHom wp.hom wq.hom) := by
      simp only [Category.assoc, ← TD.map_comp, hp]
    _ = W.map (F.map r.hom ≫ mu.app (P, Q) ≫
        TB.map (Prod.mkHom fp.hom fq.hom)) ≫
        sigma.app (P', Q') ≫ TD.map (Prod.mkHom wp.hom wq.hom) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hsigma]
    _ = W.map ft.hom ≫ wt.hom ≫ s'.hom := by
      rw [hm]
      simp only [Functor.map_comp, Category.assoc, hw]
    _ = e.app S ≫ G.map vt.hom ≫ gt.hom ≫ s'.hom := by
      rw [← Category.assoc, ← het]
      simp only [Category.assoc]
    _ = e.app S ≫ G.map (V.map r.hom) ≫ G.map (tau.app (P, Q)) ≫
        G.map (TC.map (Prod.mkHom vp.hom vq.hom)) ≫
        nu.app (P'', Q'') ≫ TD.map (Prod.mkHom gp.hom gq.hom) := by
      rw [← hg]
      simp only [← G.map_comp_assoc, ← hv]
    _ = _ := by
      simp only [Category.assoc]
      rw [reassoc_of% hnu, ← reassoc_of% he]
      simp only [← TD.map_comp]
      rfl

attribute [local instance] sfIntrinsicPullback_additive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- The cube carries the chosen tensor models and exact-functor factorizations.
/-- Paste normalized tensor-model faces and a prescribed total diagonal into the cube.
Source: Stacks Tag 07A4, representative tensor-model pasting
(blueprint: lem-pur-completed-pullback-tensor-evaluation-pasting).
Proof: use the system tensor models and finite tensor models as the four corners.
The two given evaluation normalizations and the system comparison normalization
supply three faces, the finite normalization supplies the fourth, and he gives
the two factor faces. The assumed total diagonal supplies the last face.
Naturality of tensor comparisons pastes these faces; cancellation of the model
isomorphisms gives the asserted derived cube. This step does not prove the
ordinary diagonal or obtain the finite normalization.
-/
theorem completedPullbackTensor_evaluation_pasting {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f)
    (he : ∀ A : CochainComplex (coefficientSequenceModules l E Y) ℤ,
      e.hom.app (DerivedCategory.Q.obj A) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app A) ≫
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app A) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)))
    (hn : CoefficientEvaluationTensorNormalization l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction)
    (hx : CoefficientEvaluationTensorNormalization l E X
      (pullbackTensorCalculus l E X).toCoefficientDerivedSystemReduction)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) Q) :
    let FC : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
        CochainComplex (coefficientSequenceModules l E X) ℤ :=
          (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    let VC : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
        CochainComplex (normalizedDVRModules l E Y n) ℤ :=
          (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)
    let WC : CochainComplex (coefficientSequenceModules l E X) ℤ ⥤
        CochainComplex (normalizedDVRModules l E X n) ℤ :=
          (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)
    let GC : CochainComplex (normalizedDVRModules l E Y n) ℤ ⥤
        CochainComplex (normalizedDVRModules l E X n) ℤ := (sfIntrinsicPullback
      (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ)
    let tY : CochainComplex (coefficientSequenceModules l E Y) ℤ ×
        CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
            CochainComplex (coefficientSequenceModules l E Y) ℤ :=
          coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology Y)) (coefficientSequenceCommRingSheaf l E Y)
    let tX : CochainComplex (coefficientSequenceModules l E X) ℤ ×
        CochainComplex (coefficientSequenceModules l E X) ℤ ⥤
            CochainComplex (coefficientSequenceModules l E X) ℤ :=
          coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
    let tY' : CochainComplex (normalizedDVRModules l E Y n) ℤ ×
        CochainComplex (normalizedDVRModules l E Y n) ℤ ⥤
            CochainComplex (normalizedDVRModules l E Y n) ℤ :=
          coefficientTotalTensor.{u, u + 1, u}
      (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
    let tX' : CochainComplex (normalizedDVRModules l E X n) ℤ ×
        CochainComplex (normalizedDVRModules l E X n) ℤ ⥤
            CochainComplex (normalizedDVRModules l E X n) ℤ :=
          coefficientTotalTensor.{u, u + 1, u}
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
    let d (A : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
        WC.obj (FC.obj A) ≅ GC.obj (VC.obj A) :=
      (pullbackTensorInverseEvaluationComplex l E f n).symm.app A ≪≫
        (NatIso.mapHomologicalComplex c (.up ℤ)).app (VC.obj A)
    ∀ (hVP : CochainComplex.IsKFlatIndependentCoefficients
        (R := integralCoefficientCommRingSheaf l E Y n) (VC.obj P))
      (hVQ : CochainComplex.IsKFlatIndependentCoefficients
        (R := integralCoefficientCommRingSheaf l E Y n) (VC.obj Q))
      (hGVP : CochainComplex.IsKFlatIndependentCoefficients
        (R := integralCoefficientCommRingSheaf l E X n) (GC.obj (VC.obj P)))
      (hGVQ : CochainComplex.IsKFlatIndependentCoefficients
        (R := integralCoefficientCommRingSheaf l E X n) (GC.obj (VC.obj Q)))
      (k : GC.obj (tY'.obj (VC.obj P, VC.obj Q)) ≅
        tX'.obj (GC.obj (VC.obj P), GC.obj (VC.obj Q)))
      (_hfinite : (finiteDerivedPullback l E n f).map
          (coefficientFiniteTensorModelIso l E Y
            (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemTensors n
            (VC.obj P) (VC.obj Q) hVP hVQ).hom ≫
        (finitePullbackTensorConstructionIso l E f n).hom.app
          (DerivedCategory.Q.obj (VC.obj P), DerivedCategory.Q.obj (VC.obj Q)) ≫
        (finiteIntrinsicDerivedTensor l E X n).map
          (Prod.mkHom
            ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
              f).mapDerivedCategoryFactors.hom.app (VC.obj P))
            ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
              f).mapDerivedCategoryFactors.hom.app (VC.obj Q))) =
        (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
          f).mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map k.hom ≫
        (coefficientFiniteTensorModelIso l E X
          (pullbackTensorCalculus l E X).toCoefficientDerivedSystemTensors
          n _ _ hGVP hGVQ).hom)
      (_hdiag :
        let b := (pullbackTensorSequenceCochain l E f).app (P, Q)
        let v := coefficientEvaluationTensorIso l E Y n P Q
        let w := coefficientEvaluationTensorIso l E X n (FC.obj P) (FC.obj Q)
        let z := tX'.mapIso (Iso.prod (d P) (d Q))
        e.hom.app (DerivedCategory.Q.obj (tY.obj (P, Q))) ≫
          (finiteDerivedPullback l E n f).map
            (((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.app
              (tY.obj (P, Q)) ≪≫ DerivedCategory.Q.mapIso v).hom) ≫
          ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
            f).mapDerivedCategoryFactors.app
              (tY'.obj (VC.obj P, VC.obj Q)) ≪≫ DerivedCategory.Q.mapIso k).hom =
        (coefficientSequenceDerivedEvaluation l E X n).map
          (((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app
            (tY.obj (P, Q)) ≪≫ DerivedCategory.Q.mapIso b).hom) ≫
          ((coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.app
            (tX.obj (FC.obj P, FC.obj Q)) ≪≫ DerivedCategory.Q.mapIso w ≪≫
              DerivedCategory.Q.mapIso z).hom),
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSystemComparison l E f).hom.app (M, N)) ≫
      ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
        ((pullbackTensorSequenceDerived l E f).obj M,
          (pullbackTensorSequenceDerived l E f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (e.hom.app M)
          (e.hom.app N)) =
    e.hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M, N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M, N)) ≫
      (finitePullbackTensorConstructionIso l E f n).hom.app
      ((coefficientSequenceDerivedEvaluation l E Y n).obj M,
        (coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  intro FC VC WC GC tY tX tY' tX' d hVP hVQ hGVP hGVQ k hfinite hdiag M N
  have hFP := pullbackTensorSequenceGood l E f P hP
  have hFQ := pullbackTensorSequenceGood l E f Q hQ
  have hWFP := (coefficientTensorModelPreservation l E X).2 (FC.obj P) hFP n
  have hWFQ := (coefficientTensorModelPreservation l E X).2 (FC.obj Q) hFQ n
  let r : (DerivedCategory.Q.obj (tY.obj (P, Q)) :
      coefficientSequenceDerived l E Y) ≅
      (pullbackTensorCalculus l E Y).systemClosed.tensor.obj
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
    pullbackTensorSystemModel l E Y P Q hP hQ
  let r' : (DerivedCategory.Q.obj (tX.obj (FC.obj P, FC.obj Q)) :
      coefficientSequenceDerived l E X) ≅
      (pullbackTensorCalculus l E X).systemClosed.tensor.obj
        (DerivedCategory.Q.obj (FC.obj P), DerivedCategory.Q.obj (FC.obj Q)) :=
    pullbackTensorSystemModel l E X (FC.obj P) (FC.obj Q) hFP hFQ
  let s : (DerivedCategory.Q.obj (tY'.obj (VC.obj P, VC.obj Q)) :
      proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) ≅
      (finiteIntrinsicDerivedTensor l E Y n).obj
        (DerivedCategory.Q.obj (VC.obj P), DerivedCategory.Q.obj (VC.obj Q)) :=
    coefficientFiniteTensorModelIso l E Y
    (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemTensors n
    (VC.obj P) (VC.obj Q) hVP hVQ
  let s' : (DerivedCategory.Q.obj (tX'.obj (GC.obj (VC.obj P), GC.obj (VC.obj Q))) :
      proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) ≅
      (finiteIntrinsicDerivedTensor l E X n).obj
        (DerivedCategory.Q.obj (GC.obj (VC.obj P)),
          DerivedCategory.Q.obj (GC.obj (VC.obj Q))) :=
    coefficientFiniteTensorModelIso l E X
    (pullbackTensorCalculus l E X).toCoefficientDerivedSystemTensors n
    (GC.obj (VC.obj P)) (GC.obj (VC.obj Q)) hGVP hGVQ
  let b : FC.obj (tY.obj (P, Q)) ≅ tX.obj (FC.obj P, FC.obj Q) :=
    (pullbackTensorSequenceCochain l E f).app (P, Q)
  let v : VC.obj (tY.obj (P, Q)) ≅ tY'.obj (VC.obj P, VC.obj Q) :=
    coefficientEvaluationTensorIso l E Y n P Q
  let w : WC.obj (tX.obj (FC.obj P, FC.obj Q)) ≅
      tX'.obj (WC.obj (FC.obj P), WC.obj (FC.obj Q)) :=
    coefficientEvaluationTensorIso l E X n (FC.obj P) (FC.obj Q)
  let z : tX'.obj (WC.obj (FC.obj P), WC.obj (FC.obj Q)) ≅
      tX'.obj (GC.obj (VC.obj P), GC.obj (VC.obj Q)) := tX'.mapIso (Iso.prod (d P) (d Q))
  let fp :
      (pullbackTensorSequenceDerived l E f).obj (DerivedCategory.Q.obj (P)) ≅
      DerivedCategory.Q.obj (FC.obj P) :=
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app P
  let fq :
      (pullbackTensorSequenceDerived l E f).obj (DerivedCategory.Q.obj (Q)) ≅
      DerivedCategory.Q.obj (FC.obj Q) :=
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app Q
  let ft :
      (pullbackTensorSequenceDerived l E f).obj (DerivedCategory.Q.obj (tY.obj (P, Q))) ≅
      DerivedCategory.Q.obj (tX.obj (FC.obj P, FC.obj Q)) :=
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app
    (tY.obj (P, Q)) ≪≫ DerivedCategory.Q.mapIso b
  let vp :
      (coefficientSequenceDerivedEvaluation l E Y n).obj (DerivedCategory.Q.obj (P)) ≅
      DerivedCategory.Q.obj (VC.obj P) :=
    (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.app P
  let vq :
      (coefficientSequenceDerivedEvaluation l E Y n).obj (DerivedCategory.Q.obj (Q)) ≅
      DerivedCategory.Q.obj (VC.obj Q) :=
    (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.app Q
  let vt :
      (coefficientSequenceDerivedEvaluation l E Y n).obj (DerivedCategory.Q.obj (tY.obj (P, Q))) ≅
      DerivedCategory.Q.obj (tY'.obj (VC.obj P, VC.obj Q)) :=
    (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.app
    (tY.obj (P, Q)) ≪≫ DerivedCategory.Q.mapIso v
  let wp :
      (coefficientSequenceDerivedEvaluation l E X n).obj (DerivedCategory.Q.obj (FC.obj P)) ≅
      DerivedCategory.Q.obj (GC.obj (VC.obj P)) :=
    (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.app
    (FC.obj P) ≪≫ DerivedCategory.Q.mapIso (d P)
  let wq :
      (coefficientSequenceDerivedEvaluation l E X n).obj (DerivedCategory.Q.obj (FC.obj Q)) ≅
      DerivedCategory.Q.obj (GC.obj (VC.obj Q)) :=
    (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.app
    (FC.obj Q) ≪≫ DerivedCategory.Q.mapIso (d Q)
  let wt :
      (coefficientSequenceDerivedEvaluation l E X n).obj
        (DerivedCategory.Q.obj (tX.obj (FC.obj P, FC.obj Q))) ≅
      DerivedCategory.Q.obj (tX'.obj (GC.obj (VC.obj P), GC.obj (VC.obj Q))) :=
    (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.app
    (tX.obj (FC.obj P, FC.obj Q)) ≪≫ DerivedCategory.Q.mapIso w ≪≫
      DerivedCategory.Q.mapIso z
  let gp :
      (finiteDerivedPullback l E n f).obj (DerivedCategory.Q.obj (VC.obj P)) ≅
      DerivedCategory.Q.obj (GC.obj (VC.obj P)) := (sfIntrinsicPullback
    (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.app (VC.obj P)
  let gq :
      (finiteDerivedPullback l E n f).obj (DerivedCategory.Q.obj (VC.obj Q)) ≅
      DerivedCategory.Q.obj (GC.obj (VC.obj Q)) := (sfIntrinsicPullback
    (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.app (VC.obj Q)
  let gt :
      (finiteDerivedPullback l E n f).obj (DerivedCategory.Q.obj (tY'.obj (VC.obj P, VC.obj Q))) ≅
      DerivedCategory.Q.obj (tX'.obj (GC.obj (VC.obj P), GC.obj (VC.obj Q))) := (sfIntrinsicPullback
    (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.app
      (tY'.obj (VC.obj P, VC.obj Q)) ≪≫ DerivedCategory.Q.mapIso k
  apply tensor_cube_paste
    (pullbackTensorSequenceDerived l E f) (coefficientSequenceDerivedEvaluation l E Y n)
    (coefficientSequenceDerivedEvaluation l E X n) (finiteDerivedPullback l E n f)
    (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (finiteIntrinsicDerivedTensor l E Y n) (finiteIntrinsicDerivedTensor l E X n)
    (pullbackTensorSystemComparison l E f).hom
    ((pullbackTensorCalculus l E Y).evaluationTensor n).hom
    ((pullbackTensorCalculus l E X).evaluationTensor n).hom
    (finitePullbackTensorConstructionIso l E f n).hom e.hom
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj (tY.obj (P, Q)))
    _ _ _ _ _ _ _ _ _ r r' s s' fp fq ft vp vq vt wp wq wt gp gq gt
  · dsimp only [r, r', fp, fq, ft, FC, tY, b, Functor.comp_obj, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom]
    erw [Category.assoc]
    unfold pullbackTensorSystemComparison pullbackTensorUniqueChoice
    exact (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec P Q hP hQ
  · dsimp only [r, s, vp, vq, vt, v, VC, tY, Functor.comp_obj,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    erw [Category.assoc]
    exact hn n P Q hP hQ
  · have hface := completedPullbackTensor_evaluation_model_transport l E X n hx
      (FC.obj P) (FC.obj Q) hFP hFQ (GC.obj (VC.obj P)) (GC.obj (VC.obj Q))
      hGVP hGVQ (d P) (d Q)
    dsimp only [r', s', wp, wq, wt, z, WC, w, tX, tX', Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom]
    simp only [Category.assoc]
    exact hface
  · simpa only [s, s', gp, gq, gt, GC, tY', Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Category.assoc] using hfinite
  · simpa only [fp, vp, wp, gp, d, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Functor.mapIso_hom, Category.assoc] using
      completedPullbackTensor_evaluation_factors l E f n c e he P
  · simpa only [fq, vq, wq, gq, d, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Functor.mapIso_hom, Category.assoc] using
      completedPullbackTensor_evaluation_factors l E f n c e he Q
  · exact hdiag

end WeilConjectures
