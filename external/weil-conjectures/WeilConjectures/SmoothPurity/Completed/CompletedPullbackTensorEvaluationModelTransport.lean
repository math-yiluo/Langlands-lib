/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus

/-! # Transport of evaluation tensor-model normalization

Source: Stacks Tags 07A4, 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-model-transport).
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

private theorem tensor_face_transport
    {B D : Type*} [Category* B] [Category* D]
    (W : B ⥤ D) (TB : B × B ⥤ B) (TD : D × D ⥤ D)
    (sigma : TB ⋙ W ⟶ W.prod W ⋙ TD)
    {S P Q : B} {R R' P' Q' P'' Q'' : D}
    (r : S ≅ TB.obj (P, Q)) (s : R ≅ TD.obj (P', Q'))
    (s' : R' ≅ TD.obj (P'', Q''))
    (fp : W.obj P ⟶ P') (fq : W.obj Q ⟶ Q')
    (a : P' ⟶ P'') (b : Q' ⟶ Q'') (u : W.obj S ⟶ R) (v : R ⟶ R')
    (h : W.map r.hom ≫ sigma.app (P, Q) ≫ TD.map (Prod.mkHom fp fq) = u ≫ s.hom)
    (hnat : v ≫ s'.hom = s.hom ≫ TD.map (Prod.mkHom a b)) :
    W.map r.hom ≫ sigma.app (P, Q) ≫ TD.map (Prod.mkHom (fp ≫ a) (fq ≫ b)) =
      u ≫ v ≫ s'.hom := by
  have hp : Prod.mkHom (fp ≫ a) (fq ≫ b) =
      Prod.mkHom fp fq ≫ Prod.mkHom a b := rfl
  rw [hp, Functor.map_comp]
  calc
    _ = (W.map r.hom ≫ sigma.app (P, Q) ≫ TD.map (Prod.mkHom fp fq)) ≫
        TD.map (Prod.mkHom a b) := by simp only [Category.assoc]
    _ = (u ≫ s.hom) ≫ TD.map (Prod.mkHom a b) := by rw [h]
    _ = _ := by simp only [Category.assoc, ← hnat]

attribute [local instance] sfIntrinsicPullback_additive
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem finite_model_naturality (W : Scheme.{u}) (n : ℕ)
    (P Q P' Q' : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P')
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q')
    (a : P ⟶ P') (b : Q ⟶ Q') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{u, u + 1, u}
      (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)).map
        (Prod.mkHom a b)) ≫
      (coefficientFiniteTensorModelIso l E W
        (pullbackTensorCalculus l E W).toCoefficientDerivedSystemTensors
        n P' Q' hP' hQ').hom =
    (coefficientFiniteTensorModelIso l E W
      (pullbackTensorCalculus l E W).toCoefficientDerivedSystemTensors
      n P Q hP hQ).hom ≫
      (finiteIntrinsicDerivedTensor l E W n).map
        (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) := by
  unfold coefficientFiniteTensorModelIso CoefficientTensorModels.iso
  exact ((pullbackTensorCalculus l E W).finiteTensorModel n).comparison.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := ⟨P', hP'⟩) a)
      (ObjectProperty.homMk (X := ⟨Q, hQ⟩) (Y := ⟨Q', hQ'⟩) b))

/-- Evaluation normalization is stable under isomorphisms of the finite tensor factors.
Source: Stacks Tags 0941 and 03D2, naturality of tensor models
(blueprint: lem-pur-completed-pullback-tensor-evaluation-model-transport).
Proof: apply the supplied evaluation normalization to the two sequence complexes.
Naturality of the finite tensor model moves the two finite isomorphisms through
that model. Functoriality combines the factorization maps with these isomorphisms.
Associativity then pastes the two equalities.
-/
theorem completedPullbackTensor_evaluation_model_transport (X : Scheme.{u}) (n : ℕ)
    (hx : CoefficientEvaluationTensorNormalization l E X
      (pullbackTensorCalculus l E X).toCoefficientDerivedSystemReduction)
    (P Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E X) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E X) Q)
    (R S : CochainComplex (normalizedDVRModules l E X n) ℤ)
    (hR : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n) R)
    (hS : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n) S)
    (a : ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj P ≅ R)
    (b : ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj Q ≅ S) :
    let t := coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
    let t' := coefficientTotalTensor.{u, u + 1, u}
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
    (coefficientSequenceDerivedEvaluation l E X n).map
        (pullbackTensorSystemModel l E X P Q hP hQ).hom ≫
      ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom
          ((coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map a.hom)
          ((coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app Q ≫
            DerivedCategory.Q.map b.hom)) =
    (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
        (t.obj (P, Q)) ≫
      DerivedCategory.Q.map (coefficientEvaluationTensorIso l E X n P Q).hom ≫
      DerivedCategory.Q.map (t'.map (Prod.mkHom a.hom b.hom)) ≫
      (coefficientFiniteTensorModelIso l E X
        (pullbackTensorCalculus l E X).toCoefficientDerivedSystemTensors n R S hR hS).hom := by
  intro t t'
  let V := (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)
  have hVP := (coefficientTensorModelPreservation l E X).2 P hP n
  have hVQ := (coefficientTensorModelPreservation l E X).2 Q hQ n
  have hnorm := hx n P Q hP hQ
  have hnat := finite_model_naturality l E X n (V.obj P) (V.obj Q) R S
    hVP hVQ hR hS a.hom b.hom
  have hface := tensor_face_transport (coefficientSequenceDerivedEvaluation l E X n)
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (finiteIntrinsicDerivedTensor l E X n)
    ((pullbackTensorCalculus l E X).evaluationTensor n).hom
    (pullbackTensorSystemModel l E X P Q hP hQ) _
    (coefficientFiniteTensorModelIso l E X
      (pullbackTensorCalculus l E X).toCoefficientDerivedSystemTensors n R S hR hS)
    ((coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app P)
    ((coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app Q)
    (DerivedCategory.Q.map a.hom) (DerivedCategory.Q.map b.hom)
    ((coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (coefficientEvaluationTensorIso l E X n P Q).hom)
    (DerivedCategory.Q.map (t'.map (Prod.mkHom a.hom b.hom)))
    (hnorm.trans (Category.assoc _ _ _).symm) hnat
  simp only [Category.assoc] at hface
  exact hface

end WeilConjectures
