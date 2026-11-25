/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationUnit

/-! # Evaluation of sequence pullback tensor maps on generators

Source: Stacks Tags 07A4, 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-generators).
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
  pullbackTensorSequenceInverse pullbackTensorSystemComparison
  pullbackTensorInverseEvaluationComplex finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorCalculus pullbackTensorSequenceDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModulePullback

attribute [local instance] sfIntrinsicPullback_additive

attribute [local implicit_reducible] integralOperationsLevelPullback
  pullbackTensorSequenceDirect coefficientSequenceEvaluation pullbackTensorSequenceBase
  pullbackTensorSequenceCochain

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  sfIntrinsicPullback coefficientSequenceEvaluation coefficientEvaluationTensorIso
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceTopology
  SheafOfModules.monoidalCategory

-- The section formulas compare coefficient modules on the sequence and finite sites.
/-- The evaluated sequence tensor map sends unit generators to the intrinsic unit tensors.
Source: Stacks Tags 07A4, 0941 and 03D2
(blueprint: lem-pur-completed-pullback-tensor-evaluation-generators).
Proof: naturality of evaluation moves the sequence tensor map inside evaluation.
Its defining normalization sends the unit of a pure tensor to the tensor of the
sequence units. The evaluation tensor comparison preserves these generators.
The final tensor map applies the evaluation mate to each unit; its unit formula
and hc identify them with the two intrinsic inverse-image units.
-/
theorem completedPullbackTensor_evaluation_generators {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (A : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : A.val.obj (op U)),
      (c.hom.app A).val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (n + 1))))).unit.app A).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app A).val.app (op U) x)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (p q i : ℤ) (hpq : p + q = i) (U : Y.ProEt)
    (x : (P.X p).val.obj (op (n, U))) (y : (Q.X q).val.obj (op (n, U))) :
    let F : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
        CochainComplex (coefficientSequenceModules l E X) ℤ :=
      (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    let V : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
        CochainComplex (normalizedDVRModules l E Y n) ℤ :=
      (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)
    let W : CochainComplex (coefficientSequenceModules l E X) ℤ ⥤
        CochainComplex (normalizedDVRModules l E X n) ℤ :=
      (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)
    let G : CochainComplex (normalizedDVRModules l E Y n) ℤ ⥤
        CochainComplex (normalizedDVRModules l E X n) ℤ :=
      (sfIntrinsicPullback
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
    let tX' : CochainComplex (normalizedDVRModules l E X n) ℤ ×
        CochainComplex (normalizedDVRModules l E X n) ℤ ⥤
            CochainComplex (normalizedDVRModules l E X n) ℤ :=
          coefficientTotalTensor.{u, u + 1, u}
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
    let d (A : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
        W.obj (F.obj A) ⟶ G.obj (V.obj A) :=
      (pullbackTensorInverseEvaluationComplex l E f n).inv.app A ≫
        (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app (V.obj A)
    let b : F.obj (tY.obj (P, Q)) ⟶ tX.obj (F.obj P, F.obj Q) :=
      (pullbackTensorSequenceCochain l E f).hom.app (P, Q)
    let w : W.obj (tX.obj (F.obj P, F.obj Q)) ⟶
        tX'.obj (W.obj (F.obj P), W.obj (F.obj Q)) :=
      (coefficientEvaluationTensorIso l E X n (F.obj P) (F.obj Q)).hom
    let z := tX'.map (Prod.mkHom (d P) (d Q))
    let sg := coefficientTensorGenerator.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P Q p q i hpq (op (n, U)) x y
    (z.f i).val.app (op ((proEtaleBaseChange f).obj U))
      ((w.f i).val.app _ (((W.map b).f i).val.app _
        (coefficientEvaluationSection l E X
          ((pullbackTensorSequenceInverse l E f).obj ((tY.obj (P, Q)).X i)) n
          (op ((proEtaleBaseChange f).obj U))
          (((pullbackTensorSequenceAdjunction l E f).unit.app
            ((tY.obj (P, Q)).X i)).val.app (op (n, U)) sg)))) =
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n) (G.obj (V.obj P)) (G.obj (V.obj Q))
      p q i hpq (op ((proEtaleBaseChange f).obj U))
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app
          ((coefficientSequenceEvaluation l E Y n).obj (P.X p))).val.app (op U)
        (coefficientEvaluationSection l E Y (P.X p) n (op U) x))
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app
          ((coefficientSequenceEvaluation l E Y n).obj (Q.X q))).val.app (op U)
        (coefficientEvaluationSection l E Y (Q.X q) n (op U) y)) := by
  intro F V W G tY tX tX' d b w z sg
  change (z.f i).val.app (op ((proEtaleBaseChange f).obj U))
    ((w.f i).val.app _
      ((((coefficientSequenceEvaluation l E X n).map (b.f i)).val.app _)
        (coefficientEvaluationSection l E X
          ((pullbackTensorSequenceInverse l E f).obj ((tY.obj (P, Q)).X i)) n
          (op ((proEtaleBaseChange f).obj U))
          (((pullbackTensorSequenceAdjunction l E f).unit.app
            ((tY.obj (P, Q)).X i)).val.app (op (n, U)) sg)))) = _
  erw [evaluationSection_map]
  have hseq := (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose_spec
    P Q p q i hpq (n, U) x y
  erw [hseq]
  erw [pullbackTensorEvaluationTensor_generator_cast]
  erw [CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}]
  dsimp only [d]
  erw [evaluation_complex_unit l E f n c hc, evaluation_complex_unit l E f n c hc]

end WeilConjectures
