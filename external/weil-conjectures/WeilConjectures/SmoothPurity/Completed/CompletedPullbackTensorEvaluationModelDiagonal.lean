/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatNormalization
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationDiagonal

/-! # The total diagonal with tensor-model isomorphisms

Source: Stacks Tags 07A4, 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-model-diagonal).
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

attribute [local instance] sfIntrinsicPullback_additive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Express the ordinary-derived diagonal through the composite model isomorphisms.
Source: Stacks Tags 07A4, 0941 and 03D2
(blueprint: lem-pur-completed-pullback-tensor-evaluation-model-diagonal).
Proof: use the total diagonal through exact-functor factorizations. Expand only
composite isomorphisms, mapped isomorphisms and the product of the ordinary mates;
functoriality and associativity identify its two sides with the displayed paths.
This step changes neither the complexes nor the tensor comparison.
-/
theorem completedPullbackTensor_evaluation_model_diagonal {X Y : Scheme.{u}}
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
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (k : ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj
      ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
        (integralCoefficientCommRingSheaf l E Y n)).obj
        ((((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P),
         (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q))) ≅
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
        ((((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)),
         (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q))))
    (hk : FinitePullbackTensorGenerators l E f n
      (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)
      (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q) k) :
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
          DerivedCategory.Q.mapIso z).hom := by
  intro FC VC WC GC tY tX tY' tX' d
  have hdiag := completedPullbackTensor_evaluation_diagonal l E f n c hc e he P Q k hk
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Functor.comp_obj, Functor.prod_obj, Category.assoc, Iso.prod_hom, Iso.symm_hom,
    d, FC, VC, WC, GC, tY, tX, tY', tX'] using hdiag

end WeilConjectures
