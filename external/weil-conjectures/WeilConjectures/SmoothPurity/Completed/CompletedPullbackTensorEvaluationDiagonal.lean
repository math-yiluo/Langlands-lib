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
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationQuotient
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationFactors

/-! # The total diagonal through exact-functor factorizations

Source: Stacks Tags 07A4, 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-diagonal).
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

private theorem diagonal_paste
    {D : Type*} [Category* D]
    {A0 A1 A2 A3 A4 B0 B1 B2 C0 C1 Z : D}
    (e : A0 ⟶ A1) (ga : A1 ⟶ A2) (gv : A2 ⟶ A3)
    (delta0 : A2 ⟶ C0) (delta1 : A3 ⟶ A4) (qgv : C0 ⟶ A4) (qk : A4 ⟶ Z)
    (wa : A0 ⟶ B0) (wb : B0 ⟶ B1) (gamma0 : B0 ⟶ C1) (gamma1 : B1 ⟶ B2)
    (qd : C1 ⟶ C0) (qwb : C1 ⟶ B2) (qw : B2 ⟶ Z)
    (he : e ≫ ga ≫ delta0 = wa ≫ gamma0 ≫ qd)
    (hv : gv ≫ delta1 = delta0 ≫ qgv)
    (hw : wb ≫ gamma1 = gamma0 ≫ qwb)
    (hc : qd ≫ qgv ≫ qk = qwb ≫ qw) :
    e ≫ ga ≫ gv ≫ delta1 ≫ qk = wa ≫ wb ≫ gamma1 ≫ qw := by
  rw [reassoc_of% hv, reassoc_of% he, hc, ← reassoc_of% hw]

attribute [local instance] sfIntrinsicPullback_additive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- The chosen exact-functor factorizations have large implicit coefficient types.
/-- Descend the ordinary cochain square through the exact-functor factorization maps.
Source: Stacks Tags 07A4, 0941 and 03D2
(blueprint: lem-pur-completed-pullback-tensor-evaluation-diagonal).
Proof: apply the derived quotient to the ordinary cochain compatibility. Naturality
of the exact finite-pullback factorization moves evaluation of the ordinary tensor
map through that factorization. The supplied equation he then replaces the evaluated
sequence pullback by the intrinsic finite pullback. Finally use naturality of the
X evaluation factorization. Associativity pastes these three squares.
-/
theorem completedPullbackTensor_evaluation_diagonal {X Y : Scheme.{u}}
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
    let tX' : CochainComplex (normalizedDVRModules l E X n) ℤ ×
        CochainComplex (normalizedDVRModules l E X n) ℤ ⥤
            CochainComplex (normalizedDVRModules l E X n) ℤ :=
          coefficientTotalTensor.{u, u + 1, u}
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
    let d (A : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
        WC.obj (FC.obj A) ⟶ GC.obj (VC.obj A) :=
      (pullbackTensorInverseEvaluationComplex l E f n).inv.app A ≫
        (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app (VC.obj A)
    let b := (pullbackTensorSequenceCochain l E f).hom.app (P, Q)
    let v := (coefficientEvaluationTensorIso l E Y n P Q).hom
    let w := (coefficientEvaluationTensorIso l E X n (FC.obj P) (FC.obj Q)).hom
    let z := tX'.map (Prod.mkHom (d P) (d Q))
    e.hom.app (DerivedCategory.Q.obj (tY.obj (P, Q))) ≫
      (finiteDerivedPullback l E n f).map
        ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app _) ≫
      (finiteDerivedPullback l E n f).map (DerivedCategory.Q.map v) ≫
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
        f).mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map k.hom =
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _) ≫
      (coefficientSequenceDerivedEvaluation l E X n).map (DerivedCategory.Q.map b) ≫
      (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map w ≫ DerivedCategory.Q.map z := by
  intro FC VC WC GC tY tX' d b v w z
  have hcQ := completedPullbackTensor_evaluation_quotient l E f n c hc P Q k hk
    DerivedCategory.Q
  change DerivedCategory.Q.map (d (tY.obj (P, Q))) ≫
    DerivedCategory.Q.map (GC.map v) ≫ DerivedCategory.Q.map k.hom =
    DerivedCategory.Q.map (WC.map b) ≫ DerivedCategory.Q.map w ≫
      DerivedCategory.Q.map z at hcQ
  have hvnat := (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
    f).mapDerivedCategoryFactors_hom_naturality v
  have hwnat := (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors_hom_naturality b
  change (finiteDerivedPullback l E n f).map (DerivedCategory.Q.map v) ≫
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
      f).mapDerivedCategoryFactors.hom.app _ =
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
      f).mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map (GC.map v) at hvnat
  change (coefficientSequenceDerivedEvaluation l E X n).map (DerivedCategory.Q.map b) ≫
    (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ =
    (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (WC.map b) at hwnat
  have heS' := completedPullbackTensor_evaluation_factors l E f n c e he
    (tY.obj (P, Q))
  change e.hom.app (DerivedCategory.Q.obj (tY.obj (P, Q))) ≫
      (finiteDerivedPullback l E n f).map
        ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app _) ≫
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
        f).mapDerivedCategoryFactors.hom.app _ =
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _) ≫
      (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (d (tY.obj (P, Q))) at heS'
  exact diagonal_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ heS' hvnat hwnat hcQ

end WeilConjectures
