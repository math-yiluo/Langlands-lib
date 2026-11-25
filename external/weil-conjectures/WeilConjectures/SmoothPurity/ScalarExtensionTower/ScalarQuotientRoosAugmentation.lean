/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import WeilConjectures.TraceFormula.Supporting.StrictQuotientCompletionRealization
import all WeilConjectures.TraceFormula.Supporting.StrictQuotientCompletionUnit
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

/-! # The Roos augmentation of a coherent scalar quotient presentation

Source: Stacks 06YY and 0941. The reduction adjunction unit is calculated
on both mapping-cocone coordinates for a specified coefficient calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence coefficientSequenceRestriction
  coefficientSequenceEvaluation unrestrictedTowerUnit coefficientConstantTowerLimit

private theorem scalar_roos_unit_eq (W : Scheme.{u})
    (I : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    pullbackTensorRoosUnit l E W I = integralComparisonLimitToRoos l E W I := by
  apply (integralComparisonLimitToRoos_existsUnique l E W I).unique
  · constructor
    · intro n
      have hf := CochainComplex.mappingCocone.lift_fst
        (scalarRoosBoundary I.asFunctor) (pullbackTensorRoosAugmentation l E W I) 0
        (pullbackTensorRoosAugmentation_condition l E W I)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ f ≫ CategoryTheory.Limits.Pi.π
          (fun m ↦ I.asFunctor.obj (Opposite.op m)) n) hf).trans
            (CategoryTheory.Limits.Pi.lift_comp_π _ n))
    · intro i j h
      exact CochainComplex.mappingCocone.lift_f_snd_v
        (scalarRoosBoundary I.asFunctor) (pullbackTensorRoosAugmentation l E W I) 0
        (pullbackTensorRoosAugmentation_condition l E W I) i j h
  · exact (integralComparisonLimitToRoos_existsUnique l E W I).exists.choose_spec

-- Whole-system localization and several exact-restriction comparisons are composed here.
private theorem coherent_roos_augmentation (X : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l E X) :
    ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    IsIntegralComparisonPresentationCoherent l E X S P.obj C e κ →
    ∃ v : P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
        (((v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫ Pi.π (fun m ↦
              ((((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
                C).asFunctor.obj (op m))) n).f i).val.app U) x =
          integralComparisonRestrictedSection l E X (C.X i) n U
            (integralComparisonSequenceSection l E X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x)))) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), v.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor)).v i j h = 0) ∧
      S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E X).map e.hom ≫
        (integralComparisonRoosBridge l E X ρ C).hom = DerivedCategory.Q.map v := by
  classical
  obtain ⟨M, ⟨D⟩⟩ := CompletionUnit.fixedCalculusModels l E X S
  let r := roosModel l E X S M D
  have hr : r.comparison = ρ.comparison := by
    apply (pullbackTensorRoosModel_existsUnique l E X).unique
    · intro I hI
      rw [scalar_roos_unit_eq l E X I]
      exact r.computes I
    · intro I hI
      rw [scalar_roos_unit_eq l E X I]
      exact ρ.computes I
  have hbridge (C : CochainComplex (coefficientSequenceModules l E X) ℤ) :
      integralComparisonRoosBridge l E X r C = integralComparisonRoosBridge l E X ρ C := by
    unfold integralComparisonRoosBridge
    rw [hr]
  obtain ⟨rho, hrho⟩ := strictQuotientCompletionRealization l E X S r
  intro P C e κ hp hc
  rw [← hbridge C]
  obtain ⟨a, ha, hrhoa⟩ := hrho P C e κ hp hc
  let b := trfStrictQuotientConeAugmentation l E X P.obj
  let v := b ≫ integralOperationsRoosFunctor.map a.inv
  have ha' := normalized_tower_map l E X C P.obj κ a ha
  have hinv (n : ℕ) :
      a.inv.app (op n) ≫
        (NatIso.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) (.up ℤ)).hom.app C =
      ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
        (κ n).inv := by
    apply (cancel_mono (((scalarReductionRestriction l E X n).mapHomologicalComplex
      (.up ℤ)).map (κ n).hom)).1
    rw [Category.assoc, ← ha' n]
    rw [Iso.inv_hom_id_app, ← Functor.map_comp, Iso.inv_hom_id]
    exact (((scalarReductionRestriction l E X n).mapHomologicalComplex
      (.up ℤ)).map_id _).symm
  refine ⟨v, ?_, ?_, ?_⟩
  · intro n i U x
    have hv : v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫ Pi.π (fun m ↦
              ((((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
                C).asFunctor.obj (op m))) n =
        unrestrictedTowerUnit l E X P.obj n ≫ a.inv.app (op n) := by
      dsimp only [v]
      rw [Category.assoc,
        ← Category.assoc (integralOperationsRoosFunctor.map a.inv)]
      erw [(IntegralAmbient.roosMap_coordinates a.inv).1]
      rw [← Category.assoc, ← Category.assoc]
      change (b ≫ CochainComplex.mappingCocone.fst _) ≫ _ ≫ _ = _
      dsimp only [b, trfStrictQuotientConeAugmentation]
      rw [CochainComplex.mappingCocone.lift_fst]
      rw [Pi.map_π]
      erw [← Category.assoc, Pi.lift_comp_π]
    rw [hv]
    change ((a.inv.app (op n)).f i).val.app U
      ((((unrestrictedTowerUnit l E X P.obj n).f i).val.app U) x) = _
    rw [unrestrictedTowerUnit_condition]
    let z := ((NatIso.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) (.up ℤ)).app C)
    let zi := (HomologicalComplex.eval _ (.up ℤ) i).mapIso z
    let zu := (SheafOfModules.evaluation _ U).mapIso zi
    apply (ConcreteCategory.bijective_of_isIso zu.hom).1
    have hi := congrArg (fun f ↦ (f.f i).val.app U
      (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x)) (hinv n)
    exact hi.trans (restricted_section_cancel l E X (C.X i) n U _).symm
  · intro i j h
    dsimp only [v]
    erw [HomologicalComplex.comp_f, Category.assoc,
      (IntegralAmbient.roosMap_coordinates a.inv).2 i j h, ← Category.assoc]
    have hb : b.f i ≫
        (CochainComplex.mappingCocone.snd (trfQuotientDifference l E X P.obj)).v i j h =
        0 := CochainComplex.mappingCocone.lift_f_snd_v _ _ _
          (trfStrictQuotientUnit_condition l E X P.obj) i j h
    rw [hb, zero_comp]
  · apply (cancel_mono (DerivedCategory.Q.map
      (integralOperationsRoosFunctor.map a.hom))).1
    simp only [Category.assoc, ← hrhoa]
    have hu := strictQuotientCompletionUnit l E X S M D r rho (fun I ↦ by
      dsimp only [r, roosModel, comparisonFromModel, Iso.trans_hom, NatTrans.comp_app,
        Iso.symm_hom, NatIso.ofComponents_hom_app, Iso.refl_hom]
      exact Category.comp_id _) hrho P
    rw [hu]
    dsimp only [v]
    rw [← DerivedCategory.Q.map_comp, Category.assoc,
      ← integralOperationsRoosFunctor.map_comp, a.inv_hom_id,
      integralOperationsRoosFunctor.map_id]
    exact congrArg DerivedCategory.Q.map (Category.comp_id b).symm

-- Compare both Roos coordinates through the large ordinary tensor interfaces.
/-- A coherent scalar quotient augmentation has the prescribed entire Roos map.
Source: Stacks 06YY and 0941; the tensor-unit augmentation in step 2 of
lem-pur-scalar-completion-quotient-presentation.
(blueprint: lem-pur-scalar-quotient-roos-augmentation).

Proof: unfold coherence and denote its strict constant-tower map by b. Transpose
its whole-system equation under the constant-tower/limit adjunction. The ordinary
transpose of b followed by the right-derived limit unit is therefore the reduction
adjunct of eS, after the exact-restriction comparison. The normalization of rho
identifies that unit followed by the Roos bridge with the localization of the
limit-tuple map whose shifted coordinate is zero. This holds on K-injective
towers by rho.computes and extends to every tower by a K-injective resolution
and naturality. After composing with q, the nth tuple coordinate on the ordinary
scalar generator 1 tensor x is determined by coherence, hκS and hq with s=1.
It is exactly the scalar quotient tensor unit. Completed-coefficient linearity
extends this to every s tensor x; sheafification and tensor generation identify
all coordinate maps. The shifted coordinate is zero on both sides. The two
mapping-cocone coordinates thus identify the strict chain map with
integralScalarCompletionChain. Localization gives the displayed equality.
This proof uses no chosen scalar realization or scalar-completion comparison,
no derived evaluation faithfulness and no completeness assumption. The same
coordinate proof includes zero complexes, empty schemes and the first quotient. -/
theorem scalarQuotientRoosAugmentation (Y : Scheme.{u})
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L Y)
    (ρ : IntegralComparisonRoosModel.{u, u} l L Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)
    (eS : SL.reduction.obj (DerivedCategory.Q.obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≅
      DerivedCategory.Q.obj
        (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C))
    (κS : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C) ≅
        (unrestrictedIntegralFiniteComplex l L Y n).obj
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hpS : CoefficientReductionPresentation l L Y SL.toCoefficientDerivedSystemReduction
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)
      (scalarGood l E L ι Y P).1
      (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
        (.up ℤ)).obj C) eS κS)
    (hcS : IsIntegralComparisonPresentationCoherent l L Y SL
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)
      (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
        (.up ℤ)).obj C) eS κS)
    (hκS : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (P.obj.X i).val.obj (op U)),
        ((κS n).hom.f i).val.app (op U)
          (coefficientEvaluationSection l L Y
            ((((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
              (.up ℤ)).obj C).X i) n (op U)
            (integralComparisonSequenceTensorSection.{u, u} l E L ι Y (C.X i)
              (op (n, U)) 1
              (integralComparisonSequenceSection.{u, u} l E Y (C.X i) n (op U)
                (((κ n).inv.f i).val.app (op U)
                  (unrestrictedIntegralTensorSection.{u, u} l E Y n (P.obj.X i)
                    (op U) 1 x))))) =
          unrestrictedIntegralTensorSection l L Y n
            ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj).X i)
            (op U) 1
            (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) (op U) 1 x))
    (q : (((coefficientSequenceRestriction l L Y).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E L ι Y).obj P.obj)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L Y).obj.obj (op (n, U.unop)))
        (x : (P.obj.X i).val.obj U),
      ((q.hom.app (op n)).f i).val.app U
        (integralComparisonRestrictedSection l L Y
          ((((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
            (.up ℤ)).obj C).X i) n U
          (integralComparisonSequenceTensorSection l E L ι Y (C.X i) (op (n, U.unop)) s
            (integralComparisonSequenceSection l E Y (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E Y n (P.obj.X i) U 1 x))))) =
        integralScalarTensorSection l E L ι Y n (P.obj.X i) U s x)
    : SL.adjunction.unit.app (DerivedCategory.Q.obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
      (coefficientSequenceLimit l L Y).map eS.hom ≫
      (integralComparisonRoosBridge l L Y ρ _).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
    DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj) := by
  classical
  let PS := ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj
  let CS := ((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
    (.up ℤ)).obj C
  let GP : (integralOperationsGoodComplex l L Y).FullSubcategory :=
    ⟨PS, scalarGood l E L ι Y P⟩
  let I := ((coefficientSequenceRestriction l L Y).mapHomologicalComplex (.up ℤ)).obj CS
  let T := (integralScalarTowerFunctor l E L ι Y).obj P.obj
  obtain ⟨v, hv, hzero, he⟩ :=
    coherent_roos_augmentation l L Y SL ρ GP CS eS κS hpS hcS
  let w := v ≫ integralOperationsRoosFunctor.map q.hom
  have hw (n : ℕ) :
      w ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫
        Pi.π (fun m ↦ T.obj (op m)) n =
      v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary I.asFunctor) ≫
        Pi.π (fun m ↦ I.asFunctor.obj (op m)) n ≫ q.hom.app (op n) := by
    dsimp only [w]
    rw [Category.assoc, ← Category.assoc (integralOperationsRoosFunctor.map q.hom)]
    erw [(IntegralAmbient.roosMap_coordinates q.hom).1]
    simp only [Category.assoc]
    erw [Pi.map_π]
  have hwunit (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U) :
      (((w ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫
        Pi.π (fun m ↦ T.obj (op m)) n).f i).val.app U)
        (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) U 1 x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i) U 1 x := by
    rw [hw]
    change ((q.hom.app (op n)).f i).val.app U
      ((((v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary I.asFunctor) ≫
        Pi.π (fun m ↦ I.asFunctor.obj (op m)) n).f i).val.app U)
        (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) U 1 x)) = _
    rw [hv]
    let y := integralComparisonSequenceTensorSection l E L ι Y (C.X i)
      (op (n, U.unop)) 1
      (integralComparisonSequenceSection l E Y (C.X i) n U
        (((κ n).inv.f i).val.app U
          (unrestrictedIntegralTensorSection l E Y n (P.obj.X i) U 1 x)))
    have hk : ((κS n).inv.f i).val.app U
        (unrestrictedIntegralTensorSection l L Y n (PS.X i) U 1
          (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) U 1 x)) =
      coefficientEvaluationSection l L Y (CS.X i) n U y := by
      have h := congrArg (fun z ↦ ((κS n).inv.f i).val.app U z) (hκS n i U.unop x)
      have hc := congrArg (fun f ↦ (f.f i).val.app U
        (coefficientEvaluationSection l L Y (CS.X i) n U y)) (κS n).hom_inv_id
      exact h.symm.trans hc
    rw [hk]
    have hy : integralComparisonSequenceSection l L Y (CS.X i) n U
        (coefficientEvaluationSection l L Y (CS.X i) n U y) = y := by
      unfold integralComparisonSequenceSection coefficientEvaluationSection
      rw [← ConcreteCategory.comp_apply, eqToHom_trans]
      rfl
    rw [hy]
    exact hq n i U 1 x
  have hχunit (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U) :
      ((((integralScalarCompletionChain l E L ι Y).app P.obj ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫
        Pi.π (fun m ↦ T.obj (op m)) n).f i).val.app U)
        (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) U 1 x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i) U 1 x := by
    have h := (integralScalarCompletionChain_existsUnique l E L ι Y).exists.choose_spec.1
      P.obj i n U 1 x
    change _ = integralScalarTensorSection l E L ι Y n (P.obj.X i) U
      ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U 1) x at h
    rw [map_one] at h
    exact h
  have hwχ : w = (integralScalarCompletionChain l E L ι Y).app P.obj := by
    apply HomologicalComplex.hom_ext
    intro i
    apply cocone_degree_ext (scalarRoosBoundary T) _ _ i
    · apply complexProduct_hom_ext
      intro n
      apply tensorSection_ext (integralCompletedScalarMap l E L ι Y)
        (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y) (P.obj.X i)
      intro U x
      rw [tensorSection_eq]
      exact (hwunit n i U x).trans (hχunit n i U x).symm
    · dsimp only [w]
      rw [HomologicalComplex.comp_f, Category.assoc]
      erw [(IntegralAmbient.roosMap_coordinates q.hom).2 i (i - 1) (by omega)]
      rw [← Category.assoc, hzero, zero_comp]
      exact ((integralScalarCompletionChain_existsUnique l E L ι Y).exists.choose_spec.2
        P.obj i (i - 1) (by omega)).symm
  erw [reassoc_of% he]
  rw [← DerivedCategory.Q.map_comp]
  exact congrArg (fun g ↦ DerivedCategory.Q.map g) hwχ

end WeilConjectures.ScalarExtensionTower
