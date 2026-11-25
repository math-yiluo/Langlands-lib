/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.SmoothPurity.IntegralAmbient.NormalizedIntegralPullbackTower
import all WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientReductionPresentation
import all WeilConjectures.SixFunctors.Supporting.OrdinaryIntegralReductionHomology
import all WeilConjectures.SixFunctors.IntegralPublishedPullback.IntegralPublishedTowerEvaluation
import all WeilConjectures.SixFunctors.IntegralPublishedPullback.IntegralPublishedFiniteEvaluation

/-! # Good-representative reduction/pullback augmentation

This is the representative-level part of the coherent reduction mate. It is
separated from the localization descent statement so that the construction can
be proved independently on flat-term K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] HasDerivedCategory.standard scalarReductionExistence
  scalarReductionDerivedExistence Functor.leftAdjoint Functor.mapDerivedCategory
attribute [local implicit_reducible] pullbackTensorReferencePullback
  pullbackTensorSequenceDerived integralOperationsGoodLocalization
  integralOperationsPullbackOnGood integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor integralOperationsPullbackLevel
  integralOperationsRestrict integralPullbackFiniteComplex integralOperationsRoos
  integralOperationsRoosFunctor Functor.ofOpSequence Functor.ofSequence
  coefficientFiniteDerivedRestriction scalarReductionDerivedRestriction
  coefficientSequenceLimit coefficientConstantTowerLimit coefficientConstantTowerEvaluation
  pullbackTensorConstantLimit pullbackTensorRestrictedTower pullbackTensorTowerQ
  unrestrictedIntegralReductionFunctor integralCoefficientSheaf integralCoefficientCommRingSheaf
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  HomologicalComplex.asFunctor
open Opposite
attribute [local instance] scalarReductionExtensionAdditive

-- Finite scalar extension and ordinary pullback commute before localization.
private def quotientSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ordinaryIntegralPullComplex l E f ⋙
        (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ) ≅
      unrestrictedIntegralFiniteComplex l E Y n ⋙
        (integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ) := by
  letI := integralOperationsLevelPullback_additive l E f n
  let b := Functor.isoWhiskerRight (ordinaryAmbientPullIso l E f)
    (scalarReductionExtension l E X n) ≪≫ IntegralAmbient.finitePullComparison l E f n
  exact Functor.mapHomologicalComplexCompIso b (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (scalarReductionExtension l E Y n ⋙
        integralOperationsLevelPullback l E f n)) (.up ℤ)).symm

private theorem quotientSquare_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    (((scalarReductionExtension_adjunction l E X n).choose).mapHomologicalComplex
        (.up ℤ)).unit.app ((ordinaryIntegralPullComplex l E f).obj P) ≫
      ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
        ((quotientSquare l E f n).hom.app P) =
    ((ordinaryIntegralQuotientAugmentation l E f).app P).app (op n) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ((ordinaryIntegralModuleAdjunction l E f).homEquiv _ _).injective
  ext V x
  have h := (ordinaryIntegralQuotientAugmentation_existsUnique l E f).exists.choose_spec
    P n i V.unop x
  have ha := (scalarReductionExtension_adjunction l E X n).choose_spec
  have hn := ((scalarReductionExtension_adjunction l E X n).choose).unit.naturality
    ((ordinaryAmbientPullIso l E f).hom.app (P.X i))
  have hn' := congrArg (fun z ↦ z.val.app (op ((proEtaleBaseChange f).obj V.unop))
    ((((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app V) x)) hn
  simp only [Functor.comp_map, Functor.id_map] at hn'
  change
    (((quotientSquare l E f n).hom.app P).f i).val.app
        (op ((proEtaleBaseChange f).obj V.unop))
      ((((scalarReductionExtension_adjunction l E X n).choose).unit.app
        ((ordinaryIntegralModulePull l E f).obj (P.X i))).val.app
          (op ((proEtaleBaseChange f).obj V.unop))
          ((((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app V) x)) = _
  change
    ((IntegralAmbient.finitePullComparison l E f n).hom.app (P.X i)).val.app
        (op ((proEtaleBaseChange f).obj V.unop))
      (((scalarReductionExtension l E X n).map
        ((ordinaryAmbientPullIso l E f).hom.app (P.X i))).val.app
          (op ((proEtaleBaseChange f).obj V.unop))
          ((((scalarReductionExtension_adjunction l E X n).choose).unit.app
            ((ordinaryIntegralModulePull l E f).obj (P.X i))).val.app
              (op ((proEtaleBaseChange f).obj V.unop))
              ((((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app V) x))) = _
  change
    ((((scalarReductionExtension_adjunction l E X n).choose).unit.app
      ((IntegralAmbient.pull l E f).obj (P.X i))).val.app
        (op ((proEtaleBaseChange f).obj V.unop)))
      ((((ordinaryAmbientPullIso l E f).hom.app (P.X i)).val.app
        (op ((proEtaleBaseChange f).obj V.unop)))
        ((((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app V) x)) =
    (((scalarReductionExtension l E X n).map
      ((ordinaryAmbientPullIso l E f).hom.app (P.X i))).val.app
        (op ((proEtaleBaseChange f).obj V.unop)))
      (((((scalarReductionExtension_adjunction l E X n).choose).unit.app
        ((ordinaryIntegralModulePull l E f).obj (P.X i))).val.app
          (op ((proEtaleBaseChange f).obj V.unop)))
        ((((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app V) x)) at hn'
  rw [← hn']
  let V' := op ((proEtaleBaseChange f).obj V.unop)
  let M := (IntegralAmbient.pull l E f).obj (P.X i)
  have hs := ordinaryAmbientPullIso_unit l E f (P.X i) V.unop x
  have hu := ha M V' (IntegralAmbient.pullSection l E f (P.X i) V.unop x)
  have hg := IntegralAmbient.finitePullComparison_unit l E f n (P.X i) V.unop x
  simp only [IntegralAmbient.pullGenerator, IntegralAmbient.finiteGenerator] at hg
  exact (congrArg (fun y ↦
    ((IntegralAmbient.finitePullComparison l E f n).hom.app (P.X i)).val.app V'
      ((((scalarReductionExtension_adjunction l E X n).choose).unit.app M).val.app V' y))
    hs).trans ((congrArg
      (((IntegralAmbient.finitePullComparison l E f n).hom.app (P.X i)).val.app V')
      hu).trans (hg.trans h.symm))

-- Identify each finite evaluation with the prescribed strict pullback complex.
private def finiteOutput {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E X n).obj
        ((pullbackTensorSequenceDerived l E f).obj
          ((pullbackTensorCalculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj))) ≅
      DerivedCategory.Q.obj (integralPullbackFiniteComplex l E f P.obj n) := by
  let C := ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj
  let D := ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C
  let a := (pullbackTensorSequenceDerived l E f).mapIso
    ((pullbackTensorReductionModel l E Y).app P) ≪≫
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app C
  let j := ((pullbackTensorInverseEvaluationComplex l E f n).app C).symm ≪≫
    ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).mapIso
      (((pullbackTensorReductionEvaluationComplex l E Y n).app P.obj).symm)
  exact (coefficientSequenceDerivedEvaluation l E X n).mapIso a ≪≫
    (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.app D ≪≫
    DerivedCategory.Q.mapIso j

-- The published Roos realization preserves these same finite projections.
private theorem model_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
    (pullbackTensorIntegralPullbackModel l E f).hom.app (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceProjection l E X n).app
        ((pullbackTensorSequenceDerived l E f).obj
          ((pullbackTensorCalculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj))) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        (finiteOutput l E f P n).hom =
    (integralDerivedPullbackComparison l E f).hom.app P ≫
      integralOperationRoosProjection l E X
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
        (integralPullbackFiniteComplex l E f P.obj n) := by
  let C := ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj
  let D := ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C
  let F := pullbackTensorSequenceDerived l E f
  let R := scalarReductionRestriction l E X n
  let a := F.map ((pullbackTensorReductionModel l E Y).hom.app P) ≫
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app C
  let j := (pullbackTensorInverseEvaluationComplex l E f n).inv.app C ≫
    ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map
      ((pullbackTensorReductionEvaluationComplex l E Y n).inv.app P.obj)
  have hq : (integralComparisonRestrictedEvaluationFactors l E X D n).hom ≫
      DerivedCategory.Q.map (pullbackTensorPullbackTowerLevel l E f P.obj n).hom ≫
      R.mapDerivedCategoryFactors.inv.app (integralPullbackFiniteComplex l E f P.obj n) =
    R.mapDerivedCategory.map
      ((coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app D ≫
        DerivedCategory.Q.map j) := by
    have hn := R.mapDerivedCategoryFactors.hom.naturality j
    dsimp only [Functor.comp_map] at hn
    dsimp only [pullbackTensorPullbackTowerLevel, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app_inv, Iso.app_hom]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% (IntegralPublishedPullback.restricted_level_factors l E X D n)]
    dsimp only [R] at hn ⊢
    simp only [← Functor.map_comp, ← Functor.map_comp_assoc]
    change _ ≫ (R.mapDerivedCategoryFactors.hom.app _ ≫
      (DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map j) ≫
        R.mapDerivedCategoryFactors.inv.app _)) = _
    erw [reassoc_of% hn.symm]
    dsimp only [R, coefficientFiniteDerivedRestriction, scalarReductionDerivedRestriction]
    simp only [Iso.hom_inv_id_app]
    erw [Category.comp_id]
    rw [← Functor.map_comp]
  have hm : (pullbackTensorIntegralPullbackModel l E f).hom.app
        (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceLimit l E X).map a ≫
      (pullbackTensorLimitRoos l E X D).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map
        (pullbackTensorPullbackTower l E f P.obj).hom) =
    (integralDerivedPullbackComparison l E f).hom.app P := by
    have h := (pullbackTensorIntegralPullbackModel_existsUnique l E f).exists.choose_spec P
    change (pullbackTensorIntegralPullbackModel l E f).app (DerivedCategory.Q.obj P.obj) = _ at h
    have h' := congrArg (fun i ↦ i.hom ≫
      (pullbackTensorReferencePullbackModel l E f P).hom) h
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at h'
    dsimp only [pullbackTensorReferencePullbackModel] at h'
    simpa only [a, D, C, F, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Functor.map_comp, Category.assoc] using h'
  have h := congrArg (fun t ↦ t ≫ integralOperationRoosProjection l E X
    ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
      R.mapDerivedCategoryFactors.inv.app (integralPullbackFiniteComplex l E f P.obj n)) hm
  simp only [Category.assoc] at h
  erw [reassoc_of% (IntegralPublishedPullback.roos_projection_natural l E
    (pullbackTensorPullbackTower l E f P.obj).hom n)] at h
  erw [reassoc_of% (IntegralPublishedPullback.published_bridge_projection l E X D n)] at h
  erw [reassoc_of% ((coefficientSequenceProjection l E X n).naturality a)] at h
  have hq' := (pullbackTensorPullbackTower_existsUnique l E f P.obj).exists.choose_spec n
  change (pullbackTensorPullbackTower l E f P.obj).app (op n) = _ at hq'
  have hqh := congrArg Iso.hom hq'
  change (pullbackTensorPullbackTower l E f P.obj).hom.app (op n) = _ at hqh
  rw [hqh] at h
  erw [hq] at h
  dsimp only [finiteOutput, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Iso.symm_hom, Functor.map_comp]
  dsimp only [a, j, F, C, D, R] at h
  simpa only [Functor.map_comp, Functor.comp_obj, integralOperationsGoodLocalization,
    ObjectProperty.ι_obj, coefficientFiniteDerivedRestriction, scalarReductionDerivedRestriction,
    Category.assoc] using h

private theorem completion_chain_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E f P) ≫
      integralOperationRoosProjection l E X
        ((integralOperationsPullbackTowerFunctor l E f).obj P) n =
    DerivedCategory.Q.map (((ordinaryIntegralQuotientAugmentation l E f).app P).app
      (op n)) := by
  unfold integralOperationRoosProjection
  rw [← Functor.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  unfold ordinaryIntegralCompletionChain
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc, CochainComplex.mappingCocone.lift_f_fst_f]
  exact congrArg (fun a ↦ a.f i) (Pi.lift_comp_π (fun m : ℕ ↦
    ((ordinaryIntegralQuotientAugmentation l E f).app P).app (op m)) n)

-- The ordinary quotient augmentation is the adjunct of a composite of isomorphisms.
private theorem finite_completion_adjunct_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
    IsIso (((coefficientFiniteAdjunction l E X n).homEquiv _ _).symm
      ((ordinaryIntegralCompletionComparison l E f).app (DerivedCategory.Q.obj P.obj) ≫
        (integralDerivedPullbackComparison l E f).hom.app P ≫
        integralOperationRoosProjection l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
          (integralPullbackFiniteComplex l E f P.obj n))) := by
  let U := (ordinaryIntegralPullComplex l E f).obj P.obj
  let R := scalarReductionRestriction l E X n
  let q := (quotientSquare l E f n).app P.obj
  let c := ordinaryIntegralPullComplexCounit l E f P.obj
  have hc : IsIso c := ordinaryIntegralPullComplexCounit_isIso l E f P
  let k := reductionPull_kflat l E f P.obj P.property
  let m := coefficientFiniteReductionModel l E X U k n
  let z := (coefficientFiniteDerivedExtension l E X n).map c ≫ m.hom ≫
    DerivedCategory.Q.map q.hom
  have hz : IsIso z := by dsimp only [z]; infer_instance
  have hu : (coefficientFiniteAdjunction l E X n).homEquiv _ _
      (m.hom ≫ DerivedCategory.Q.map q.hom) =
    DerivedCategory.Q.map
        (((ordinaryIntegralQuotientAugmentation l E f).app P.obj).app (op n)) ≫
      R.mapDerivedCategoryFactors.inv.app (integralPullbackFiniteComplex l E f P.obj n) := by
    apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
      (integralPullbackFiniteComplex l E f P.obj n))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [Adjunction.homEquiv_unit, Functor.map_comp]
    have hn := R.mapDerivedCategoryFactors.hom.naturality q.hom
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc, coefficientFiniteDerivedRestriction,
      scalarReductionDerivedRestriction]
    erw [hn]
    erw [reassoc_of% (CompletedQuotient.finiteModel_unit l E X U k n)]
    rw [← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (quotientSquare_unit l E f P.obj n)
  have he : (coefficientFiniteAdjunction l E X n).homEquiv _ _ z =
      (ordinaryIntegralCompletionComparison l E f).app (DerivedCategory.Q.obj P.obj) ≫
        (integralDerivedPullbackComparison l E f).hom.app P ≫
        integralOperationRoosProjection l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
        R.mapDerivedCategoryFactors.inv.app (integralPullbackFiniteComplex l E f P.obj n) := by
    dsimp only [z]
    rw [Adjunction.homEquiv_naturality_left, hu]
    have h := (ordinaryIntegralCompletionComparison_existsUnique l E f).exists.choose_spec P
    change (ordinaryIntegralCompletionComparison l E f).app (DerivedCategory.Q.obj P.obj) ≫
      (integralDerivedPullbackComparison l E f).hom.app P = _ at h
    simp only [← Category.assoc] at h ⊢
    erw [h]
    simp only [Category.assoc]
    rw [← Category.assoc (DerivedCategory.Q.map _) _, completion_chain_projection]
  have he' := congrArg ((coefficientFiniteAdjunction l E X n).homEquiv _ _).symm he
  rw [Equiv.symm_apply_apply] at he'
  exact he' ▸ hz

private def reductionMate {C D T : Type*} [Category C] [Category D] [Category T]
    {R : D ⥤ T} {L : T ⥤ D} (adj : R ⊣ L)
    {F : C ⥤ D} {G : C ⥤ T} (a : F ⟶ G ⋙ L) : F ⋙ R ⟶ G where
  app K := (adj.homEquiv _ _).symm (a.app K)
  naturality K K' f := by
    apply (adj.homEquiv _ _).injective
    dsimp only [Functor.comp_map]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact a.naturality f

private theorem reductionMate_unit {C D T : Type*}
    [Category C] [Category D] [Category T]
    {R : D ⥤ T} {L : T ⥤ D} (adj : R ⊣ L)
    {F : C ⥤ D} {G : C ⥤ T} (a : F ⟶ G ⋙ L) (K : C) :
    a.app K = adj.unit.app (F.obj K) ≫ L.map ((reductionMate adj a).app K) :=
  ((adj.homEquiv _ _).apply_symm_apply (a.app K)).symm.trans (adj.homEquiv_unit _ _ _)

private def completionMate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
        (pullbackTensorCalculus l E X).reduction ⟶
      (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f :=
  reductionMate (pullbackTensorCalculus l E X).adjunction
    (G := (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f)
    ((pullComparison l E f) ≫ (pullbackTensorIntegralPullbackModel l E f).hom)

private theorem evaluated_mate {W : Scheme.{u}}
    (T : CoefficientDerivedSystemCalculus l E W)
    {A : DerivedCategory (scalarReductionSource l E W)}
    {N : coefficientSequenceDerived l E W}
    (a : A ⟶ (coefficientSequenceLimit l E W).obj N) (n : ℕ) :
    (coefficientFiniteAdjunction l E W n).homEquiv _ _
      ((T.reductionEvaluation n).inv.app A ≫
        (coefficientSequenceDerivedEvaluation l E W n).map
          ((T.adjunction.homEquiv _ _).symm a)) =
    a ≫ (coefficientSequenceProjection l E W n).app N := by
  rw [T.adjunction.homEquiv_counit, Functor.map_comp, ← Category.assoc]
  have hn := (T.reductionEvaluation n).inv.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc, Adjunction.homEquiv_naturality_left]
  exact congrArg (a ≫ ·) (T.counit_projection N n)

private theorem completionMate_good_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    IsIso ((completionMate l E f).app (DerivedCategory.Q.obj P.obj)) := by
  apply ((pullbackTensorCalculus l E X).isIso_iff_evaluations _).2
  intro n
  let b := (completionMate l E f).app (DerivedCategory.Q.obj P.obj)
  let V := coefficientSequenceDerivedEvaluation l E X n
  let T := pullbackTensorCalculus l E X
  let e := (T.reductionEvaluation n).app
    ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj
      (DerivedCategory.Q.obj P.obj))
  let t := ((coefficientFiniteAdjunction l E X n).homEquiv _ _).symm
    ((ordinaryIntegralCompletionComparison l E f).app (DerivedCategory.Q.obj P.obj) ≫
      (integralDerivedPullbackComparison l E f).hom.app P ≫
      integralOperationRoosProjection l E X
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
        (integralPullbackFiniteComplex l E f P.obj n))
  have ht : IsIso t := finite_completion_adjunct_isIso l E f P n
  have he : e.inv ≫ V.map b ≫ (finiteOutput l E f P n).hom =
    (coefficientFiniteDerivedExtension l E X n).map
      ((pullIso l E f).hom.app (DerivedCategory.Q.obj P.obj)) ≫ t := by
    apply ((coefficientFiniteAdjunction l E X n).homEquiv _ _).injective
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    erw [evaluated_mate l E T]
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    dsimp only [pullComparison, NatTrans.comp_app]
    simp only [Category.assoc]
    erw [model_projection l E f P n]
    simp only [pullComparison, NatTrans.comp_app, Category.assoc]
  have hi : IsIso (e.inv ≫ V.map b ≫ (finiteOutput l E f P n).hom) := by
    rw [he]
    infer_instance
  have : IsIso (V.map b ≫ (finiteOutput l E f P n).hom) :=
    IsIso.of_isIso_comp_left e.inv _
  exact IsIso.of_isIso_comp_right (V.map b) (finiteOutput l E f P n).hom

/-- The normalized pullback/reduction adjunct equation on good representatives.
Source: Stacks 03D2, 07A6, 08TC and 0941; the representative calculation in
`fix-prop-projection-formula.proof.md`.
(blueprint: lem-sf-pullback-reduction-augmentation-good).

Proof: form the natural adjoint mate of the ordinary completion comparison
followed by the strict Roos realization. On good representatives its finite
components identify with the ordinary pullback/scalar-reduction isomorphisms:
the quotient augmentation is their scalar adjunct on generators, and the Roos
realization preserves these finite projections. Conservative finite evaluation
makes the mate invertible on good representatives. Fully faithful precomposition
with the good localization reflects the resulting natural isomorphism. The
hom-set adjunction unit formula gives the asserted equation.
-/
theorem pullbackReductionAugmentation_good {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ a : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
        (pullbackTensorCalculus l E X).reduction ≅
      (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (pullComparison l E f).app (DerivedCategory.Q.obj P.obj) ≫
            (pullbackTensorIntegralPullbackModel l E f).hom.app (DerivedCategory.Q.obj P.obj) =
          (pullbackTensorCalculus l E X).adjunction.unit.app
              ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj
                (DerivedCategory.Q.obj P.obj)) ≫
            (coefficientSequenceLimit l E X).map
              (a.hom.app (DerivedCategory.Q.obj P.obj)) := by
  let b := completionMate l E f
  let W := (Functor.whiskeringLeft _ _ (coefficientSequenceDerived l E X)).obj
    (integralOperationsGoodLocalization l E Y)
  obtain ⟨hW⟩ := good_whisker_fullyFaithful l E Y (coefficientSequenceDerived l E X)
  have : IsIso (W.map b) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro P
    exact completionMate_good_isIso l E f P
  have : IsIso b := hW.isIso_of_isIso_map b
  refine ⟨asIso b, ?_⟩
  intro P
  exact reductionMate_unit (pullbackTensorCalculus l E X).adjunction
    (G := (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f)
    ((pullComparison l E f) ≫ (pullbackTensorIntegralPullbackModel l E f).hom)
    (DerivedCategory.Q.obj P.obj)

end WeilConjectures.IntegralOrdinary
