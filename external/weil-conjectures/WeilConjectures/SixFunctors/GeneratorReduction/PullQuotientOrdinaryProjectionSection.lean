/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge

/-! # Sectionwise ordinary projection of the quotient pullback mate

Source: Stacks 03D7 and 0941; primitive coefficient comparisons in
`fix-prop-coherence.proof.md`.
(blueprint: lem-sf-pull-quotient-ordinary-projection-section)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted constantSheaf
  Functor.leftAdjoint presheafToSheaf
  pullbackTensorSequenceRing completedIntegralCommRingProjectionUnrestricted
  coefficientSequenceCommRingSystem coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSheaf completedIntegralCommRingSheafUnrestricted
attribute [local implicit_reducible] PurCompactSupport.completed pullbackTensorOrdinaryLimit
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  IntegralOnSlice.Site IntegralOnSlice.siteCategory IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring
  proEtaleRingModuleDirectImage integralOperationsLevelPullback
  coefficientProEtaleModulePullback integralOperationsPullbackGenerator
  MorphismProperty Scheme.ProEt Scheme.instCategoryProEt
  CategoryTheory.Category.opposite Quiver.opposite CategoryTheory.CategoryStruct.opposite
  Functor.sheafPushforwardContinuous Prod.sectR SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  coefficientSequenceEvaluation coefficientProEtaleModuleDirectImage
  proEtaleConstantModuleDirectImage proEtaleConstantDirectImageMap coefficientProEtaleDirectRingMap
  pullbackTensorSequenceBase pullbackTensorSequenceDirect SheafOfModules.restrictScalars

private theorem mate_unit (a : IntegralSystemRealization.OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : integralTowerModules l E Y) :
    (proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)).unit.app M ≫
      (proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).map
        ((pullbackTensorOrdinaryAdjunction l E X).unit.app
          ((IntegralSystemRealization.integralOrdinaryPull l E f).obj M) ≫
          (pullbackTensorOrdinaryLimit l E X).map ((a.reductionPull l E f).hom.app M)) =
    (pullbackTensorOrdinaryAdjunction l E Y).unit.app M ≫
      (pullbackTensorOrdinaryLimit l E Y).map
        ((pullbackTensorSequenceAdjunction l E f).unit.app
          ((pullbackTensorOrdinaryReduction l E Y).obj M)) ≫
      (a.comparison f).hom.app
        ((pullbackTensorSequenceInverse l E f).obj
          ((pullbackTensorOrdinaryReduction l E Y).obj M)) := by
  let A := (pullbackTensorOrdinaryAdjunction l E Y).comp
    (pullbackTensorSequenceAdjunction l E f)
  let B := (proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).comp
      (pullbackTensorOrdinaryAdjunction l E X)
  have hconj : conjugateIsoEquiv A B (a.reductionPull l E f) = a.comparison f := by
    change (conjugateIsoEquiv _ _
      ((conjugateIsoEquiv _ _).symm (a.comparison f).symm)).symm = _
    rw [Equiv.apply_symm_apply]
    rfl
  have h := unit_conjugateEquiv A B (a.reductionPull l E f).hom M
  change A.unit.app M ≫ (conjugateIsoEquiv A B (a.reductionPull l E f)).hom.app _ =
    B.unit.app M ≫ _ at h
  rw [hconj] at h
  simpa only [A, B, Adjunction.comp_unit_app, Functor.map_comp,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    IntegralSystemRealization.integralOrdinaryPull, Category.assoc] using h.symm

private theorem mate_projection (a : IntegralSystemRealization.OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : integralTowerModules l E Y)
    (n : ℕ) (V : Y.ProEt) (x : M.val.obj (op V)) :
    let N := (pullbackTensorSequenceInverse l E f).obj
      ((pullbackTensorOrdinaryReduction l E Y).obj M)
    let t := (pullbackTensorOrdinaryAdjunction l E X).unit.app
      ((IntegralSystemRealization.integralOrdinaryPull l E f).obj M) ≫
      (pullbackTensorOrdinaryLimit l E X).map ((a.reductionPull l E f).hom.app M)
    IntegralSystemRealization.ordinaryLimitProjection l E X N n
      ((proEtaleBaseChange f).obj V)
      (t.val.app (op ((proEtaleBaseChange f).obj V))
        (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app (op V) x)) =
    ((pullbackTensorSequenceDirectEvaluation l E f n).hom.app N).val.app (op V)
      (IntegralSystemRealization.ordinaryLimitProjection l E Y
        ((pullbackTensorSequenceDirect l E f).obj N) n V
        (((pullbackTensorOrdinaryAdjunction l E Y).unit.app M ≫
          (pullbackTensorOrdinaryLimit l E Y).map
            ((pullbackTensorSequenceAdjunction l E f).unit.app
              ((pullbackTensorOrdinaryReduction l E Y).obj M))).val.app (op V) x)) := by
  intro N t
  have hm := congrArg (fun k ↦ k.val.app (op V) x) (mate_unit l E a f M)
  have hp := a.projections f N n V
    (((pullbackTensorOrdinaryAdjunction l E Y).unit.app M ≫
      (pullbackTensorOrdinaryLimit l E Y).map
        ((pullbackTensorSequenceAdjunction l E f).unit.app
          ((pullbackTensorOrdinaryReduction l E Y).obj M))).val.app (op V) x)
  unfold IntegralSystemRealization.integralPushSection
    IntegralSystemRealization.finitePushSection at hp
  exact (congrArg
    (IntegralSystemRealization.ordinaryLimitProjection l E X N n
      ((proEtaleBaseChange f).obj V)) hm).trans hp

private theorem projection_map (W : Scheme.{u})
    {M N : coefficientSequenceModules l E W} (k : M ⟶ N) (n : ℕ) (V : W.ProEt)
    (x : ((pullbackTensorOrdinaryLimit l E W).obj M).val.obj (op V)) :
    IntegralSystemRealization.ordinaryLimitProjection l E W N n V
        (((pullbackTensorOrdinaryLimit l E W).map k).val.app (op V) x) =
      ((coefficientSequenceEvaluation l E W n).map k).val.app (op V)
        (IntegralSystemRealization.ordinaryLimitProjection l E W M n V x) := by
  have h := limMap_π ((coefficientSequenceRestriction l E W).map k) (op n)
  have hs := (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.naturality k
  change ((coefficientSequenceRestriction l E W).map k).app (op n) ≫ _ = _ at hs
  have he : (pullbackTensorOrdinaryLimit l E W).map k ≫
      limit.π ((coefficientSequenceRestriction l E W).obj N) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app N =
    limit.π ((coefficientSequenceRestriction l E W).obj M) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app M ≫
      (coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n).map k := by
    change limMap ((coefficientSequenceRestriction l E W).map k) ≫ _ ≫ _ = _
    rw [← Category.assoc, h, Category.assoc, hs]
  unfold IntegralSystemRealization.ordinaryLimitProjection
    IntegralSystemRealization.restrictionSection
  exact congrArg (fun q ↦ q.val.app (op V) x) he

private theorem projection_unit (W : Scheme.{u}) (M : integralTowerModules l E W)
    (n : ℕ) (V : W.ProEt) (x : M.val.obj (op V)) :
    IntegralSystemRealization.ordinaryLimitProjection l E W
      ((pullbackTensorOrdinaryReduction l E W).obj M) n V
      (((pullbackTensorOrdinaryAdjunction l E W).unit.app M).val.app (op V) x) =
    ((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app (op V)
      (((pullbackTensorFiniteAdjunction l E W n).unit.app M).val.app (op V) x) := by
  have h := (pullbackTensorReductionEvaluation_existsUnique l E W n).exists.choose_spec M
  change (pullbackTensorFiniteAdjunction l E W n).homEquiv M _
    ((pullbackTensorReductionEvaluation l E W n).hom.app M) = _ at h
  rw [Adjunction.homEquiv_unit] at h
  exact (congrArg (fun k ↦ k.val.app (op V) x) h).symm

private theorem inverse_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E Y) (n : ℕ) (V : Y.ProEt)
    (x : ((coefficientSequenceEvaluation l E Y n).obj M).val.obj (op V)) :
    ((pullbackTensorSequenceInverseEvaluation l E f n).hom.app M).val.app
      (op ((proEtaleBaseChange f).obj V))
      (integralOperationsPullbackGenerator l E f n
        ((coefficientSequenceEvaluation l E Y n).obj M) V x) =
    ((pullbackTensorSequenceDirectEvaluation l E f n).hom.app
      ((pullbackTensorSequenceInverse l E f).obj M)).val.app (op V)
      (((coefficientSequenceEvaluation l E Y n).map
        ((pullbackTensorSequenceAdjunction l E f).unit.app M)).val.app (op V) x) := by
  have h := (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose_spec M
  change (coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).homEquiv _ _
    ((pullbackTensorSequenceInverseEvaluation l E f n).hom.app M) = _ at h
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.val.app (op V) x) h

private def finiteComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : integralTowerModules l E Y) (n : ℕ) :
    (coefficientSequenceEvaluation l E X n).obj
        ((pullbackTensorSequenceInverse l E f).obj
          ((pullbackTensorOrdinaryReduction l E Y).obj M)) ≅
      (integralOperationsLevelPullback l E f n).obj
        ((unrestrictedIntegralReductionFunctor l E Y n).obj M) :=
  ((pullbackTensorSequenceInverseEvaluation l E f n).app
    ((pullbackTensorOrdinaryReduction l E Y).obj M)).symm ≪≫
    (integralOperationsLevelPullback l E f n).mapIso
      ((pullbackTensorReductionEvaluation l E Y n).app M).symm

private theorem finiteComparison_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : integralTowerModules l E Y) (n : ℕ) (V : Y.ProEt)
    (x : ((unrestrictedIntegralReductionFunctor l E Y n).obj M).val.obj (op V)) :
    (finiteComparison l E f M n).hom.val.app (op ((proEtaleBaseChange f).obj V))
      (((pullbackTensorSequenceInverseEvaluation l E f n).hom.app
        ((pullbackTensorOrdinaryReduction l E Y).obj M)).val.app
          (op ((proEtaleBaseChange f).obj V))
        (integralOperationsPullbackGenerator l E f n
          ((coefficientSequenceEvaluation l E Y n).obj
            ((pullbackTensorOrdinaryReduction l E Y).obj M)) V
          (((pullbackTensorReductionEvaluation l E Y n).hom.app M).val.app (op V) x))) =
      integralOperationsPullbackGenerator l E f n
        ((unrestrictedIntegralReductionFunctor l E Y n).obj M) V x := by
  let e := (pullbackTensorSequenceInverseEvaluation l E f n).app
    ((pullbackTensorOrdinaryReduction l E Y).obj M)
  let q := (pullbackTensorReductionEvaluation l E Y n).app M
  let F := integralOperationsLevelPullback l E f n
  let adj := coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
  have hc : e.hom ≫ (finiteComparison l E f M n).hom = F.map q.inv := by
    simp only [finiteComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp, e, q, F]
  have h := congrArg (fun k ↦ k.val.app (op V) x) (adj.unit.naturality q.hom)
  change integralOperationsPullbackGenerator l E f n _ V (q.hom.val.app (op V) x) =
    (F.map q.hom).val.app (op ((proEtaleBaseChange f).obj V))
      (integralOperationsPullbackGenerator l E f n _ V x) at h
  have hcancel := congrArg (fun k ↦ k.val.app (op ((proEtaleBaseChange f).obj V))
    (integralOperationsPullbackGenerator l E f n _ V x))
    (show F.map q.hom ≫ F.map q.inv = 𝟙 _ by
      rw [← F.map_comp, q.hom_inv_id, F.map_id])
  change (finiteComparison l E f M n).hom.val.app _
    (e.hom.val.app _ (integralOperationsPullbackGenerator l E f n _ V
      (q.hom.val.app (op V) x))) = _
  erw [h]
  exact (congrArg (fun k ↦ k.val.app (op ((proEtaleBaseChange f).obj V))
    ((F.map q.hom).val.app (op ((proEtaleBaseChange f).obj V))
      (integralOperationsPullbackGenerator l E f n _ V x))) hc).trans hcancel

private theorem scalar_unit_tensor (W : Scheme.{u}) (M : integralTowerModules l E W)
    (n : ℕ) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((pullbackTensorFiniteAdjunction l E W n).unit.app M).val.app V x =
      unrestrictedIntegralTensorSection l E W n M V 1 x := by
  have h := (scalarReductionExtension_adjunction l E W n).choose_spec M V x
  dsimp only [pullbackTensorFiniteAdjunction, unrestrictedIntegralTensorSection,
    unrestrictedIntegralReductionFunctor, unrestrictedIntegralReductionExistence,
    scalarReductionExistence] at h ⊢
  exact h

attribute [local irreducible] finiteComparison pullbackTensorOrdinaryReduction
  pullbackTensorOrdinaryAdjunction pullbackTensorSequenceAdjunction
  pullbackTensorSequenceDirectEvaluation pullbackTensorReductionEvaluation
  pullbackTensorSequenceInverseEvaluation
  IntegralSystemRealization.OrdinaryLimitModel.reductionPull

private theorem normalized_projection
    (a : IntegralSystemRealization.OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : integralTowerModules l E Y)
    (n : ℕ) (V : Y.ProEt) (x : M.val.obj (op V)) :
    let N := (pullbackTensorSequenceInverse l E f).obj
      ((pullbackTensorOrdinaryReduction l E Y).obj M)
    let t := (pullbackTensorOrdinaryAdjunction l E X).unit.app
      ((IntegralSystemRealization.integralOrdinaryPull l E f).obj M) ≫
      (pullbackTensorOrdinaryLimit l E X).map ((a.reductionPull l E f).hom.app M)
    (finiteComparison l E f M n).hom.val.app (op ((proEtaleBaseChange f).obj V))
      (IntegralSystemRealization.ordinaryLimitProjection l E X N n
        ((proEtaleBaseChange f).obj V)
        (t.val.app (op ((proEtaleBaseChange f).obj V))
          (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app (op V) x))) =
      integralOperationsPullbackGenerator l E f n
        ((unrestrictedIntegralReductionFunctor l E Y n).obj M) V
        (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x) := by
  intro N t
  let M₀ := (pullbackTensorOrdinaryReduction l E Y).obj M
  let z := ((pullbackTensorOrdinaryAdjunction l E Y).unit.app M).val.app (op V) x
  let y := ((pullbackTensorFiniteAdjunction l E Y n).unit.app M).val.app (op V) x
  let η := (pullbackTensorSequenceAdjunction l E f).unit.app M₀
  let c := (finiteComparison l E f M n).hom.val.app (op ((proEtaleBaseChange f).obj V))
  let d := ((pullbackTensorSequenceDirectEvaluation l E f n).hom.app N).val.app (op V)
  let e := ((coefficientSequenceEvaluation l E Y n).map η).val.app (op V)
  let b := ((pullbackTensorReductionEvaluation l E Y n).hom.app M).val.app (op V)
  have hm := mate_projection l E a f M n V x
  have hp := projection_map l E Y η n V z
  have hu := projection_unit l E Y M n V x
  have hi := inverse_unit l E f M₀ n V (b y)
  have hc := finiteComparison_unit l E f M n V y
  have hs := scalar_unit_tensor l E Y M n (op V) x
  exact (congrArg c hm).trans
    ((congrArg (fun w ↦ c (d w)) hp).trans
      ((congrArg (fun w ↦ c (d (e w))) hu).trans
        ((congrArg c hi.symm).trans
          (hc.trans (congrArg (integralOperationsPullbackGenerator l E f n
            ((unrestrictedIntegralReductionFunctor l E Y n).obj M) V) hs)))))

private theorem projected_map_eq
    (a : IntegralSystemRealization.OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : OpenFactorCoherence.Pull l E f)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ) :
    let M := P.X i
    let N := (pullbackTensorSequenceInverse l E f).obj
      ((pullbackTensorOrdinaryReduction l E Y).obj M)
    let t := (pullbackTensorOrdinaryAdjunction l E X).unit.app
      ((IntegralSystemRealization.integralOrdinaryPull l E f).obj M) ≫
      (pullbackTensorOrdinaryLimit l E X).map ((a.reductionPull l E f).hom.app M)
    t ≫ limit.π ((coefficientSequenceRestriction l E X).obj N) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app N ≫
        (scalarReductionRestriction l E X n).map (finiteComparison l E f M n).hom =
      ((((IntegralOnSlice.augmentation l E X none).app
        ((OpenFactorCoherence.pullCx l E f).obj P)).app (op n) ≫
        (p.tower.hom.app P).app (op n)).f i) := by
  intro M N t
  apply ((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).homEquiv M _).injective
  simp only [Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change (finiteComparison l E f M n).hom.val.app
    (op ((proEtaleBaseChange f).obj V.unop))
    (IntegralSystemRealization.ordinaryLimitProjection l E X N n
      ((proEtaleBaseChange f).obj V.unop)
      (t.val.app _ (((proEtaleRingModuleAdjunction f
        ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app V x))) = _
  rw [normalized_projection]
  have haug := (IntegralOnSlice.augmentation_existsUnique l E X none).exists.choose_spec
    ((OpenFactorCoherence.pullCx l E f).obj P) n i
    (op ((proEtaleBaseChange f).obj V.unop))
    (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app V x)
  change (((((IntegralOnSlice.augmentation l E X none).app _).app (op n)).f i).val.app
    _ _) = _ at haug
  change _ = (((p.tower.hom.app P).app (op n)).f i).val.app _
    (((((IntegralOnSlice.augmentation l E X none).app _).app (op n)).f i).val.app _ _)
  exact (p.generators P n i V.unop x).symm.trans
    (congrArg ((((p.tower.hom.app P).app (op n)).f i).val.app
      (op ((proEtaleBaseChange f).obj V.unop))) haug).symm

private theorem tower_level {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ) :
    let N := (pullbackTensorSequenceInverse l E f).obj
      ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i))
    ((pullbackTensorPullbackTower l E f P).hom.app (op n)).f i =
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app N ≫
        (scalarReductionRestriction l E X n).map
          (finiteComparison l E f (P.X i) n).hom := by
  intro N
  have h := (pullbackTensorPullbackTower_existsUnique l E f P).exists.choose_spec n
  change (pullbackTensorPullbackTower l E f P).app (op n) = _ at h
  have hi := congrArg (fun e ↦ e.hom.f i) h
  change _ = (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app N ≫
    (scalarReductionRestriction l E X n).map
      ((pullbackTensorSequenceInverseEvaluation l E f n).inv.app
        ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i))) ≫
    (scalarReductionRestriction l E X n).map
      ((integralOperationsLevelPullback l E f n).map
        ((pullbackTensorReductionEvaluation l E Y n).inv.app (P.X i))) at hi
  apply hi.trans
  rw [← Functor.map_comp]
  unfold finiteComparison
  rfl

/-- The finite projection identity on one cochain degree and one section.

Source: Stacks Project, Tags 03D7, 03EL and 0941; current blueprint
`sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`,
ordinary projected-section calculation.

Proof: evaluate the ordinary reduction/limit mate at the chosen degree and
section. The unit identity for the conjugate adjunction identifies its finite
projection with the scalar adjunction unit. The inverse-image and reduction
evaluation normalizations cancel the comparison factors in the strict pullback
tower. The generators equation of the prescribed pull presentation identifies
the resulting finite unit with the quotient augmentation followed by the tower.
The argument is purely sectionwise and applies to zero complexes and empty
sites as well.
-/
theorem pullQuotientOrdinaryProjection_section
    (a : IntegralSystemRealization.OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : OpenFactorCoherence.Pull l E f)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
    (V : X.ProEtᵒᵖ)
    (x : (((OpenFactorCoherence.pullCx l E f).obj P).X i).val.obj V) :
    (((((pullbackTensorOrdinaryAdjunction l E X).mapHomologicalComplex (.up ℤ)).unit.app
      ((OpenFactorCoherence.pullCx l E f).obj P) ≫
      ((pullbackTensorOrdinaryLimit l E X).mapHomologicalComplex (.up ℤ)).map
        (a.reductionPullComplex l E f P) ≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (coefficientSequenceRestriction l E X ⋙
          pullbackTensorConstantLimit l E X)) (.up ℤ)).inv.app
        (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
          (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
            (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P))) ≫
      (pullbackTensorPullbackTower l E f P).hom.app (op n)).f i).val.app V x) =
      (((((IntegralOnSlice.augmentation l E X none).app
        ((OpenFactorCoherence.pullCx l E f).obj P)).app (op n) ≫
        (p.tower.hom.app P).app (op n)).f i).val.app V x) := by
  have h := projected_map_eq l E a f p P n i
  have ht := tower_level l E f P n i
  dsimp only at h ht
  rw [← ht] at h
  have hs := congrArg (fun k ↦ k.val.app V x) h
  convert hs using 1 <;> rfl

end WeilConjectures.GeneratorReduction
