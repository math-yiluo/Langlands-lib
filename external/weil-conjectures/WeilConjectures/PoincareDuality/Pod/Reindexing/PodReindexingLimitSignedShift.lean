/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.PoincareDuality.Pod.PodNativeRoosFunctorComparison
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.PoincareDuality.Pod.PodNormalizedRoosComparisonShift
import all WeilConjectures.PoincareDuality.Pod.PodStrictRoosReindexShift
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingSignedRoosShift
import all WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Signed shifts of the normalized whole-tower limit comparison -/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 10000] WeilConjectures.podLimitCommShift

attribute [local instance 50000] WeilConjectures.podSheafCanonicalPreadditive

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Keep the coefficient universe explicit during sheafification synthesis.
private instance (priority := 20000) fixedAbSheafify (Z : Scheme.{u}) :
    HasSheafify (ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Z

private instance (priority := 20000) fixedAbBijective (Z : Scheme.{u}) :
    (ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Z

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The localization functor of strict coefficient systems. -/
private abbrev coefficientQ (W : Scheme.{u}) :
    CochainComplex (coefficientSequenceModules l E W) ℤ ⥤ coefficientSequenceDerived l E W :=
  DerivedCategory.Q

/-- The K-injective-normalized limit-to-Roos comparison as a natural isomorphism. -/
private def podLimitRoosIso (W : Scheme.{u}) (ρ : IntegralComparisonRoosModel l E W) :
    coefficientQ l E W ⋙ coefficientSequenceLimit l E W ≅
      ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙ roosF) ⋙
        DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l E W) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ρ.comparison ≪≫
      Functor.isoWhiskerRight (podNativeRoosIso (A := scalarReductionSource l E W))
        DerivedCategory.Q) ≪≫
    (Functor.associator _ _ _).symm

private theorem podLimitRoosIso_hom_app (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (podLimitRoosIso l E W ρ).hom.app C = (podLimitRoos l E ρ C).hom := by
  have e : (podNativeRoosIso (A := scalarReductionSource l E W)).hom.app
      (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C) =
      𝟙 _ := rfl
  simp only [coefficientSequenceLimit, comp_obj, podLimitRoosIso, isoWhiskerLeft_trans,
    Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, associator_inv_app, whiskerRight_app, associator_hom_app,
    whiskerLeft_app, e, Category.comp_id, Category.id_comp, podLimitRoos]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

attribute [local instance] CategoryTheory.RoosConeCalculus.roosCommShift

private instance podLimitRoosIso_commShift (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E W) :
    NatTrans.CommShift (podLimitRoosIso l E W ρ).hom ℤ := by
  have h : NatTrans.CommShift (ρ.comparison.hom ≫
      Functor.whiskerRight (podNativeRoosIso (A := scalarReductionSource l E W)).hom
        DerivedCategory.Q) ℤ :=
    podNormalizedRoosComparisonCommShift l E W ρ
      CategoryTheory.RoosConeCalculus.roosCommShift
      CategoryTheory.RoosConeCalculus.shift_augmentation
  let RW := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)
  exact (inferInstance : NatTrans.CommShift ((Functor.associator (coefficientQ l E W)
      (coefficientSequenceDerivedRestriction l E W) (coefficientConstantTowerLimit l E W)).inv ≫
    Functor.whiskerRight (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom
      (coefficientConstantTowerLimit l E W) ≫
    (Functor.associator RW DerivedCategory.Q (coefficientConstantTowerLimit l E W)).hom ≫
    Functor.whiskerLeft RW (ρ.comparison.hom ≫ Functor.whiskerRight
        (podNativeRoosIso (A := scalarReductionSource l E W)).hom DerivedCategory.Q) ≫
    (Functor.associator RW roosF DerivedCategory.Q).inv) ℤ)

/-- The source presentation: limit, then ordinary reindexing, read on Roos complexes. -/
private def podSourcePresentation {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) :
    coefficientQ l E Y ⋙ coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ≅
      (((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙ roosF) ⋙
        isoReductionIntegralComplex l E g) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (podLimitRoosIso l E Y D.sourceRoos) (podOrdinaryReindex l E g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm

/-- The target presentation: system pullback, then limit, read on Roos complexes. -/
private def podTargetPresentation {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) :
    coefficientQ l E Y ⋙ integralComparisonDerivedSequencePullback l E g ⋙
        coefficientSequenceLimit l E X ≅
      ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ) ⋙
        (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙ roosF) ⋙
        DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors
      (coefficientSequenceLimit l E X) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (podLimitRoosIso l E X D.targetRoos) ≪≫
    (Functor.associator _ _ _).symm

/-- Composition of shift-compatible transformations, with the middle shift unified. -/
private theorem commShift_comp_of {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] {F₁ F₂ F₃ : C ⥤ D}
    {_ : F₁.CommShift ℤ} {_ : F₂.CommShift ℤ} {_ : F₃.CommShift ℤ}
    {τ : F₁ ⟶ F₂} {τ' : F₂ ⟶ F₃} (h : NatTrans.CommShift τ ℤ)
    (h' : NatTrans.CommShift τ' ℤ) : NatTrans.CommShift (τ ≫ τ') ℤ :=
  inferInstance

/-- Both presentations commute with shifts and have the expected components. -/
private theorem podReindexingLimitPresentations {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) :
    ∃ (a : coefficientQ l E Y ⋙ coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ≅
        (((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙ roosF) ⋙
          isoReductionIntegralComplex l E g) ⋙ DerivedCategory.Q)
      (b : coefficientQ l E Y ⋙ integralComparisonDerivedSequencePullback l E g ⋙
          coefficientSequenceLimit l E X ≅
        ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ) ⋙
          (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙ roosF) ⋙
          DerivedCategory.Q),
      NatTrans.CommShift a.hom ℤ ∧ NatTrans.CommShift b.hom ℤ ∧
      (∀ C, a.hom.app C =
        (podOrdinaryReindex l E g).map (podLimitRoos l E D.sourceRoos C).hom ≫
          (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _) ∧
      (∀ C, b.hom.app C =
        (coefficientSequenceLimit l E X).map
          ((integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app C) ≫
          (podLimitRoos l E D.targetRoos _).hom) := by
  refine ⟨podSourcePresentation l E g D, podTargetPresentation l E g D, ?_, ?_, ?_, ?_⟩
  · let RY := (coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)
    have t1 : NatTrans.CommShift (Functor.associator (coefficientQ l E Y)
        (coefficientSequenceLimit l E Y) (podOrdinaryReindex l E g)).inv ℤ := inferInstance
    have t2 : NatTrans.CommShift (Functor.whiskerRight (podLimitRoosIso l E Y D.sourceRoos).hom
        (podOrdinaryReindex l E g)) ℤ := inferInstance
    have t3 : NatTrans.CommShift
        (Functor.associator (RY ⋙ roosF) DerivedCategory.Q (podOrdinaryReindex l E g)).hom ℤ :=
      inferInstance
    have t4 : NatTrans.CommShift (Functor.whiskerLeft (RY ⋙ roosF)
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom) ℤ := inferInstance
    have t5 : NatTrans.CommShift (Functor.associator (RY ⋙ roosF)
        (isoReductionIntegralComplex l E g) DerivedCategory.Q).inv ℤ := inferInstance
    exact commShift_comp_of t1 (commShift_comp_of t2 (commShift_comp_of t3
      (commShift_comp_of t4 t5)))
  · let RX := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
    let P := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
    have t1 : NatTrans.CommShift (Functor.associator (coefficientQ l E Y)
        (integralComparisonDerivedSequencePullback l E g)
        (coefficientSequenceLimit l E X)).inv ℤ := inferInstance
    have t2 : NatTrans.CommShift (Functor.whiskerRight
        (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom
        (coefficientSequenceLimit l E X)) ℤ := inferInstance
    have t3 : NatTrans.CommShift
        (Functor.associator P DerivedCategory.Q (coefficientSequenceLimit l E X)).hom ℤ :=
      inferInstance
    have t4 : NatTrans.CommShift
        (Functor.whiskerLeft P (podLimitRoosIso l E X D.targetRoos).hom) ℤ := inferInstance
    have t5 : NatTrans.CommShift
        (Functor.associator P (RX ⋙ roosF) DerivedCategory.Q).inv ℤ := inferInstance
    exact commShift_comp_of t1 (commShift_comp_of t2 (commShift_comp_of t3
      (commShift_comp_of t4 t5)))
  · intro C
    simp only [comp_obj, podSourcePresentation, Iso.trans_hom, Iso.symm_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, associator_inv_app, whiskerRight_app,
      podLimitRoosIso_hom_app, associator_hom_app, Category.comp_id, Category.id_comp]
    rfl
  · intro C
    let P := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
    have h : (podTargetPresentation l E g D).hom.app C = 𝟙 _ ≫
        (coefficientSequenceLimit l E X).map
          ((integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app C) ≫
        𝟙 _ ≫ (podLimitRoosIso l E X D.targetRoos).hom.app (P.obj C) ≫ 𝟙 _ := rfl
    rw [h, podLimitRoosIso_hom_app]
    simp only [Category.id_comp]
    exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- The strict Roos reindexing square, read through the native Roos shift functors. -/
private theorem podReindexingStrictNativeShift {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hnat : PodCompletionReindex.RoosNaturality l E g D)
    (hshift : PodCompletionReindex.RoosShift l E g D)
    (hgen : PodCompletionReindex.RestrictedGenerators l E g D)
    (hSY : D.shiftSource.Laws) (hSX : D.shiftTarget.Laws)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (r : ℤ) :
    let RY := (coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)
    let RX := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
    let P := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
    let U := (RY ⋙ roosF) ⋙ isoReductionIntegralComplex l E g
    let V := P ⋙ RX ⋙ roosF
    let f (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) : U.obj C ⟶ V.obj C :=
      (D.roos (podRestrictedTower l E C)).hom ≫
        integralOperationsRoosFunctor.map (D.restricted C).hom
    (U.commShiftIso r).hom.app C ≫ (f C)⟦r⟧' =
      f (C⟦r⟧) ≫ (V.commShiftIso r).hom.app C := by
  intro RY RX P U V f
  have hs := podStrictRoosReindexShift l E g D hnat hshift hgen hSX C r
  dsimp only at hs
  simp only [U, V, f, Functor.commShiftIso_comp_hom_app]
  rw [roosShift_hom_ext_complex_sheaf _ D.shiftSource hSY,
    roosShift_hom_ext_complex_sheaf _ D.shiftTarget hSX]
  rw [Functor.comp_map, ← podNativeRoosMap_eq, ← podNativeRoosMap_eq, ← podNativeRoosMap_eq]
  erw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  exact hs

-- The calculation pastes several strict and localized shift squares.
/-- The normalized whole-tower limit reindexing commutes with integer shifts.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 0941 and 011G
(blueprint: lem-pod-reindexing-limit-signed-shift-s8).

Proof: the restricted generator formula gives the same termwise map in degree i+r
before and after shifting; hence its restriction comparison commutes with shift.
Use naturality and the RoosShift law to paste this strict-tower square with the
source and target signed Roos comparisons. The two normalized limit-to-Roos
identities then turn LimitModel into the shift square for D.limit at Q(C).
Cancel the invertible Roos and localization comparisons. Finally the essential
surjectivity of Q and naturality extend the identity to all derived objects. -/
theorem podReindexingLimitSignedShift
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hnat : PodCompletionReindex.RoosNaturality l E g D)
    (hshift : PodCompletionReindex.RoosShift l E g D)
    (hgen : PodCompletionReindex.RestrictedGenerators l E g D)
    (hmodel : PodCompletionReindex.LimitModel l E g D)
    (hSY : D.shiftSource.Laws) (hSX : D.shiftTarget.Laws) :
    NatTrans.CommShift D.limit.hom ℤ := by
  let := CategoryTheory.RoosConeCalculus.roosCommShift
    (A := scalarReductionSource l E Y)
  let := CategoryTheory.RoosConeCalculus.roosCommShift
    (A := scalarReductionSource l E X)
  let RY := (coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)
  let RX := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
  let P := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
  let F := isoReductionIntegralComplex l E g
  let HY := RY ⋙ roosF
  let HX := RX ⋙ roosF
  let U := HY ⋙ F
  let V := P ⋙ HX
  obtain ⟨a, b, ha, hb, haC, hbC⟩ := podReindexingLimitPresentations l E g D
  let ν := a.symm ≪≫ Functor.isoWhiskerLeft (coefficientQ l E Y) D.limit ≪≫ b
  let f (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
      U.obj C ⟶ V.obj C := (D.roos (podRestrictedTower l E C)).hom ≫
        integralOperationsRoosFunctor.map (D.restricted C).hom
  have hnC (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
      ν.hom.app C = DerivedCategory.Q.map (f C) := by
    apply (cancel_epi (a.hom.app C)).mp
    dsimp only [ν, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    erw [Iso.hom_inv_id_app_assoc]
    rw [haC, hbC]
    dsimp only [f]
    erw [DerivedCategory.Q.map_comp]
    erw [Category.assoc]
    exact (hmodel C).symm
  have hf (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (r : ℤ) :
      (U.commShiftIso r).hom.app C ≫ (f C)⟦r⟧' =
        f (C⟦r⟧) ≫ (V.commShiftIso r).hom.app C :=
    podReindexingStrictNativeShift l E g D hnat hshift hgen hSY hSX C r
  have : NatTrans.CommShift ν.hom ℤ := commShift_Q_components U V ν.hom f hnC hf
  have : NatTrans.CommShift (Functor.whiskerLeft (coefficientQ l E Y) D.limit.hom) ℤ :=
    commShift_of_conjugate a b _ ν.hom (by
      dsimp only [ν, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp])
  exact NatTrans.CommShift.of_whiskerLeft D.limit.hom (coefficientQ l E Y)
    (fun A ↦ ⟨DerivedCategory.Q.objPreimage A,
      (DerivedCategory.Q.objObjPreimageIso A).inv, inferInstance⟩)

end WeilConjectures
