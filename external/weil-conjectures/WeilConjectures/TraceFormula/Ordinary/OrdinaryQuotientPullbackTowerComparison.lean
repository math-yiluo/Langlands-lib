/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels

import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackSuccessor

/-! # Strict pullback comparison for ordinary quotient systems

Source: Stacks 06YY, 0941 and 099N(5), the strict quotient-system construction.
(blueprint: lem-trf-ordinary-quotient-pullback-tower-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingProjectionUnrestricted
namespace OrdinaryTowerProof
private theorem comp_identity_sections
    {C : Type v} [Category C] {D : Type w} [Category D] {B : Type*} [Category B]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : GrothendieckTopology B} {F : C ⥤ D} {G : D ⥤ B}
    [F.IsContinuous J K] [G.IsContinuous K I]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {T : Sheaf I RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K I).obj T) :
    ∀ M U x, HEq (((SheafOfModules.pushforwardComp.{u} φ ψ).hom.app M).val.app U x) x := by
  intro M U x
  exact heq_of_eq (SheafOfModules.pushforwardComp_hom_app_val_app φ ψ M U x)

private theorem comp_inv_identity_sections
    {C : Type v} [Category C] {D : Type w} [Category D] {B : Type*} [Category B]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : GrothendieckTopology B} {F : C ⥤ D} {G : D ⥤ B}
    [F.IsContinuous J K] [G.IsContinuous K I]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {T : Sheaf I RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K I).obj T) :
    ∀ M U x, HEq (((SheafOfModules.pushforwardComp.{u} φ ψ).inv.app M).val.app U x) x := by
  intro M U x
  exact heq_of_eq (SheafOfModules.pushforwardComp_inv_app_val_app φ ψ M U x)

private theorem congr_identity_sections
    {C : Type v} [Category C] {D : Type w} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] {R : Sheaf K RingCat.{u}}
    {S : Sheaf J RingCat.{u}}
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (h : φ = ψ) :
    ∀ M U (x : ((SheafOfModules.pushforward.{u} φ).obj M).val.obj U),
      HEq (((SheafOfModules.pushforwardCongr h).hom.app M).val.app U x) x := by
  intro M U x
  exact heq_of_eq (SheafOfModules.pushforwardCongr_hom_app_val_app h M U x)

private theorem trans_identity_sections
    {C : Type v} [Category C] {D : Type w} [Category D]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {F G H : D ⥤ SheafOfModules.{u} R} (e : F ≅ G) (d : G ≅ H)
    (he : ∀ M U (x : (F.obj M).val.obj U), HEq ((e.hom.app M).val.app U x) x)
    (hd : ∀ M U (x : (G.obj M).val.obj U), HEq ((d.hom.app M).val.app U x) x) :
    ∀ M U (x : (F.obj M).val.obj U), HEq (((e ≪≫ d).hom.app M).val.app U x) x := by
  intro M U x
  dsimp only [Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val]
  rw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact (hd M U _).trans (he M U x)

end OrdinaryTowerProof

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

namespace OrdinaryTowerProof

attribute [local irreducible] Functor.leftAdjoint

attribute [local irreducible] integralComparisonSequenceRingMap
  coefficientProEtaleDirectRingMap in
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralComparisonSequenceBaseChange integralComparisonSequenceDirectImage
  Functor.sheafPushforwardContinuous Prod.sectR SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  coefficientSequenceEvaluation coefficientProEtaleModuleDirectImage in
/-- Direct image on sequences commutes with evaluation by the identity on sections.
Source: Stacks 03D1 and 0941 (blueprint: lem-trf-ordinary-quotient-pullback-tower-comparison).
Proof: both functors evaluate M at (n, f-basechange U) with scalar action through
the same constant-section coefficient map. The identity section maps give the
natural isomorphism. Sectionwise extensionality proves uniqueness. -/
private theorem canonical_exists
    {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    ∃ e : integralComparisonSequenceDirectImage l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        coefficientProEtaleModuleDirectImage.{t, u} f
          (CommRingCat.of (ULift.{t + 1} (finiteCoefficientRing l E (n + 1)))),
      ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
        (x : ((coefficientSequenceEvaluation l E Y n).obj
          ((integralComparisonSequenceDirectImage l E f).obj M)).val.obj (op U)),
        HEq ((e.hom.app M).val.app (op U) x) x := by
  unfold integralComparisonSequenceDirectImage
  let a := eqToHom (coefficientSequenceEvaluationRing_eq l E Y n).symm
  let b := eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm
  let φ : (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E Y) ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            (coefficientSequenceCommRingSheaf l E X)) :=
    ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
  let ψ : integralCoefficientSheaf l E Y n ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj (integralCoefficientSheaf l E X n) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (finiteCoefficientRing l E (n + 1))))).hom
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
  have h : a ≫ ((Prod.sectR n Y.ProEt).sheafPushforwardContinuous RingCat.{max u (t + 1)}
      (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology Y))).map φ =
      ψ ≫ ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).map b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have ha : a.hom.app U = 𝟙 _ := by
      dsimp only [a]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hb : b.hom.app ((proEtaleBaseChange f).op.obj U) = 𝟙 _ := by
      dsimp only [b]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change a.hom.app U ≫ φ.hom.app (op (n, U.unop)) =
      ψ.hom.app U ≫ b.hom.app ((proEtaleBaseChange f).op.obj U)
    rw [ha, hb]
    unfold φ ψ integralComparisonSequenceRingMap integralComparisonSequenceRingComponent
    rfl
  have : (Prod.sectR n Y.ProEt ⋙ integralComparisonSequenceBaseChange f).IsContinuous
      (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology X)) :=
    Functor.isContinuous_comp _ _ _ (coefficientSequenceTopology (ProEt.topology Y)) _
  let e₁ := SheafOfModules.pushforwardComp (F := Prod.sectR n Y.ProEt)
    (G := integralComparisonSequenceBaseChange f) a φ
  let e₂ := SheafOfModules.pushforwardCongr
    (F := Prod.sectR n Y.ProEt ⋙ integralComparisonSequenceBaseChange f)
    (S := integralCoefficientSheaf l E Y n)
    (R := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E X)) h
  let e₃ := (SheafOfModules.pushforwardComp (F := proEtaleBaseChange f)
    (G := Prod.sectR n X.ProEt) ψ b).symm
  let e := e₁ ≪≫ e₂ ≪≫ e₃
  have he : ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEtᵒᵖ)
      (x : ((coefficientSequenceEvaluation l E Y n).obj
        ((SheafOfModules.pushforward φ).obj M)).val.obj U),
      HEq ((e.hom.app M).val.app U x) x := by
    apply trans_identity_sections e₁ (e₂ ≪≫ e₃)
    · exact comp_identity_sections (F := Prod.sectR n Y.ProEt)
        (G := integralComparisonSequenceBaseChange f) a φ
    · apply trans_identity_sections e₂ e₃
      · exact congr_identity_sections
          (F := Prod.sectR n Y.ProEt ⋙ integralComparisonSequenceBaseChange f)
          (S := integralCoefficientSheaf l E Y n)
          (R := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            (coefficientSequenceCommRingSheaf l E X)) h
      · exact comp_inv_identity_sections (F := proEtaleBaseChange f)
          (G := Prod.sectR n X.ProEt) ψ b
  exact ⟨e, (fun M U x ↦ he M (op U) x)⟩

attribute [local irreducible] coefficientSequenceCommRingSheaf integralCoefficientCommRingSheaf

private def directEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :=
  (canonical_exists l E f n).choose

private theorem directEvaluation_sections {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (N : coefficientSequenceModules l E X) (U : Y.ProEt)
    (x : ((coefficientSequenceEvaluation l E Y n).obj
      ((integralComparisonSequenceDirectImage l E f).obj N)).val.obj (op U)) :
    HEq (((directEvaluation l E f n).hom.app N).val.app (op U) x) x :=
  (canonical_exists l E f n).choose_spec N U x

attribute [local irreducible] directEvaluation

private def inverseEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n ≅
      integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E X n := by
  let adj := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)
  let adjn := coefficientProEtaleModuleAdjunction.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (finiteCoefficientRing l E (n + 1))))
  let d := directEvaluation l E f n
  have : ((𝟭 ℕ).prod (proEtaleBaseChange f)).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) :=
    integralComparisonSequenceBaseChange_continuous f
  have : IsIso ((mateEquiv adj adjn).symm d.hom) :=
    SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
        RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E Y))
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
        RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E X)) n
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
        RingCat.{max u (t + 1)})).map (integralComparisonSequenceRingMap l E f))
      (integralCoefficientSheaf l E Y n) (integralCoefficientSheaf l E X n)
      (coefficientSequenceEvaluationRing_eq l E Y n)
      (coefficientSequenceEvaluationRing_eq l E X n)
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
        RingCat.{max u (t + 1)})).map
        (coefficientProEtaleDirectRingMap.{t, u} f
          (CommRingCat.of (ULift.{t + 1} (finiteCoefficientRing l E (n + 1))))))
      (integralComparisonSequencePullback l E f) (integralOperationsLevelPullback l E f n)
      adj adjn d
  exact asIso ((mateEquiv adj adjn).symm d.hom)

private theorem inverseEvaluation_hom {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    (inverseEvaluation l E f n).hom =
      ((mateEquiv
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
        (coefficientProEtaleModuleAdjunction.{t, u} f
          (CommRingCat.of (ULift.{t + 1} (finiteCoefficientRing l E (n + 1)))))).symm
            (directEvaluation l E f n).hom) := rfl

private theorem evaluation_section_heq {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    HEq (coefficientEvaluationSection l E X N n U x) x := by rfl

private theorem evaluation_map_section {X : Scheme.{t}}
    {N N' : coefficientSequenceModules l E X} (g : N ⟶ N')
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    (((coefficientSequenceEvaluation l E X n).map g).val.app U)
      (coefficientEvaluationSection l E X N n U x) =
    coefficientEvaluationSection l E X N' n U
      (g.val.app (op (n, U.unop)) x) := rfl

attribute [local irreducible] inverseEvaluation

private theorem inverseEvaluation_unit {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (N : coefficientSequenceModules l E Y) (U : Y.ProEt)
    (x : N.val.obj (op (n, U))) :
    (((inverseEvaluation l E f n).hom.app N).val.app
      (op ((proEtaleBaseChange f).obj U)))
      (integralOperationsPullbackGenerator l E f n
        ((coefficientSequenceEvaluation l E Y n).obj N) U
        (coefficientEvaluationSection l E Y N n (op U) x)) =
      coefficientEvaluationSection l E X
        ((integralComparisonSequencePullback l E f).obj N) n
        (op ((proEtaleBaseChange f).obj U))
        (integralComparisonSequenceGenerator l E f N n U x) := by
  have h := unit_mateEquiv_symm
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
    (coefficientProEtaleModuleAdjunction.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (finiteCoefficientRing l E (n + 1)))))
    (directEvaluation l E f n).hom N
  have hs := congrArg (fun a ↦ a.val.app (op U)
    (coefficientEvaluationSection l E Y N n (op U) x)) h
  have hd := directEvaluation_sections l E f n
    ((integralComparisonSequencePullback l E f).obj N) U
    (((coefficientSequenceEvaluation l E Y n).map
      ((Adjunction.ofIsRightAdjoint
        (integralComparisonSequenceDirectImage l E f)).unit.app N)).val.app (op U)
          (coefficientEvaluationSection l E Y N n (op U) x))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hs
  rw [inverseEvaluation_hom]
  apply eq_of_heq
  have h := (heq_of_eq hs.symm).trans hd
  have h' := evaluation_map_section l E
    ((Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E f)).unit.app N) n (op U) x
  exact ((h.trans (heq_of_eq h')).trans (evaluation_section_heq l E _ n (op U) _)).trans
    (evaluation_section_heq l E _ n (op ((proEtaleBaseChange f).obj U)) _).symm

private abbrev pullTower {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
    (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

private theorem eqToHom_section {C : Type v} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {N N' : SheafOfModules.{u} R} (h : N = N') (U : Cᵒᵖ) (x : N.val.obj U) :
    HEq ((eqToHom h).val.app U x) x := by
  subst N'
  rfl

private theorem restrictionEvaluation_section {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    (((eqToIso (coefficientSequenceRestriction_evaluation l E X n)).app N).hom.val.app U)
      (integralComparisonRestrictedSection l E X N n U x) =
        coefficientEvaluationSection l E X N n U x := by
  simp only [Iso.app_hom, eqToIso.hom, eqToHom_app]
  apply eq_of_heq
  have h := eqToHom_section
    (congrArg (fun F ↦ F.obj N) (coefficientSequenceRestriction_evaluation l E X n))
    U (integralComparisonRestrictedSection l E X N n U x)
  exact (h.trans (cast_heq _ _)).trans (evaluation_section_heq l E N n U x).symm

private def moduleLevel {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y) (n : ℕ) :
    (M.tensor ⋙ integralComparisonSequencePullback l E f) ⋙
        coefficientSequenceRestriction l E X ⋙
          (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n) ≅
      (scalarReductionExtension l E Y n ⋙ integralOperationsLevelPullback l E f n) ⋙
        scalarReductionRestriction l E X n :=
  Functor.isoWhiskerLeft (M.tensor ⋙ integralComparisonSequencePullback l E f)
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.associator _ _ _ ) ≪≫
        Functor.isoWhiskerLeft M.tensor (inverseEvaluation l E f n).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (M.evaluation n) (integralOperationsLevelPullback l E f n))
      (scalarReductionRestriction l E X n)

attribute [local irreducible] moduleLevel

private def level {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    ((pullTower l E f).obj ((M.quotient l E Y).obj P)).obj (op n) ≅
      ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (moduleLevel l E f M n).app (P.X i))
    (fun i j _ ↦ ((moduleLevel l E f M n).hom.naturality (P.d i j)).symm)

attribute [local irreducible] level
attribute [local implicit_reducible]
  HomologicalComplex.complexOfFunctorsToFunctorToComplex HomologicalComplex.asFunctor

private theorem finiteGenerator_naturality {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    {N N' : integralOperationsFiniteModules l E Y n} (g : N ⟶ N')
    (U : Y.ProEt) (x : N.val.obj (op U)) :
    (((integralOperationsLevelPullback l E f n).map g).val.app
        (op ((proEtaleBaseChange f).obj U)))
      (integralOperationsPullbackGenerator l E f n N U x) =
    integralOperationsPullbackGenerator l E f n N' U (g.val.app (op U) x) := by
  exact (congrArg (fun a ↦ a.val.app (op U) x)
    ((coefficientProEtaleModuleAdjunction.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (finiteCoefficientRing l E (n + 1))))).unit.naturality
        g)).symm

private theorem inverseEvaluation_inv_unit {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (N : coefficientSequenceModules l E Y) (U : Y.ProEt)
    (x : N.val.obj (op (n, U))) :
    (((inverseEvaluation l E f n).inv.app N).val.app
      (op ((proEtaleBaseChange f).obj U)))
      (coefficientEvaluationSection l E X
        ((integralComparisonSequencePullback l E f).obj N) n
        (op ((proEtaleBaseChange f).obj U))
        (integralComparisonSequenceGenerator l E f N n U x)) =
      integralOperationsPullbackGenerator l E f n
        ((coefficientSequenceEvaluation l E Y n).obj N) U
        (coefficientEvaluationSection l E Y N n (op U) x) := by
  rw [← inverseEvaluation_unit l E f n N U x]
  exact congrArg (fun a ↦ a.val.app (op ((proEtaleBaseChange f).obj U))
    (integralOperationsPullbackGenerator l E f n
      ((coefficientSequenceEvaluation l E Y n).obj N) U
      (coefficientEvaluationSection l E Y N n (op U) x)))
    ((inverseEvaluation l E f n).hom_inv_id_app N)

private theorem level_unit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (n : ℕ) (i : ℤ) (U : Y.ProEt)
    (x : (M.tensor.obj (P.X i)).val.obj (op (n, U))) :
    (((level l E f M P n).hom.f i).val.app
        (op ((proEtaleBaseChange f).obj U)))
      (integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E f).obj (M.tensor.obj (P.X i))) n
        (op ((proEtaleBaseChange f).obj U))
        (integralComparisonSequenceGenerator l E f (M.tensor.obj (P.X i)) n U x)) =
      integralOperationsPullbackGenerator l E f n
        ((scalarReductionExtension l E Y n).obj (P.X i)) U
        (((M.evaluation n).hom.app (P.X i)).val.app (op U)
          (coefficientEvaluationSection l E Y (M.tensor.obj (P.X i)) n (op U) x)) := by
  simp only [level, HomologicalComplex.Hom.isoOfComponents_hom_f]
  simp only [moduleLevel]
  change (((integralOperationsLevelPullback l E f n).map
      ((M.evaluation n).hom.app (P.X i))).val.app _)
    ((((inverseEvaluation l E f n).inv.app (M.tensor.obj (P.X i))).val.app _)
      ((((eqToIso (coefficientSequenceRestriction_evaluation l E X n)).app
        ((integralComparisonSequencePullback l E f).obj (M.tensor.obj (P.X i)))).hom.val.app _)
          _)) = _
  rw [restrictionEvaluation_section, inverseEvaluation_inv_unit]
  exact finiteGenerator_naturality l E f n ((M.evaluation n).hom.app (P.X i)) U _

private def towerIso {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    (pullTower l E f).obj ((M.quotient l E Y).obj P) ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P := by
  have h := ordinaryQuotientPullback_successor l E f M P (level l E f M P)
    (level_unit l E f M P)
  let a : (pullTower l E f).obj ((M.quotient l E Y).obj P) ⟶
      (integralOperationsPullbackTowerFunctor l E f).obj P :=
    NatTrans.ofOpSequence (fun n ↦ (level l E f M P n).hom) h
  letI : ∀ n, IsIso (a.app n) := fun n ↦ Iso.isIso_hom (level l E f M P n.unop)
  letI := NatIso.isIso_of_isIso_app a
  exact asIso a

private def comparison {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y) :
    M.quotient l E Y ⋙ pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f :=
  NatIso.ofComponents (towerIso l E f M) (by
    intro P Q a
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.hom_ext
    intro i
    simp only [NatTrans.comp_app, HomologicalComplex.comp_f, towerIso, asIso_hom,
      NatTrans.ofOpSequence_app, level, HomologicalComplex.Hom.isoOfComponents_hom_f]
    exact (moduleLevel l E f M n.unop).hom.naturality (a.f i))

private theorem comparison_hom_app_f {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) (i : ℤ) :
    (((comparison l E f M).hom.app P).app (op n)).f i =
      (level l E f M P n).hom.f i := rfl

attribute [local irreducible] comparison

private theorem cast_map {A A' B B' : Type v} (hA : A = A') (hB : B = B')
    (f : A → B) (g : A' → B') (h : HEq f g) (x : A') :
    f (cast hA.symm x) = cast hB.symm (g x) := by
  cases hA
  cases hB
  exact congrFun (eq_of_heq h) x

private theorem restriction_map_section {X : Scheme.{t}}
    {N N' : coefficientSequenceModules l E X} (g : N ⟶ N')
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    ((((coefficientSequenceRestriction l E X).map g).app (op n)).val.app U)
      (integralComparisonRestrictedSection l E X N n U x) =
    integralComparisonRestrictedSection l E X N' n U
      (g.val.app (op (n, U.unop)) x) := by
  have h : HEq (fun y ↦
      ((((coefficientSequenceRestriction l E X).map g).app (op n)).val.app U) y)
      (fun y : N.val.obj (op (n, U.unop)) ↦ g.val.app (op (n, U.unop)) y) := by
    unfold coefficientSequenceRestriction
    exact (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.2 g n U
  exact cast_map (integralComparisonRestrictedSectionType l E X N n U)
    (integralComparisonRestrictedSectionType l E X N' n U) _ _ h x

private theorem sequenceGenerator_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {N N' : coefficientSequenceModules l E Y} (g : N ⟶ N')
    (n : ℕ) (U : Y.ProEt) (x : N.val.obj (op (n, U))) :
    (((integralComparisonSequencePullback l E f).map g).val.app
        (op (n, (proEtaleBaseChange f).obj U)))
      (integralComparisonSequenceGenerator l E f N n U x) =
    integralComparisonSequenceGenerator l E f N' n U
      (g.val.app (op (n, U)) x) := by
  exact (congrArg (fun a ↦ a.val.app (op (n, U)) x)
    ((Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E f)).unit.naturality g)).symm

private theorem pullTower_map_app_f {X Y : Scheme.{t}} (f : X ⟶ Y)
    {C D : CochainComplex (coefficientSequenceModules l E Y) ℤ} (b : C ⟶ D)
    (n : ℕ) (i : ℤ) :
    (((pullTower l E f).map b).app (op n)).f i =
      (((coefficientSequenceRestriction l E X).map
        ((integralComparisonSequencePullback l E f).map (b.f i))).app (op n)) := rfl

end OrdinaryTowerProof

/-- Ordinary pullback of a strict quotient system is the defining pullback tower,
naturally on all complexes, with the tensor-unit generator normalization.
Source: Stacks 099N(5), 03D2, 0941, pullback of modules and quotient systems.
(blueprint: lem-trf-ordinary-quotient-pullback-tower-comparison).

Proof: at every quotient level, transpose the tensor-unit map through the actual
sequence inverse-image adjunction. The resulting evaluation comparison identifies
sequence inverse image with the finite constant-coefficient inverse image. Compose
with M.evaluation and then restrict coefficients to the completed ring. On unit
generators this sends the image of x to the image of its finite comparison.
These comparisons commute with quotient transitions because both adjuncts are the
same constant-section map followed by the actual quotient reduction. They commute
with differentials and every chain map by naturality of adjunction units. Their
inverses assemble too, giving the natural isomorphism θ on the entire strict tower.
For any strict presentation isomorphism a, pull back a inverse and compose with θ.
Naturality of the sequence inverse-image unit and the finite comparison equation
turn its generator formula into the displayed one. Restriction leaves the section
type unchanged through the recorded casts. No infinite product passes through
inverse image, and this statement uses no derived-limit comparison. -/
theorem ordinaryQuotientPullbackTowerComparison {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y) :
    let T := (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    ∃ θ : M.quotient l E Y ⋙ T ≅ integralOperationsPullbackTowerFunctor l E f,
    ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
      (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (a : (M.quotient l E Y).obj P ≅ C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
          (unrestrictedIntegralFiniteComplex l E Y n).obj P),
      (∀ n : ℕ,
        ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
          κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) →
      ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (C.X i).val.obj (op (n, U))),
        (((T.mapIso a.symm ≪≫ θ.app P).hom.app (op n)).f i).val.app
            (op ((proEtaleBaseChange f).obj U))
          (integralComparisonRestrictedSection l E X
            ((integralComparisonSequencePullback l E f).obj (C.X i)) n
            (op ((proEtaleBaseChange f).obj U))
            (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
          integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
            (((κ n).hom.f i).val.app (op U)
              (coefficientEvaluationSection l E Y (C.X i) n (op U) x)) := by
  dsimp only
  refine ⟨OrdinaryTowerProof.comparison l E f M, ?_⟩
  intro P C a κ hκ n i U x
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapIso_hom, OrdinaryTowerProof.pullTower_map_app_f,
    OrdinaryTowerProof.comparison_hom_app_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [OrdinaryTowerProof.restriction_map_section l E
    ((integralComparisonSequencePullback l E f).map (a.inv.f i)) n
    (op ((proEtaleBaseChange f).obj U))
    (integralComparisonSequenceGenerator l E f (C.X i) n U x)]
  erw [OrdinaryTowerProof.sequenceGenerator_naturality, OrdinaryTowerProof.level_unit]
  congr 1
  have hh :
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).map a.inv ≫
        ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P).hom =
      (κ n).hom := by
    rw [← hκ n]
    exact (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex
      (.up ℤ)).mapIso a).inv_hom_id_assoc (κ n).hom
  erw [← OrdinaryTowerProof.evaluation_map_section l E (a.inv.f i) n (op U) x]
  exact congrArg (fun b ↦ (b.f i).val.app (op U)
    (coefficientEvaluationSection l E Y (C.X i) n (op U) x)) hh

end WeilConjectures
