/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # Evaluation of canonical sequence direct image

Source: Stacks Project, Tags 03D1 and 0941
(blueprint: lem-pur-integral-comparison-sequence-direct-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures

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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

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
Source: Stacks 03D1 and 0941 (blueprint: lem-pur-integral-comparison-sequence-direct-evaluation).
Proof: both functors evaluate M at (n, f-basechange U) with scalar action through
the same constant-section coefficient map. The identity section maps give the
natural isomorphism. Sectionwise extensionality proves uniqueness. -/
private theorem canonical_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃ e : integralComparisonSequenceDirectImage l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        coefficientProEtaleModuleDirectImage.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))),
      ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
        (x : ((coefficientSequenceEvaluation l E Y n).obj
          ((integralComparisonSequenceDirectImage l E f).obj M)).val.obj (op U)),
        HEq ((e.hom.app M).val.app (op U) x) x := by
  unfold integralComparisonSequenceDirectImage
  let a := eqToHom (coefficientSequenceEvaluationRing_eq l E Y n).symm
  let b := eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm
  let φ : (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E Y) ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E X)) :=
    ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : integralCoefficientSheaf l E Y n ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj (integralCoefficientSheaf l E X n) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have h : a ≫ ((Prod.sectR n Y.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology Y))).map φ =
      ψ ≫ ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
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
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
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
          (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E X)) h
      · exact comp_inv_identity_sections (F := proEtaleBaseChange f)
          (G := Prod.sectR n X.ProEt) ψ b
  exact ⟨e, (fun M U x ↦ he M (op U) x)⟩

/-- Direct image on sequences commutes with evaluation by the identity on sections.
Source: Stacks 03D1 and 0941 (blueprint: lem-pur-integral-comparison-sequence-direct-evaluation).
Proof: both functors evaluate M at (n, f-basechange U) with scalar action through
the same constant-section coefficient map. The identity section maps give the
natural isomorphism. Sectionwise extensionality proves uniqueness. -/
theorem integralComparisonSequenceDirectEvaluation_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! e : integralComparisonSequenceDirectImage l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        coefficientProEtaleModuleDirectImage.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))),
      ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
        (x : ((coefficientSequenceEvaluation l E Y n).obj
          ((integralComparisonSequenceDirectImage l E f).obj M)).val.obj (op U)),
        HEq ((e.hom.app M).val.app (op U) x) x := by
  obtain ⟨e, he⟩ := canonical_exists l E f n
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  ext U x
  exact eq_of_heq ((he' M U.unop x).trans (he M U.unop x).symm)

end WeilConjectures
