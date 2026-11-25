/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram

/-! # Ordinary direct-image evaluation for compact support

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941.
(blueprint: lem-trf-compact-support-direct-image-ordinary-evaluation).

This is the ordinary sectionwise component of the direct-image evaluation theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor

universe t u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

-- Prove the section formulas over abstract sheaves before specializing the ring maps.
-- This avoids reducing the nested sequence-site scalar restrictions in the concrete proof.
private theorem compactSupportPushforwardComp_sections
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

private theorem compactSupportPushforwardComp_inv_sections
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

private theorem compactSupportPushforwardCongr_sections
    {C : Type v} [Category C] {D : Type w} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] {R : Sheaf K RingCat.{u}}
    {S : Sheaf J RingCat.{u}}
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (h : φ = ψ) :
    ∀ M U (x : ((SheafOfModules.pushforward.{u} φ).obj M).val.obj U),
      HEq (((SheafOfModules.pushforwardCongr h).hom.app M).val.app U x) x := by
  intro M U x
  exact heq_of_eq (SheafOfModules.pushforwardCongr_hom_app_val_app h M U x)

private theorem compactSupportIsoTrans_sections
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
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary direct-image comparison is sectionwise the identity.

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941.
The direct image is computed on the sequence site by restriction along
`proEtaleBaseChange p`; evaluating at `n` computes the same section as the finite
coefficient direct image.  The coefficient map is the constant-section map, so the
comparison is identity on every section.  This smaller statement supplies exactly
the ordinary component used by the parent theorem.
(blueprint: lem-trf-compact-support-direct-image-ordinary-evaluation).
-/
theorem compactSupportDirectImageOrdinaryEvaluation
    {Z Y : Scheme.{t}} (p : Z ⟶ Y) :
    ∃ (ordinary : ∀ n : ℕ,
        integralComparisonSequenceDirectImage l E p ⋙ coefficientSequenceEvaluation l E Y n ≅
          coefficientSequenceEvaluation l E Z n ⋙ compactSupportLevelDirectImage l E p n),
      ∀ (n : ℕ) (N : coefficientSequenceModules l E Z)
              (V : Y.ProEtᵒᵖ)
              (x : ((integralComparisonSequenceDirectImage l E p ⋙
                coefficientSequenceEvaluation l E Y n).obj N).val.obj V),
              HEq (((ordinary n).hom.app N).val.app V x) x := by
  have level (n : ℕ) :
      ∃ e : integralComparisonSequenceDirectImage l E p ⋙ coefficientSequenceEvaluation l E Y n ≅
          coefficientSequenceEvaluation l E Z n ⋙ compactSupportLevelDirectImage l E p n,
        ∀ (N : coefficientSequenceModules l E Z) (V : Y.ProEtᵒᵖ)
          (x : ((integralComparisonSequenceDirectImage l E p ⋙
            coefficientSequenceEvaluation l E Y n).obj N).val.obj V),
          HEq (((e.hom.app N).val.app V) x) x := by
    let a := eqToHom (coefficientSequenceEvaluationRing_eq l E Y n).symm
    let b := eqToHom (coefficientSequenceEvaluationRing_eq l E Z n).symm
    let r' :
        (sheafCompose _ (forget₂ CommRingCat.{max u (t+1)} RingCat)).obj
          (coefficientSequenceCommRingSheaf l E Y) ⟶
        ((integralComparisonSequenceBaseChange p).sheafPushforwardContinuous RingCat
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceTopology (Scheme.ProEt.topology Z))).obj
            ((sheafCompose _ (forget₂ CommRingCat.{max u (t+1)} RingCat)).obj
              (coefficientSequenceCommRingSheaf l E Z)) :=
      ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E p).hom
        (forget₂ CommRingCat.{max u (t+1)} RingCat)⟩
    let A := CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1)))
    let s : integralCoefficientSheaf l E Y n ⟶
        ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous RingCat
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)).obj
            (integralCoefficientSheaf l E Z n) :=
      ⟨Functor.whiskerRight (Scheme.coefficientProEtaleDirectRingMap.{t, u} p A).hom
        (forget₂ CommRingCat.{max u (t+1)} RingCat)⟩
    have := Functor.isContinuous_comp (Prod.sectR n Y.ProEt)
      (integralComparisonSequenceBaseChange p) (Scheme.ProEt.topology Y)
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology Z))
    have := Functor.isContinuous_comp (Scheme.proEtaleBaseChange p) (Prod.sectR n Z.ProEt)
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)
      (coefficientSequenceTopology (Scheme.ProEt.topology Z))
    have h : a ≫ ((Prod.sectR n Y.ProEt).sheafPushforwardContinuous RingCat
        (Scheme.ProEt.topology Y)
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))).map r' =
        s ≫ ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous RingCat
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)).map b := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      have ha : a.hom.app U = 𝟙 _ := by
        dsimp only [a]
        rw [ObjectProperty.eqToHom_hom, eqToHom_app]
        rfl
      have hb : b.hom.app ((Scheme.proEtaleBaseChange p).op.obj U) = 𝟙 _ := by
        dsimp only [b]
        rw [ObjectProperty.eqToHom_hom, eqToHom_app]
        rfl
      change a.hom.app U ≫ r'.hom.app (op (n, U.unop)) =
        s.hom.app U ≫ b.hom.app ((Scheme.proEtaleBaseChange p).op.obj U)
      rw [ha, hb]
      rfl
    refine ⟨SheafOfModules.pushforwardComp a r' ≪≫
      SheafOfModules.pushforwardCongr h ≪≫ (SheafOfModules.pushforwardComp s b).symm, ?_⟩
    apply compactSupportIsoTrans_sections
    · exact compactSupportPushforwardComp_sections
        (F := Prod.sectR n Y.ProEt) (G := integralComparisonSequenceBaseChange p) a r'
    · apply compactSupportIsoTrans_sections
      · exact compactSupportPushforwardCongr_sections
          (F := Prod.sectR n Y.ProEt ⋙ integralComparisonSequenceBaseChange p)
          (S := integralCoefficientSheaf l E Y n)
          (R := (sheafCompose _ (forget₂ CommRingCat.{max u (t+1)} RingCat)).obj
            (coefficientSequenceCommRingSheaf l E Z)) h
      · exact compactSupportPushforwardComp_inv_sections
          (F := Scheme.proEtaleBaseChange p) (G := Prod.sectR n Z.ProEt) s b
  exact ⟨fun n ↦ (level n).choose, fun n ↦ (level n).choose_spec⟩

end WeilConjectures
