/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Direct image on restricted coefficient towers

Source: Stacks Project, Tags 03D7 and 0941.
(blueprint: lem-sf-integral-ordinary-tower-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted constantSheaf
  pullbackTensorSequenceRing completedIntegralCommRingProjectionUnrestricted
  sfCompletedCoefficientMap
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  Functor.sheafPushforwardContinuous Prod.sectR SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  coefficientSequenceEvaluation coefficientProEtaleModuleDirectImage
  proEtaleConstantModuleDirectImage proEtaleConstantDirectImageMap coefficientProEtaleDirectRingMap
  pullbackTensorSequenceBase pullbackTensorSequenceDirect SheafOfModules.restrictScalars

private theorem directEvaluation_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E X) (V : Y.ProEt)
    (x : ((coefficientSequenceEvaluation l E Y n).obj
      ((pullbackTensorSequenceDirect l E f).obj M)).val.obj (op V)) :
    HEq (((pullbackTensorSequenceDirectEvaluation l E f n).hom.app M).val.app (op V) x) x := by
  dsimp only [pullbackTensorSequenceDirectEvaluation, pullbackTensorUniqueChoice]
  exact (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec M V x

attribute [local irreducible] pullbackTensorSequenceDirectEvaluation

private theorem scalarComparison_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : scalarReductionTarget l E X n) (V : Y.ProEtᵒᵖ)
    (x : ((proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      scalarReductionRestriction l E Y n).obj M).val.obj V) :
    HEq (((sfDirectImageRestrictionComparison l E f n).hom.app M).val.app V x) x := by
  dsimp only [sfDirectImageRestrictionComparison]
  exact heq_of_eq
    ((sfDirectImageRestrictionComparison_existsUnique l E f n).exists.choose_spec M V x)

attribute [local irreducible] sfDirectImageRestrictionComparison

private def levelComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y) ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) ≅
      (coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n)) ⋙
          sfCompletedModuleDirectImage l E f :=
  Functor.isoWhiskerLeft (pullbackTensorSequenceDirect l E f)
      (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)) ≪≫
    Functor.isoWhiskerRight (pullbackTensorSequenceDirectEvaluation l E f n)
      (scalarReductionRestriction l E Y n) ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E X n)
      (sfDirectImageRestrictionComparison l E f n) ≪≫
    Functor.isoWhiskerRight (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).symm
      (sfCompletedModuleDirectImage l E f)

attribute [local irreducible] levelComparison

private theorem eqToHom_sections
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (h : M = N) (V : Cᵒᵖ) (x : M.val.obj V) :
    HEq ((eqToHom h).val.app V x) x := by
  subst N
  rfl

private theorem restrict_sections
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (φ : R ⟶ S)
    {A B : SheafOfModules.{u + 1} S} (g : A ⟶ B) (V : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars φ).obj A).val.obj V) :
    HEq (((SheafOfModules.restrictScalars φ).map g).val.app V x) (g.val.app V x) := by
  rfl

private theorem restrictIso_sections
    {A C : Type*} [Category A] [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (φ : R ⟶ S)
    {F G : A ⥤ SheafOfModules.{u + 1} S} (e : F ≅ G)
    (he : ∀ M V (x : (F.obj M).val.obj V), HEq ((e.hom.app M).val.app V x) x) :
    ∀ M V (x : ((F ⋙ SheafOfModules.restrictScalars φ).obj M).val.obj V),
      HEq (((Functor.isoWhiskerRight e (SheafOfModules.restrictScalars φ)).hom.app M).val.app
        V x) x := by
  intro M V x
  exact (restrict_sections φ (e.hom.app M) V x).trans (he M V x)

private theorem restrictedEvaluation_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E X) (V : Y.ProEtᵒᵖ)
    (x : (((pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceEvaluation l E Y n) ⋙
      scalarReductionRestriction l E Y n).obj M).val.obj V) :
    HEq (((Functor.isoWhiskerRight (pullbackTensorSequenceDirectEvaluation l E f n)
      (scalarReductionRestriction l E Y n)).hom.app M).val.app V x) x := by
  exact restrictIso_sections
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n))
    (pullbackTensorSequenceDirectEvaluation l E f n)
    (fun N U z ↦ directEvaluation_sections l E f n N U.unop z) M V x

private theorem finiteScalarComparison_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E X) (V : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E X n ⋙
      (proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        scalarReductionRestriction l E Y n)).obj M).val.obj V) :
    HEq (((Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E X n)
      (sfDirectImageRestrictionComparison l E f n)).hom.app M).val.app V x) x := by
  exact scalarComparison_sections l E f n ((coefficientSequenceEvaluation l E X n).obj M) V x

private theorem levelComparison_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E X) (V : Y.ProEtᵒᵖ)
    (x : (((pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y).obj M).obj
      (op n)).val.obj V) :
    HEq (((levelComparison l E f n).hom.app M).val.app V x) x := by
  unfold levelComparison
  let e₁ := Functor.isoWhiskerLeft (pullbackTensorSequenceDirect l E f)
    (eqToIso (coefficientSequenceRestriction_evaluation l E Y n))
  let e₂ := Functor.isoWhiskerRight (pullbackTensorSequenceDirectEvaluation l E f n)
    (scalarReductionRestriction l E Y n)
  let e₃ := Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E X n)
    (sfDirectImageRestrictionComparison l E f n)
  let e₄ := Functor.isoWhiskerRight
    (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).symm
    (sfCompletedModuleDirectImage l E f)
  have h₁ : ∀ V x, HEq ((e₁.hom.app M).val.app V x) x := by
    intro V x
    simp only [e₁, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      eqToIso.hom, eqToHom_app]
    exact eqToHom_sections _ _ _
  have h₂ : ∀ V x, HEq ((e₂.hom.app M).val.app V x) x :=
    restrictedEvaluation_sections l E f n M
  have h₃ : ∀ V x, HEq ((e₃.hom.app M).val.app V x) x :=
    finiteScalarComparison_sections l E f n M
  have h₄ : ∀ V x, HEq ((e₄.hom.app M).val.app V x) x := by
    intro V x
    simp only [e₄, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Iso.symm_hom, eqToIso.inv, eqToHom_app, eqToHom_map]
    exact eqToHom_sections _ _ _
  exact (h₄ V _).trans ((h₃ V _).trans ((h₂ V _).trans (h₁ V x)))

private theorem identity_square {A B C D : Type v} [Zero A] [Zero B]
    (f : A → B) (g : C → D) (e : A → C) (d : B → D)
    (hfg : HEq f g) (he : ∀ x, HEq (e x) x) (hd : ∀ x, HEq (d x) x) :
    ∀ x, d (f x) = g (e x) := by
  have hA : A = C := (type_eq_of_heq (he 0)).symm
  have hB : B = D := (type_eq_of_heq (hd 0)).symm
  subst C D
  cases hfg
  intro x
  rw [eq_of_heq (he x), eq_of_heq (hd (f x))]

private theorem pushforward_map_heq
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{u + 1}} {R : Sheaf K RingCat.{u + 1}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    (M : SheafOfModules.{u + 1} R) {U V : Cᵒᵖ} (g : U ⟶ V)
    (q : F.obj V.unop ⟶ F.obj U.unop) (h : F.map g.unop = q) :
    HEq (fun x : ((SheafOfModules.pushforward φ).obj M).val.obj U ↦
      (((SheafOfModules.pushforward φ).obj M).val.map g) x)
      (fun x : M.val.obj (op (F.obj U.unop)) ↦ M.val.map q.op x) := by
  subst q
  rfl

private theorem levelComparison_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) {m n : ℕᵒᵖ} (g : m ⟶ n) :
    (((pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y).obj M).map
      g) ≫ (levelComparison l E f n.unop).hom.app M =
    (levelComparison l E f m.unop).hom.app M ≫
      (sfCompletedModuleDirectImage l E f).map
        (((coefficientSequenceRestriction l E X).obj M).map g) := by
  ext V x
  change ((levelComparison l E f n.unop).hom.app M).val.app V
      (((((coefficientSequenceRestriction l E Y).obj
        ((pullbackTensorSequenceDirect l E f).obj M)).map g).val.app V) x) =
    (((coefficientSequenceRestriction l E X).obj M).map g).val.app
      ((proEtaleBaseChange f).op.obj V)
        (((levelComparison l E f m.unop).hom.app M).val.app V x)
  have hleft := (coefficientSequenceRestriction_exists l E Y).exists.choose_spec.2.1
    ((pullbackTensorSequenceDirect l E f).obj M) m.unop n.unop (leOfHom g.unop) V
  have hright := (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.1 M
    m.unop n.unop (leOfHom g.unop) ((proEtaleBaseChange f).op.obj V)
  have hid : (pullbackTensorSequenceBase f).map
      (Prod.mkHom (homOfLE (leOfHom g.unop)) (𝟙 V.unop)) =
      Prod.mkHom (homOfLE (leOfHom g.unop))
        (𝟙 ((proEtaleBaseChange f).obj V.unop)) := by
    exact congrArg (fun k ↦ Prod.mkHom (homOfLE (leOfHom g.unop)) k)
      ((proEtaleBaseChange f).map_id V.unop)
  have hraw := pushforward_map_heq
    (F := pullbackTensorSequenceBase f)
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E Y))
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E X))
    ⟨Functor.whiskerRight (pullbackTensorSequenceRing l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ M
    (Prod.mkHom (homOfLE (leOfHom g.unop)) (𝟙 V.unop)).op
    (Prod.mkHom (homOfLE (leOfHom g.unop)) (𝟙 ((proEtaleBaseChange f).obj V.unop))) hid
  exact identity_square _ _ _ _ (hleft.trans (hraw.trans hright.symm))
    (fun z ↦ levelComparison_sections l E f m.unop M V z)
    (fun z ↦ levelComparison_sections l E f n.unop M V z) x

private def towerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y ≅
      coefficientSequenceRestriction l E X ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sfCompletedModuleDirectImage l E f) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun n ↦ (levelComparison l E f n.unop).app M)
    (fun g ↦ levelComparison_naturality l E f M g)) (by
      intro M N g
      apply NatTrans.ext
      funext n
      exact (levelComparison l E f n.unop).hom.naturality g)

private theorem towerComparison_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) :
    ((towerComparison l E f).hom.app M).app (op n) =
      (levelComparison l E f n).hom.app M := rfl

attribute [local irreducible] towerComparison

/-- The normalized finite comparisons form a unique isomorphism of coefficient towers.
Source: Stacks Project, Tags 03D1 and 0941; primitive realization Step 3.
(blueprint: lem-sf-integral-ordinary-tower-comparison).

Proof: compose restriction/evaluation, direct-image/evaluation, scalar restriction,
and the inverse restriction/evaluation comparison at each coefficient level.
Each factor is the identity on underlying sections. The specified horizontal maps
of restriction therefore make these isomorphisms natural in the tower index;
naturality in the input module is inherited from the four factors. This constructs
the isomorphism of towers. Equality on all component sections proves uniqueness. -/
theorem integralOrdinaryTowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y ≅
      coefficientSequenceRestriction l E X ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sfCompletedModuleDirectImage l E f),
      ∀ (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEtᵒᵖ)
        (x : (((pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y).obj
          M).obj (op n)).val.obj V),
        HEq (((e.hom.app M).app (op n)).val.app V x) x := by
  refine ⟨towerComparison l E f, ?_, ?_⟩
  · intro M n V x
    rw [towerComparison_component]
    exact levelComparison_sections l E f n M V x
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext V x
    have h := levelComparison_sections l E f n.unop M V x
    rw [← towerComparison_component l E f M n.unop] at h
    exact eq_of_heq ((he M n.unop V x).trans h.symm)

end WeilConjectures.IntegralSystemRealization
