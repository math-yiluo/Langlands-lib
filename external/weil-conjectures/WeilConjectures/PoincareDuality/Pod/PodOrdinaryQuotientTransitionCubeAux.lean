/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodQuotientTransition.PodQuotientTransitionGenerators
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarOrdinaryPresentationCoordinates
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Ordinary quotient cube: generators and the scalar comparison

Helpers for `podOrdinaryQuotientTransitionCube`: uniqueness of maps out of ordinary quotient
tensors on unit generators, commutation of restriction of scalars with ordinary limits, and the
generator-normalized scalar comparison of ordinary quotient tensors.

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-ordinary-quotient-transition-cube).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

namespace OrdinaryQuotientCube

/-- Commute a limit-preserving functor past the limits of a natural family of diagrams. -/
def limitCommIso {C D A A' J : Type*} [Category C] [Category D] [Category A] [Category A']
    [Category J] [HasLimitsOfShape J A] [HasLimitsOfShape J A']
    (P : C ⥤ D) (Q : A' ⥤ A) [PreservesLimitsOfShape J Q]
    (S : D ⥤ (J ⥤ A)) (S' : C ⥤ (J ⥤ A'))
    (δ : P ⋙ S ≅ S' ⋙ (whiskeringRight J A' A).obj Q) :
    P ⋙ (S ⋙ lim) ≅ (S' ⋙ lim) ⋙ Q :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight δ lim ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft S' (preservesLimitNatIso Q).symm ≪≫ (Functor.associator _ _ _).symm

/-- The projections of `limitCommIso`. -/
@[reassoc]
theorem limitCommIso_inv_π {C D A A' J : Type*} [Category C] [Category D] [Category A]
    [Category A'] [Category J] [HasLimitsOfShape J A] [HasLimitsOfShape J A']
    (P : C ⥤ D) (Q : A' ⥤ A) [PreservesLimitsOfShape J Q]
    (S : D ⥤ (J ⥤ A)) (S' : C ⥤ (J ⥤ A'))
    (δ : P ⋙ S ≅ S' ⋙ (whiskeringRight J A' A).obj Q) (Z : C) (j : J) :
    (limitCommIso P Q S S' δ).inv.app Z ≫ limit.π (S.obj (P.obj Z)) j =
      Q.map (limit.π (S'.obj Z) j) ≫ (δ.inv.app Z).app j := by
  simp [limitCommIso, preservesLimitNatIso]


/-- The level-`n` component of the ordinary quotient adjunction unit is the unit generator. -/
theorem unit_restrictedSection (W : Scheme.{u}) (M : CompletionUnit.OrdinaryModel l E W)
    (N : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj U) :
    ((M.adjunction.unit.app N ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj N)) (op n)).val.app U)
        x =
      integralComparisonRestrictedSection l E W (M.tensor.obj N) n U
        (PodQuotientTransition.unitSection l E W M N n U x) := by
  let T := (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).app (M.tensor.obj N) ≪≫
    (scalarReductionRestriction l E W n).mapIso ((M.evaluation n).app N)
  have hinj : Function.Injective (fun z ↦ T.hom.val.app U z) := by
    intro y z h
    have hi (w) : T.inv.val.app U (T.hom.val.app U w) = w :=
      congrArg (fun k ↦ k.val.app U w) T.hom_inv_id
    exact (hi y).symm.trans ((congrArg (fun w ↦ T.inv.val.app U w) h).trans (hi z))
  apply hinj
  have hunit := M.unit_tensor N n U x
  change T.hom.val.app U _ = _ at hunit
  refine hunit.trans ?_
  dsimp only [T, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    PodQuotientTransition.unitSection]
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    restricted_section_cancel l E W (M.tensor.obj N) n U]
  exact (congrArg (fun f ↦ f.val.app U
    (unrestrictedIntegralTensorSection l E W n N U 1 x))
      ((M.evaluation n).app N).inv_hom_id).symm

/-- Maps out of a left adjoint are determined by their adjoint transposes. -/
theorem adjoint_hom_ext
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (ad : F ⊣ G) {N : A} {Z : B} {f g : F.obj N ⟶ Z}
    (h : ad.unit.app N ≫ G.map f = ad.unit.app N ≫ G.map g) : f = g :=
  (ad.homEquiv N Z).injective h

section
attribute [local irreducible] SheafOfModules.monoidalCategory constantSheaf
  completedIntegralCommRingSheafUnrestricted coefficientSequenceCommRingSheaf
  scalarReductionExtension integralComparisonSequenceTensorSection
attribute [local irreducible] WeilConjectures.integralComparisonSequenceScalarModel

/-- Maps out of an ordinary quotient tensor are determined by the unit generators. -/
theorem quotient_unit_ext (W : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E W) (N : scalarReductionSource l E W)
    (Z : coefficientSequenceModules l E W) (f g : M.tensor.obj N ⟶ Z)
    (h : ∀ (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj U),
      f.val.app (op (n, U.unop)) (PodQuotientTransition.unitSection l E W M N n U x) =
        g.val.app (op (n, U.unop)) (PodQuotientTransition.unitSection l E W M N n U x)) :
    f = g := by
  have he (n : ℕ) : (coefficientSequenceEvaluation l E W n).map f =
      (coefficientSequenceEvaluation l E W n).map g := by
    apply (cancel_epi ((M.evaluation n).inv.app N)).1
    apply adjoint_hom_ext (scalarReductionExtension_adjunction l E W n).choose
    ext U x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    erw [scalarUnit_tensor]
    simpa only [PodQuotientTransition.unitSection, sequenceSection_eq] using! h n U x
  ext U x
  exact congrArg (fun k ↦ k.val.app (op U.unop.2) x) (he U.unop.1)

/-- Maps out of the scalar extension of an ordinary quotient tensor are determined by
the scalar-one tensors of unit generators. -/
theorem scalar_quotient_unit_ext (W : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E W) (N : scalarReductionSource l E W)
    (Z : coefficientSequenceModules l L W)
    (f g : (integralComparisonSequenceScalarModel l E L ι W).E.obj (M.tensor.obj N) ⟶ Z)
    (h : ∀ (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj U),
      f.val.app (op (n, U.unop))
          (integralComparisonSequenceTensorSection l E L ι W (M.tensor.obj N)
            (op (n, U.unop)) 1 (PodQuotientTransition.unitSection l E W M N n U x)) =
        g.val.app (op (n, U.unop))
          (integralComparisonSequenceTensorSection l E L ι W (M.tensor.obj N)
            (op (n, U.unop)) 1 (PodQuotientTransition.unitSection l E W M N n U x))) :
    f = g := by
  apply adjoint_hom_ext (sequenceScalarAdjunction l E L ι W).choose
  apply quotient_unit_ext l E W M N
  intro n U x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  dsimp only [SheafOfModules.restrictScalars, PresheafOfModules.restrictScalars,
    ModuleCat.restrictScalars]
  erw [sequenceScalarAdjunction_unit]
  exact h n U x

end


/-- Restriction of completed coefficients along the scalar map. -/
abbrev completedRestrict (W : Scheme.{u}) :
    scalarReductionSource l L W ⥤ scalarReductionSource l E W :=
  SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (integralCompletedScalarMap l E L ι W))

/-- Restriction of sequence coefficients along the scalar map. -/
abbrev sequenceRestrict (W : Scheme.{u}) :
    coefficientSequenceModules l L W ⥤ coefficientSequenceModules l E W :=
  SheafOfModules.restrictScalars ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralComparisonSequenceScalarMap l E L ι W))



/-- An isomorphism of sheaves of modules given by compatible sectionwise linear equivalences. -/
def sectionIso {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{a}}
    (M N : SheafOfModules.{b} R)
    (e : ∀ U : Cᵒᵖ, M.val.obj U ≃ₗ[R.obj.obj U] N.val.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U),
      e V (M.val.map f x) = N.val.map f (e U x)) : M ≅ N :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ (e U).toModuleIso) (fun _ _ f ↦ by
      ext x
      exact he f x))

/-- The isomorphism `sectionIso` acts by the given linear equivalences. -/
theorem sectionIso_hom_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{a}} (M N : SheafOfModules.{b} R)
    (e : ∀ U : Cᵒᵖ, M.val.obj U ≃ₗ[R.obj.obj U] N.val.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U),
      e V (M.val.map f x) = N.val.map f (e U x)) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((sectionIso M N e he).hom.val.app U) x = e U x := rfl

/-- The inverse of `sectionIso` acts by the inverse linear equivalences. -/
theorem sectionIso_inv_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{a}} (M N : SheafOfModules.{b} R)
    (e : ∀ U : Cᵒᵖ, M.val.obj U ≃ₗ[R.obj.obj U] N.val.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U),
      e V (M.val.map f x) = N.val.map f (e U x)) (U : Cᵒᵖ) (x : N.val.obj U) :
    ((sectionIso M N e he).inv.val.app U) x = (e U).symm x := rfl



section Generic
variable {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsContinuous J K]

/-- Restriction of scalars commutes with pushforward when the composite ring maps agree;
the comparison is the identity on sections. -/
def restrictPushforwardIso {S₁ S₂ T₁ T₂ : Sheaf J RingCat.{a}} {R₁ R₂ : Sheaf K RingCat.{a}}
    (α : R₁ ⟶ R₂) (φ₁ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{a} J K).obj R₁)
    (β₁ : T₁ ⟶ S₁) (φ₂ : S₂ ⟶ (F.sheafPushforwardContinuous RingCat.{a} J K).obj R₂)
    (β₂ : T₂ ⟶ S₂) (γ : T₁ ⟶ T₂)
    (h : β₁ ≫ φ₁ ≫ (F.sheafPushforwardContinuous RingCat.{a} J K).map α = γ ≫ β₂ ≫ φ₂) :
    SheafOfModules.restrictScalars.{b} α ⋙ SheafOfModules.pushforward φ₁ ⋙
        SheafOfModules.restrictScalars β₁ ≅
      SheafOfModules.pushforward φ₂ ⋙ SheafOfModules.restrictScalars β₂ ⋙
        SheafOfModules.restrictScalars γ :=
  NatIso.ofComponents (fun Z ↦ sectionIso _ _ (fun U ↦
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        have hr := congrArg (fun k ↦ k.hom.app U r) h
        exact congrArg
          (fun s : R₂.obj.obj (F.op.obj U) ↦ s • (id (α := Z.val.obj (F.op.obj U)) x)) hr
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (fun _ _ ↦ rfl)) (fun _ ↦ rfl)

/-- The comparison `restrictPushforwardIso` is the identity on sections. -/
theorem restrictPushforwardIso_hom_heq {S₁ S₂ T₁ T₂ : Sheaf J RingCat.{a}}
    {R₁ R₂ : Sheaf K RingCat.{a}}
    (α : R₁ ⟶ R₂) (φ₁ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{a} J K).obj R₁)
    (β₁ : T₁ ⟶ S₁) (φ₂ : S₂ ⟶ (F.sheafPushforwardContinuous RingCat.{a} J K).obj R₂)
    (β₂ : T₂ ⟶ S₂) (γ : T₁ ⟶ T₂)
    (h : β₁ ≫ φ₁ ≫ (F.sheafPushforwardContinuous RingCat.{a} J K).map α = γ ≫ β₂ ≫ φ₂)
    (Z : SheafOfModules.{b} R₂) (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars.{b} α ⋙ SheafOfModules.pushforward φ₁ ⋙
      SheafOfModules.restrictScalars β₁).obj Z).val.obj U) :
    HEq (((restrictPushforwardIso F α φ₁ β₁ φ₂ β₂ γ h).hom.app Z).val.app U x) x := HEq.rfl

end Generic


/-- The evaluated sequence scalar map is the finite quotient scalar map. -/
theorem sequenceScalar_app_apply (W : Scheme.{u}) (n : ℕ) (U : W.ProEtᵒᵖ) (y) :
    RingCat.Hom.hom ((((Prod.sectR n W.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology W) (coefficientSequenceTopology (ProEt.topology W))).map
        ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralComparisonSequenceScalarMap l E L ι W))).hom.app U) y =
      RingCat.Hom.hom ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((integralScalarQuotientSheafMap l E L ι W n).hom.app U)) y := rfl


/-- The evaluation-ring identification is the identity on sections. -/
theorem evaluationRing_eqToHom_app (W : Scheme.{u}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app U = 𝟙 _ := by
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

/-- The inverse evaluation-ring identification is the identity on sections. -/
theorem evaluationRing_eqToHom_symm_app (W : Scheme.{u}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    (eqToHom (coefficientSequenceEvaluationRing_eq l E W n)).hom.app U = 𝟙 _ := by
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- On the evaluated sequence rings, the scalar map is the finite quotient scalar map. -/
theorem evaluationScalar_eq (W : Scheme.{u}) (n : ℕ) :
    eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm ≫
      ((Prod.sectR n W.ProEt).sheafPushforwardContinuous RingCat.{u + 1} (ProEt.topology W)
        (coefficientSequenceTopology (ProEt.topology W))).map
        ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralComparisonSequenceScalarMap l E L ι W)) =
    @CategoryStruct.comp _ _ (integralCoefficientSheaf l E W n) (integralCoefficientSheaf l L W n) _
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralScalarQuotientSheafMap l E L ι W n))
      (eqToHom (coefficientSequenceEvaluationRing_eq l L W n).symm) := by
  ext1
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    evaluationRing_eqToHom_app]
  erw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, evaluationRing_eqToHom_app,
    Category.id_comp]

/-- Restricting a sequence module along the scalar map commutes with evaluation and
restriction to completed coefficients. -/
def scalarLevelIso (W : Scheme.{u}) (n : ℕ) :
    sequenceRestrict l E L ι W ⋙ coefficientSequenceEvaluation l E W n ⋙
        scalarReductionRestriction l E W n ≅
      coefficientSequenceEvaluation l L W n ⋙ scalarReductionRestriction l L W n ⋙
        completedRestrict l E L ι W :=
  restrictPushforwardIso (Prod.sectR n W.ProEt) _ _ _ _ _ _ (by
    have hspec := (integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec n
    unfold integralScalarRho at hspec
    have hq := congrArg (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map hspec
    simp only [Functor.map_comp] at hq
    rw [evaluationScalar_eq]
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ eqToHom
      (coefficientSequenceEvaluationRing_eq l L W n).symm) hq.symm)).trans (Category.assoc _ _ _))

/-- Heterogeneously equal functions take heterogeneously equal values. -/
theorem heq_fun_apply {α α' β β' : Type b} (hβ : β = β') {f : α → β} {g : α' → β'}
    (hfg : HEq f g) {x : α} {x' : α'} (hx : HEq x x') : HEq (f x) (g x') := by
  have hα := type_eq_of_heq hx
  subst hα hβ
  rw [eq_of_heq hfg, eq_of_heq hx]

/-- An `eqToHom` of sheaves of modules is the identity on sections. -/
theorem sheafOfModules_eqToHom_heq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{a}} {M N : SheafOfModules.{b} R} (h : M = N) (U : Cᵒᵖ)
    (x : M.val.obj U) : HEq ((eqToHom h).val.app U x) x := by
  subst h
  rfl

/-- The level-`n` comparison between restricting a sequence module along the scalar map and
restricting its completed coefficients. -/
def scalarRestrictionLevel (W : Scheme.{u}) (n : ℕ) :
    sequenceRestrict l E L ι W ⋙ coefficientSequenceRestriction l E W ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) ≅
      coefficientSequenceRestriction l L W ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l L W)).obj (op n) ⋙
          completedRestrict l E L ι W :=
  isoWhiskerLeft (sequenceRestrict l E L ι W)
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) ≪≫
    scalarLevelIso l E L ι W n ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (eqToIso (coefficientSequenceRestriction_evaluation l L W n).symm)
      (completedRestrict l E L ι W) ≪≫ Functor.associator _ _ _

/-- The level comparison `scalarRestrictionLevel` is the identity on sections. -/
theorem scalarRestrictionLevel_hom_heq (W : Scheme.{u}) (n : ℕ)
    (Z : coefficientSequenceModules l L W) (V : W.ProEtᵒᵖ)
    (x : (((coefficientSequenceRestriction l E W).obj ((sequenceRestrict l E L ι W).obj Z)).obj
      (op n)).val.obj V) :
    HEq (((scalarRestrictionLevel l E L ι W n).hom.app Z).val.app V x) x := by
  simp only [scalarRestrictionLevel, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, eqToIso.hom, eqToHom_app,
    eqToHom_map, Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    Category.id_comp, Category.comp_id]
  exact (sheafOfModules_eqToHom_heq _ V _).trans
    ((restrictPushforwardIso_hom_heq _ _ _ _ _ _ _ _ _ _ _).trans
      (sheafOfModules_eqToHom_heq _ V x))

/-- The completed-restriction transition maps are the sequence transition maps. -/
theorem restriction_transition_heq (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (W : Scheme.{u}) (M : coefficientSequenceModules l K W)
    {m n : ℕ} (h : n ≤ m) (V : W.ProEtᵒᵖ) :
    HEq (fun x ↦ (((coefficientSequenceRestriction l K W).obj M).map (homOfLE h).op).val.app V x)
      (fun x : M.val.obj (op (m, V.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) := by
  unfold coefficientSequenceRestriction
  exact (coefficientSequenceRestriction_exists l K W).exists.choose_spec.2.1 M m n h V






/-- Module restriction maps agree with the underlying abelian restriction maps. -/
theorem module_map_presheaf_heq {B : Type*} [Category B]
    {R : Bᵒᵖ ⥤ RingCat.{a}} (M : PresheafOfModules.{b} R)
    {V U : Bᵒᵖ} (f : V ⟶ U) :
    HEq (fun x : M.obj V ↦ M.map f x)
      (fun x : M.presheaf.obj V ↦ M.presheaf.map f x) := by
  rfl

/-- On sections, a transition map of the completed restriction is the sequence transition. -/
theorem restriction_transition_apply_heq (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (W : Scheme.{u}) (M : coefficientSequenceModules l K W)
    {m n : ℕ} (h : n ≤ m) (V : W.ProEtᵒᵖ)
    (x : (((coefficientSequenceRestriction l K W).obj M).obj (op m)).val.obj V)
    (y : M.val.presheaf.obj (op (m, V.unop))) (hxy : HEq x y) :
    HEq ((((coefficientSequenceRestriction l K W).obj M).map (homOfLE h).op).val.app V x)
      (M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op y) :=
  heq_fun_apply (integralComparisonRestrictedSectionType l K W M n V)
    ((restriction_transition_heq l K W M h V).trans
      (module_map_presheaf_heq M.val (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op)) hxy

/-- The level comparisons `scalarRestrictionLevel` commute with quotient transitions. -/
theorem scalarRestrictionLevel_naturality (W : Scheme.{u})
    (Z : coefficientSequenceModules l L W) {m n : ℕ} (h : n ≤ m) :
    ((coefficientSequenceRestriction l E W).obj ((sequenceRestrict l E L ι W).obj Z)).map
        (homOfLE h).op ≫ (scalarRestrictionLevel l E L ι W n).hom.app Z =
      (scalarRestrictionLevel l E L ι W m).hom.app Z ≫
        (completedRestrict l E L ι W).map
          (((coefficientSequenceRestriction l L W).obj Z).map (homOfLE h).op) := by
  ext V x
  apply eq_of_heq
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  have hx : HEq x (cast (integralComparisonRestrictedSectionType l E W
      ((sequenceRestrict l E L ι W).obj Z) m V) x) := (cast_heq _ _).symm
  refine (scalarRestrictionLevel_hom_heq l E L ι W n Z V _).trans ?_
  refine (restriction_transition_apply_heq l E W _ h V x _ hx).trans ?_
  exact (restriction_transition_apply_heq l L W Z h V _ _
    ((scalarRestrictionLevel_hom_heq l E L ι W m Z V x).trans hx)).symm

/-- The inverse level comparison is the identity on sections. -/
theorem scalarRestrictionLevel_inv_heq (W : Scheme.{u}) (n : ℕ)
    (Z : coefficientSequenceModules l L W) (V : W.ProEtᵒᵖ)
    (x : ((completedRestrict l E L ι W).obj
      (((coefficientSequenceRestriction l L W).obj Z).obj (op n))).val.obj V) :
    HEq (((scalarRestrictionLevel l E L ι W n).inv.app Z).val.app V x) x := by
  have h := scalarRestrictionLevel_hom_heq l E L ι W n Z V
    (((scalarRestrictionLevel l E L ι W n).inv.app Z).val.app V x)
  have hx : ((scalarRestrictionLevel l E L ι W n).hom.app Z).val.app V
      (((scalarRestrictionLevel l E L ι W n).inv.app Z).val.app V x) = x :=
    congrArg (fun k ↦ k.val.app V x) ((scalarRestrictionLevel l E L ι W n).inv_hom_id_app Z)
  rw [hx] at h
  exact h.symm

/-- Restriction along the scalar map commutes with the completed restriction towers. -/
def scalarRestrictionTower (W : Scheme.{u}) :
    sequenceRestrict l E L ι W ⋙ coefficientSequenceRestriction l E W ≅
      coefficientSequenceRestriction l L W ⋙
        (whiskeringRight ℕᵒᵖ _ _).obj (completedRestrict l E L ι W) :=
  NatIso.ofComponents (fun Z ↦ NatIso.ofComponents
      (fun n ↦ (scalarRestrictionLevel l E L ι W n.unop).app Z) (by
        intro m n f
        have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        rw [hf]
        exact scalarRestrictionLevel_naturality l E L ι W Z (leOfHom f.unop)))
    (fun f ↦ by
      ext n : 2
      exact (scalarRestrictionLevel l E L ι W n.unop).hom.naturality f)

/-- Restriction of completed coefficients preserves sequential limits. -/
instance completedRestrict_preservesLimits (W : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (completedRestrict l E L ι W) :=
  (ScalarExtensionTower.completedScalarAdj_exists l E L ι W).choose
    |>.rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- Restriction of scalars commutes with the ordinary limit of quotient systems. -/
def scalarLimitIso (W : Scheme.{u}) :
    sequenceRestrict l E L ι W ⋙ CompletionUnit.ordinaryLimit l E W ≅
      CompletionUnit.ordinaryLimit l L W ⋙ completedRestrict l E L ι W :=
  limitCommIso _ _ _ _ (scalarRestrictionTower l E L ι W)

/-- On sections, the completed restriction of a morphism is the morphism itself. -/
theorem restriction_map_section (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (W : Scheme.{u})
    {M N : coefficientSequenceModules l K W} (f : M ⟶ N) (n : ℕ)
    (U : W.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l K W).map f).app (op n)).val.app U
        (integralComparisonRestrictedSection l K W M n U x) =
      integralComparisonRestrictedSection l K W N n U (f.val.app (op (n, U.unop)) x) := by
  have h : HEq (fun y ↦ (((coefficientSequenceRestriction l K W).map f).app (op n)).val.app U y)
      (fun y : M.val.obj (op (n, U.unop)) ↦ f.val.app (op (n, U.unop)) y) := by
    unfold coefficientSequenceRestriction
    exact (coefficientSequenceRestriction_exists l K W).exists.choose_spec.2.2 f n U
  exact eq_of_heq ((heq_fun_apply (integralComparisonRestrictedSectionType l K W N n U) h
    (cast_heq _ _)).trans (cast_heq _ _).symm)

/-- The identification of restricted sections is injective. -/
theorem restrictedSection_injective (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (W : Scheme.{u}) (M : coefficientSequenceModules l K W)
    (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Injective (integralComparisonRestrictedSection l K W M n U) := by
  intro x y h
  have := congrArg (cast (integralComparisonRestrictedSectionType l K W M n U)) h
  simpa [integralComparisonRestrictedSection] using this

/-- Restriction of scalars does not change a morphism on sections. -/
theorem restrictScalars_map_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{a}} (α : R ⟶ R') {M N : SheafOfModules.{b} R'} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((SheafOfModules.restrictScalars α).map f).val.app U x = f.val.app U x := rfl

/-- The level-`n` ordinary unit applied to a section is its unit generator. -/
theorem unit_restrictedSection_apply (W : Scheme.{u}) (M : CompletionUnit.OrdinaryModel l E W)
    (N : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj U) :
    (limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj N)) (op n)).val.app U
        ((M.adjunction.unit.app N).val.app U x) =
      integralComparisonRestrictedSection l E W (M.tensor.obj N) n U
        (PodQuotientTransition.unitSection l E W M N n U x) :=
  unit_restrictedSection l E W M N n U x


set_option backward.isDefEq.respectTransparency true in
/-- The ordinary scalar comparison of quotient tensors, normalized on unit generators. It is
conjugate to the commutation of restriction of scalars with ordinary limits. -/
theorem scalarComparison_exists (W : Scheme.{u})
    (ME : CompletionUnit.OrdinaryModel l E W) (ML : CompletionUnit.OrdinaryModel l L W) :
    ∃ α : ME.tensor ⋙ (integralComparisonSequenceScalarModel l E L ι W).E ≅
        integralOrdinaryScalar l E L ι W ⋙ ML.tensor,
      PodQuotientTransition.ScalarNormalized l E L ι W ME ML α := by
  let adjSeq := (sequenceScalarAdjunction l E L ι W).choose
  let adjSc := (ScalarExtensionTower.completedScalarAdj_exists l E L ι W).choose
  obtain ⟨a, ha, -⟩ := normalizedAdjointComparison _ _ _ _ (ME.adjunction.comp adjSeq)
    (adjSc.comp ML.adjunction) (scalarLimitIso l E L ι W)
  refine ⟨a, ?_⟩
  intro N n U x
  have h := congrArg (· ≫ limit.π ((coefficientSequenceRestriction l E W).obj
    ((sequenceRestrict l E L ι W).obj (ML.tensor.obj ((integralOrdinaryScalar l E L ι W).obj N))))
      (op n)) (ha N)
  simp only [Adjunction.comp_unit_app, Category.assoc, Functor.comp_map, Functor.comp_obj, lim_map,
    limMap_π, limMap_π_assoc, scalarLimitIso, limitCommIso_inv_π] at h
  have hx := congrArg (fun k ↦ k.val.app U x) h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    scalarRestrictionTower, NatIso.ofComponents_inv_app] at hx
  rw [(ScalarExtensionTower.completedScalarAdj_exists l E L ι W).choose_spec N U x,
    restrictScalars_map_apply, restrictScalars_map_apply, unit_restrictedSection_apply,
    unit_restrictedSection_apply, restriction_map_section, sequenceScalarAdjunction_unit] at hx
  have hr := restriction_map_section l E W ((sequenceRestrict l E L ι W).map (a.hom.app N)) n U
    (integralComparisonSequenceTensorSection l E L ι W (ME.tensor.obj N) (op (n, U.unop)) 1
      (PodQuotientTransition.unitSection l E W ME N n U x))
  exact eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq (hr.symm.trans hx.symm)).trans
    ((scalarRestrictionLevel_inv_heq l E L ι W n _ U _).trans (cast_heq _ _))))

end OrdinaryQuotientCube
end WeilConjectures
