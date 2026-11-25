/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryTowerComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompletedDirectImageComparison

/-! # Ordinary direct image and the coefficient limit

Source: Stacks Project, Tags 03D7 and 0941.
(blueprint: lem-sf-integral-ordinary-limit-model).
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

private theorem eqToHom_sections
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (h : M = N) (V : Cᵒᵖ) (x : M.val.obj V) :
    HEq ((eqToHom h).val.app V x) x := by
  subst N
  rfl

private def towerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y ≅
      coefficientSequenceRestriction l E X ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sfCompletedModuleDirectImage l E f) :=
  (integralOrdinaryTowerComparison l E f).exists.choose

private theorem towerComparison_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEtᵒᵖ)
    (x : (((pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y).obj M).obj
      (op n)).val.obj V) :
    HEq ((((towerComparison l E f).hom.app M).app (op n)).val.app V x) x := by
  exact (integralOrdinaryTowerComparison l E f).exists.choose_spec M n V x

attribute [local irreducible] towerComparison

private def limitOfComparison
    {A C D J : Type*} [Category A] [Category C] [Category D] [Category J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    (U : A ⥤ J ⥤ C) (V : A ⥤ J ⥤ D) (G : C ⥤ D)
    [PreservesLimitsOfShape J G]
    (e : V ≅ U ⋙ (Functor.whiskeringRight J C D).obj G) :
    V ⋙ lim ≅ U ⋙ lim ⋙ G :=
  Functor.isoWhiskerRight e lim ≪≫
    Functor.isoWhiskerLeft U (preservesLimitNatIso G).symm

private theorem limitOfComparison_projection
    {A C D J : Type*} [Category A] [Category C] [Category D] [Category J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    (U : A ⥤ J ⥤ C) (V : A ⥤ J ⥤ D) (G : C ⥤ D)
    [PreservesLimitsOfShape J G]
    (e : V ≅ U ⋙ (Functor.whiskeringRight J C D).obj G) (M : A) (j : J) :
    (limitOfComparison U V G e).hom.app M ≫ G.map (limit.π (U.obj M) j) =
      limit.π (V.obj M) j ≫ (e.hom.app M).app j := by
  change (lim.map (e.hom.app M) ≫ (preservesLimitIso G (U.obj M)).inv) ≫ _ = _
  rw [Category.assoc, preservesLimitIso_inv_π]
  exact limMap_π _ _

private theorem transport_projection
    {C D : Type*} [Category C] [Category D] {G H : C ⥤ D} (T : G ≅ H)
    {L A : C} {V : D} (c : V ⟶ G.obj L) (π : L ⟶ A) (d : V ⟶ G.obj A)
    (h : c ≫ G.map π = d) :
    (c ≫ T.hom.app L) ≫ H.map π = d ≫ T.hom.app A := by
  rw [Category.assoc, ← T.hom.naturality π, ← Category.assoc, h]

private def completedComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfCompletedModuleDirectImage l E f ≅
      proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) :=
  (integralCompletedDirectImageComparison l E f).exists.choose

private theorem completedComparison_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : scalarReductionSource l E X) (V : Y.ProEtᵒᵖ)
    (z : ((sfCompletedModuleDirectImage l E f).obj N).val.obj V) :
    HEq (((completedComparison l E f).hom.app N).val.app V z) z := by
  exact (integralCompletedDirectImageComparison l E f).exists.choose_spec N V z

attribute [local irreducible] completedComparison

private instance sfDirect_rightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfCompletedModuleDirectImage l E f).IsRightAdjoint := by
  exact ((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).ofNatIsoRight
      (completedComparison l E f).symm).isRightAdjoint

private def limitComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f ⋙ pullbackTensorOrdinaryLimit l E Y ≅
      pullbackTensorOrdinaryLimit l E X ⋙ sfCompletedModuleDirectImage l E f :=
  limitOfComparison (coefficientSequenceRestriction l E X)
    (pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y)
    (sfCompletedModuleDirectImage l E f) (towerComparison l E f)

private theorem limitComparison_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) :
    (limitComparison l E f).hom.app M ≫
      (sfCompletedModuleDirectImage l E f).map
        (limit.π ((coefficientSequenceRestriction l E X).obj M) (op n)) =
    limit.π ((coefficientSequenceRestriction l E Y).obj
      ((pullbackTensorSequenceDirect l E f).obj M)) (op n) ≫
      ((towerComparison l E f).hom.app M).app (op n) := by
  unfold limitComparison
  exact limitOfComparison_projection (coefficientSequenceRestriction l E X)
    (pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y)
    (sfCompletedModuleDirectImage l E f) (towerComparison l E f) M (op n)

attribute [local irreducible] limitComparison

private theorem ordinaryLimitProjection_heq (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) (n : ℕ) (V : W.ProEt)
    (x : ((pullbackTensorOrdinaryLimit l E W).obj M).val.obj (op V)) :
    HEq (ordinaryLimitProjection l E W M n V x)
      ((limit.π ((coefficientSequenceRestriction l E W).obj M) (op n)).val.app (op V) x) := by
  dsimp only [ordinaryLimitProjection, restrictionSection]
  simp only [eqToIso.hom, eqToHom_app]
  exact eqToHom_sections
    (CategoryTheory.Functor.congr_obj (coefficientSequenceRestriction_evaluation l E W n) M)
    (op V) ((limit.π ((coefficientSequenceRestriction l E W).obj M) (op n)).val.app (op V) x)

private def actualComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f ⋙ pullbackTensorOrdinaryLimit l E Y ≅
      pullbackTensorOrdinaryLimit l E X ⋙
        proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) :=
  limitComparison l E f ≪≫
    Functor.isoWhiskerLeft (pullbackTensorOrdinaryLimit l E X) (completedComparison l E f)

private theorem actualComparison_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) :
    (actualComparison l E f).hom.app M ≫
      (proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).map
          (limit.π ((coefficientSequenceRestriction l E X).obj M) (op n)) =
      limit.π ((coefficientSequenceRestriction l E Y).obj
        ((pullbackTensorSequenceDirect l E f).obj M)) (op n) ≫
        ((towerComparison l E f).hom.app M).app (op n) ≫ (completedComparison l E f).hom.app _ := by
  change ((limitComparison l E f).hom.app M ≫ (completedComparison l E f).hom.app _) ≫ _ = _
  exact (transport_projection (completedComparison l E f)
    ((limitComparison l E f).hom.app M) _ _
    (limitComparison_projection l E f M n)).trans (Category.assoc _ _ _)

attribute [local irreducible] actualComparison

private theorem actualComparison_projection_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEt)
    (x : ((pullbackTensorOrdinaryLimit l E Y).obj
      ((pullbackTensorSequenceDirect l E f).obj M)).val.obj (op V)) :
    HEq ((limit.π ((coefficientSequenceRestriction l E X).obj M) (op n)).val.app
      (op ((proEtaleBaseChange f).obj V))
        (((actualComparison l E f).hom.app M).val.app (op V) x))
      ((limit.π ((coefficientSequenceRestriction l E Y).obj
        ((pullbackTensorSequenceDirect l E f).obj M)) (op n)).val.app (op V) x) := by
  have hh := congrArg (fun h ↦ h.val.app (op V) x) (actualComparison_projection l E f M n)
  exact (heq_of_eq hh).trans ((completedComparison_sections l E f _ (op V) _).trans
    (towerComparison_sections l E f M n (op V) _))

private theorem model_projections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEt)
    (x : ((pullbackTensorOrdinaryLimit l E Y).obj
      ((pullbackTensorSequenceDirect l E f).obj M)).val.obj (op V)) :
    ordinaryLimitProjection l E X M n ((proEtaleBaseChange f).obj V)
      (integralPushSection l E f ((pullbackTensorOrdinaryLimit l E X).obj M) V
        (((actualComparison l E f).hom.app M).val.app (op V) x)) =
      finitePushSection l E f n ((coefficientSequenceEvaluation l E X n).obj M) V
        (((pullbackTensorSequenceDirectEvaluation l E f n).hom.app M).val.app (op V)
          (ordinaryLimitProjection l E Y ((pullbackTensorSequenceDirect l E f).obj M) n V x)) := by
  apply eq_of_heq
  exact (ordinaryLimitProjection_heq l E X M n ((proEtaleBaseChange f).obj V) _).trans
    ((actualComparison_projection_sections l E f M n V x).trans
      ((directEvaluation_sections l E f n M V _).trans
        (ordinaryLimitProjection_heq l E Y
          ((pullbackTensorSequenceDirect l E f).obj M) n V x)).symm)

/-- Direct image commutes with the ordinary coefficient limit, preserving every projection.
Source: Stacks Project, Tags 03D7 and 0941; primitive realization Step 3.
(blueprint: lem-sf-integral-ordinary-limit-model).

Proof: at each finite level use the identity-section direct-image/evaluation comparison
and the identity-section scalar-restriction comparison. The specified horizontal maps
of coefficientSequenceRestriction show these comparisons form an isomorphism of towers.
Apply the ordinary limit functor. The completed direct image is a right adjoint, so its
limit-preservation comparison is invertible. Its projection equation, together with the
identity-section normalizations of the two finite comparisons, is exactly the required
sectionwise formula. This uses ordinary module limits only. -/
theorem integralOrdinaryLimitModel : Nonempty (OrdinaryLimitModel l E) := by
  refine ⟨⟨fun f ↦ actualComparison l E f, ?_⟩⟩
  intro X Y f M n V x
  exact model_projections l E f M n V x

end WeilConjectures.IntegralSystemRealization
