/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge

/-! # Normalized completed direct image

Source: Stacks Project, Tags 03D7 and 0941.
(blueprint: lem-sf-integral-completed-direct-image-comparison).
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

private theorem completed_direct_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) =
      sfCompletedModuleDirectImage l E f := by
  have h : proEtaleRingDirectImageMap f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) =
        sfCompletedCoefficientMap l E f := by
    change (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
        (sfCompletedCoefficientMap l E f)) = _
    exact Equiv.apply_symm_apply _ _
  unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
  rw [h]
  rfl

private theorem eqToHom_sections
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (h : M = N) (V : Cᵒᵖ) (x : M.val.obj V) :
    HEq ((eqToHom h).val.app V x) x := by
  subst N
  rfl

private theorem functor_eq_sections
    {A C : Type*} [Category A] [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {F G : A ⥤ SheafOfModules.{u + 1} R}
    (h : F = G) (M : A) (V : Cᵒᵖ) (x : (F.obj M).val.obj V) :
    HEq (((eqToIso h).hom.app M).val.app V x) x := by
  simp only [eqToIso.hom, eqToHom_app]
  exact eqToHom_sections _ _ _

/-- The two completed direct-image presentations have a unique identity-section comparison.
Source: Stacks Project, Tags 03D1 and 0941; primitive realization Step 3.
(blueprint: lem-sf-integral-completed-direct-image-comparison).

Proof: the coefficient map for the specified completed-ring pullback is the
adjoint transpose of sfCompletedCoefficientMap. Applying the direct-image
hom-equivalence returns that map. Hence the module direct-image functors are
equal. The equality gives a natural isomorphism whose component on every section
is the identity up to heterogeneous equality. Sectionwise extensionality shows
that this normalization determines the natural isomorphism uniquely. -/
theorem integralCompletedDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : sfCompletedModuleDirectImage l E f ≅
      proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f),
      ∀ (N : scalarReductionSource l E X) (V : Y.ProEtᵒᵖ)
        (x : ((sfCompletedModuleDirectImage l E f).obj N).val.obj V),
        HEq ((e.hom.app N).val.app V x) x := by
  let T := eqToIso ((completed_direct_eq l E f).symm)
  have ht : ∀ (N : scalarReductionSource l E X) (V : Y.ProEtᵒᵖ)
      (x : ((sfCompletedModuleDirectImage l E f).obj N).val.obj V),
      HEq ((T.hom.app N).val.app V x) x := by
    intro N V x
    exact functor_eq_sections ((completed_direct_eq l E f).symm) N V x
  refine ⟨T, ht, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext N
  ext V x
  exact eq_of_heq ((he N V x).trans (ht N V x).symm)

end WeilConjectures.IntegralSystemRealization
