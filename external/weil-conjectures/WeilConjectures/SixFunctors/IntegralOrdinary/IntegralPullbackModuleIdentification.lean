/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorPullModel
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # The module pullback comparison and its adjunction units -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local implicit_reducible] PurCompactSupport.completed
  completedIntegralCommRingSheafUnrestricted
  ordinaryIntegralModulePush ordinaryIntegralPullComplex IntegralOnSlice.Site
attribute [-instance] OpenFactorCoherence.siteLocallyBijective
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] integralOperationsSiteSmall scalarReductionSourceDerived
  scalarReductionTargetDerived integralOperationsCommHasDerivedCategory
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local instance 4000] ordinaryIntegralModulePull_additive
attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted SheafOfModules.monoidalCategory
  ordinaryIntegralModulePull
  Functor.mapDerivedCategory proEtaleRingDerivedPullbackFactors
  ordinaryIntegralPullComplexCounit sfCompletedCoefficientMap ordinaryIntegralDirectRingMap

private def push_iso_aux {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X))
    (h : q = sfCompletedCoefficientMap l E f) :
    SheafOfModules.pushforward.{u + 1}
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map q) ≅
      ordinaryIntegralModulePush l E f := by
  unfold ordinaryIntegralModulePush
  rw [h]
  exact SheafOfModules.pushforwardCongr (directRing_eq l E f)

/-- The actual module direct images agree by equality of their direct ring maps.
Source: Stacks 03D1 and 03D2.
(blueprint: def-sf-integral-pullback-pushforward-identification).

Construct the isomorphism with pushforwardCongr after identifying the direct map
adjoint to the completed coefficient map with the recorded ordinary direct ring map. -/
def pullbackPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) ≅
      ordinaryIntegralModulePush l E f := by
  have hm : proEtaleRingDirectImageMap f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) =
      sfCompletedCoefficientMap l E f :=
    (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E f)
  unfold proEtaleRingModuleDirectImage ordinaryIntegralModulePush
  rw [hm]
  exact SheafOfModules.pushforwardCongr (directRing_eq l E f)

private theorem push_iso_aux_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X))
    (h : q = sfCompletedCoefficientMap l E f)
    (M : integralTowerModules l E X) (V : Y.ProEt)
    (x : M.val.obj (op ((proEtaleBaseChange f).obj V))) :
    ((push_iso_aux l E f q h).hom.app M).val.app (op V) x = x := by
  subst q
  rfl

private theorem pullbackPushforwardIso_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : integralTowerModules l E X) (V : Y.ProEt)
    (x : M.val.obj (op ((proEtaleBaseChange f).obj V))) :
    ((pullbackPushforwardIso l E f).hom.app M).val.app (op V) x = x :=
  push_iso_aux_section l E f _
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E f)) M V x

/-- The module pullback isomorphism determined by the completed-ring adjunctions.
Source: Stacks 03D2.
(blueprint: def-sf-integral-pullback-module-identification).

Transport the actual ringed module adjunction through pullbackPushforwardIso and
apply uniqueness of left adjoints to the specified ordinary module adjunction. -/
def pullbackModuleIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleRingModulePullback f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) :
      integralTowerModules l E Y ⥤ integralTowerModules l E X) ≅
      ordinaryIntegralModulePull l E f :=
  ((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).ofNatIsoRight
      (pullbackPushforwardIso l E f)).leftAdjointUniq (ordinaryIntegralModuleAdjunction l E f)

private theorem pullbackModuleIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pullbackModuleIso l E f).hom.app M).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app (op V) x) =
      (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op V) x) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)).ofNatIsoRight (pullbackPushforwardIso l E f))
    (ordinaryIntegralModuleAdjunction l E f) M
  rw [Adjunction.ofNatIsoRight_unit] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [Category.assoc, ← (pullbackPushforwardIso l E f).hom.naturality] at h
  have hh := congrArg (fun a ↦ a.val.app (op V) x) h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, pullbackPushforwardIso_section] at hh
  exact hh

/-- The inverse module comparison preserves adjunction-unit sections.
Source: Stacks 03D2.
(blueprint: lem-sf-integral-pullback-module-unit).

Proof: uniqueness of left adjoints preserves the units. The pushforward comparison
is identity on underlying sections, so evaluate the unit identity on a section.
Apply the inverse module comparison and cancel its composite with the hom. -/
theorem pullbackModuleIso_inv_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pullbackModuleIso l E f).inv.app M).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op V) x) =
      (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app (op V) x) := by
  have h := congrArg
    (((pullbackModuleIso l E f).inv.app M).val.app (op ((proEtaleBaseChange f).obj V)))
    (pullbackModuleIso_unit l E f M V x)
  change (((pullbackModuleIso l E f).hom.app M ≫
      (pullbackModuleIso l E f).inv.app M).val.app
        (op ((proEtaleBaseChange f).obj V))) _ = _ at h
  rw [Iso.hom_inv_id_app] at h
  exact h.symm

end WeilConjectures.IntegralOrdinary
