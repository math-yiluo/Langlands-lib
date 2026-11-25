/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectEvaluationSections
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectLeftSections
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectRightSections

/-! # Ordinary coefficient compatibility of direct evaluation

Source: Stacks 03DI and 0D6E
(blueprint: lem-weil-compact-support-ordinary-direct-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance] coefficientSequenceEvaluation_additiveInstance
  HasDerivedCategory.standard
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Compare the named scalar sheaves without unfolding their sheafification constructions.
attribute [local irreducible] Functor.ofSequence Functor.ofOpSequence
  constantSheaf presheafToSheaf Functor.leftAdjoint
  HasDerivedCategory.standard MorphismProperty.Over.pullback

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  coefficientSequenceEvaluation
  integralCoefficientSheafTransition compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.evaluation SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

-- The identities compare concrete scalar actions on the same section carriers.
/-- Ordinary native direct evaluation respects the actual horizontal coefficient maps.
Source: Stacks 03DI and 0D6E.
(blueprint: lem-weil-compact-support-ordinary-direct-transition).
Proof: moduleEvalP and compactSupportDirectModel are identity on section carriers.
The horizontal coefficient transformations act by the horizontal restriction of the
sequence sheaf, and the ordinary scalar direct-image comparison is identity on sections.
Base change preserves the horizontal product arrow. Apply these section formulas to both
sides, then use extensionality of module-sheaf maps. -/
theorem compactSupportOrdinaryDirectTransition {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (M : coefficientSequenceModules.{u, u} l E Z) :
    (compactSupportOrdinaryCoefficientTransition l E Y h).app
        ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) g).obj M) ≫
      (proEtaleCoefficientRestrictScalars Y (compactSupportLevelQuotient l E m n h)).map
        ((compactSupportOrdinaryDirectEvaluation l E g n).hom.app M) ≫
      (proEtaleCoefficientDirectImageComparison g
        (compactSupportLevelQuotient l E m n h)).hom.app
          ((coefficientSequenceEvaluation.{u, u} l E Z n).obj M) =
    (compactSupportOrdinaryDirectEvaluation l E g m).hom.app M ≫
      (proEtaleConstantModuleDirectImage g
        (Padic.coefficientExtensionRing l E (m + 1))).map
          ((compactSupportOrdinaryCoefficientTransition l E Z h).app M) := by
  ext V x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hl := compactSupportOrdinaryDirectLeftSections l E g h M V x
  have hr := compactSupportOrdinaryDirectRightSections l E g h M V x
  exact eq_of_heq (hl.trans hr.symm)

end WeilConjectures
