/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation

/-! # Section normalization of ordinary native direct evaluation

Source: Stacks 03DI, 0D6E and 0D6J; Zheng 4.1 and 4.10
(blueprint: lem-weil-compact-support-ordinary-direct-evaluation-sections).
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

/-- Ordinary native direct evaluation in finite constant-module coordinates.
Source: Stacks 03DI and 0D6E.
(blueprint: lem-weil-compact-support-ordinary-direct-evaluation-sections). -/
def compactSupportOrdinaryDirectEvaluation {Z Y : Scheme.{u}} (g : Z ⟶ Y) (n : ℕ) :
    ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E Z n ⋙
        proEtaleConstantModuleDirectImage g
          (Padic.coefficientExtensionRing l E (n + 1)) :=
  ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g n ≪≫
    Functor.isoWhiskerLeft _
      (compactSupportDirectModel g (Padic.coefficientExtensionRing l E (n + 1)))

private theorem raw_sections
    (R : ℕ → CommRingCat.{u + 1}) (q : ∀ n, R (n + 1) ⟶ R n)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (n : ℕ)
    (M : ProEtale.VaryingRing.Modules R q Z) (V : Y.ProEtᵒᵖ)
    (x : ((ProEtale.VaryingRing.push R q g).obj M).val.obj (op (n, V.unop))) :
    HEq (((ProEtale.VaryingRing.moduleEvalP R q g n).hom.app M).val.app V x) x := by
  exact heq_of_eq ((ProEtale.VaryingRing.moduleEvalP_existsUnique R q g n).choose_spec.1
    M V.unop x)

/-- Ordinary native direct evaluation is identity on each section carrier.
Source: Stacks 03DI and 0D6E.
(blueprint: lem-weil-compact-support-ordinary-direct-evaluation-sections).
Proof: the chosen moduleEvalP has this identity-on-sections normalization. The
compactSupportDirectModel comparison also has identity underlying section maps.
Their composite therefore has identity underlying section maps. -/
theorem compactSupportOrdinaryDirectEvaluation_sections {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (n : ℕ) (M : coefficientSequenceModules.{u, u} l E Z) (V : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E Y n).obj
      ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g).obj M)).val.obj V) :
    HEq (((compactSupportOrdinaryDirectEvaluation l E g n).hom.app M).val.app V x) x := by
  change HEq (((ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) g n).hom.app M).val.app V x) x
  exact raw_sections (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) g n M V x

end WeilConjectures
