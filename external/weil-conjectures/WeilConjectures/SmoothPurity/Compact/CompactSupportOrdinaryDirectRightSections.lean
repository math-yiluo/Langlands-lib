/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectEvaluationSections
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition

/-! # Sections of the right ordinary direct-evaluation composite

Source: Stacks 03DI and 0D6E
(blueprint: lem-weil-compact-support-ordinary-direct-right-sections).
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

attribute [local irreducible] compactSupportOrdinaryDirectEvaluation
  ProEtale.VaryingRing.moduleEvalP
  compactSupportOrdinaryCoefficientTransition

-- The formula compares scalar actions on the same underlying section carriers.
/-- The right ordinary coefficient-transition composite is horizontal restriction.
Source: Stacks 03DI and 0D6E.
(blueprint: lem-weil-compact-support-ordinary-direct-right-sections).
Proof: Ordinary evaluation is identity on section carriers. The horizontal coefficient
map on M is restriction along the horizontal product arrow. Ordinary direct image
leaves the underlying component maps unchanged, so the composite has the stated formula. -/
theorem compactSupportOrdinaryDirectRightSections
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules.{u, u} l E Z) (V : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E Y m).obj
      ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g).obj M)).val.obj V) :
    HEq (((proEtaleConstantModuleDirectImage g
        (Padic.coefficientExtensionRing l E (m + 1))).map
          ((compactSupportOrdinaryCoefficientTransition l E Z h).app M)).val.app V
            (((compactSupportOrdinaryDirectEvaluation l E g m).hom.app M).val.app V x))
      (M.val.map (Prod.mkHom (homOfLE h)
        (𝟙 ((proEtaleBaseChange g).op.obj V).unop)).op x) := by
  let tZ := (compactSupportOrdinaryCoefficientTransition l E Z h).app M
  let em := (compactSupportOrdinaryDirectEvaluation l E g m).hom.app M
  let W := (proEtaleBaseChange g).op.obj V
  change HEq (tZ.val.app W (em.val.app V x)) _
  have hZ := compactSupportOrdinaryCoefficientTransition_sections l E Z h M W
  have hm : HEq (em.val.app V x) x :=
    compactSupportOrdinaryDirectEvaluation_sections l E g m M V x
  exact heq_of_eq (congr_heq hZ hm)

end WeilConjectures
