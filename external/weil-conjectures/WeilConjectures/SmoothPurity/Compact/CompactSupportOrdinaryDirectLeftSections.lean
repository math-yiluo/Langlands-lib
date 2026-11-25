/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectEvaluationSections
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition

/-! # Sections of the left ordinary direct-evaluation composite

Source: Stacks 03DI and 0D6E
(blueprint: lem-weil-compact-support-ordinary-direct-left-sections).
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

private theorem comparison_sections
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (φ : A →+* B)
    (M : proEtaleRingModules Z (proEtaleConstantRing Z B)) (V : Y.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange g).op.obj V)) :
    HEq (((proEtaleCoefficientDirectImageComparison g φ).hom.app M).val.app V x) x := by
  exact heq_of_eq ((proEtaleCoefficientDirectImageComparison_existsUnique g φ).choose_spec.1
    M V x)

private theorem restrict_map_sections
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    {M N : proEtaleRingModules Y (proEtaleConstantRing Y B)} (f : M ⟶ N)
    (V : Y.ProEtᵒᵖ) (x : M.val.obj V) :
    (((proEtaleCoefficientRestrictScalars Y φ).map f).val.app V) x =
      f.val.app V x := by
  rfl

attribute [local irreducible] compactSupportOrdinaryDirectEvaluation
  ProEtale.VaryingRing.moduleEvalP
  compactSupportOrdinaryCoefficientTransition proEtaleCoefficientDirectImageComparison

-- The formula compares scalar actions on the same underlying section carriers.
/-- The left ordinary coefficient-transition composite is horizontal restriction.
Source: Stacks 03DI and 0D6E.
(blueprint: lem-weil-compact-support-ordinary-direct-left-sections).
Proof: The scalar direct-image comparison and restricted evaluation are identity on sections.
The horizontal coefficient map is restriction along the horizontal product arrow.
Native direct image applies the base-change functor to that arrow, which preserves
its index and identity components. Thus the composite is horizontal restriction of M. -/
theorem compactSupportOrdinaryDirectLeftSections
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules.{u, u} l E Z) (V : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E Y m).obj
      ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g).obj M)).val.obj V) :
    HEq (((proEtaleCoefficientDirectImageComparison g
        (compactSupportLevelQuotient l E m n h)).hom.app
          ((coefficientSequenceEvaluation l E Z n).obj M)).val.app V
      (((proEtaleCoefficientRestrictScalars Y (compactSupportLevelQuotient l E m n h)).map
        ((compactSupportOrdinaryDirectEvaluation l E g n).hom.app M)).val.app V
          (((compactSupportOrdinaryCoefficientTransition l E Y h).app
            ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
              (compactSupportSystemQuotient l E) g).obj M)).val.app V x)))
      (M.val.map (Prod.mkHom (homOfLE h)
        (𝟙 ((proEtaleBaseChange g).op.obj V).unop)).op x) := by
  let P := ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) g
  let tY := (compactSupportOrdinaryCoefficientTransition l E Y h).app (P.obj M)
  let en := (compactSupportOrdinaryDirectEvaluation l E g n).hom.app M
  let W := (proEtaleBaseChange g).op.obj V
  have hY := compactSupportOrdinaryCoefficientTransition_sections l E Y h (P.obj M) V
  have hc := comparison_sections g (compactSupportLevelQuotient l E m n h)
    ((coefficientSequenceEvaluation l E Z n).obj M) V
    (((proEtaleCoefficientRestrictScalars Y
      (compactSupportLevelQuotient l E m n h)).map en).val.app V (tY.val.app V x))
  have hr := heq_of_eq (restrict_map_sections (compactSupportLevelQuotient l E m n h)
    Y en V (tY.val.app V x))
  have he : HEq (en.val.app V (tY.val.app V x)) (tY.val.app V x) :=
    compactSupportOrdinaryDirectEvaluation_sections l E g n M V (tY.val.app V x)
  have hy := heq_of_eq (congr_heq hY (HEq.rfl : HEq x x))
  have hb : (ProEtale.VaryingRing.baseChange g).map
      (Prod.mkHom (homOfLE h) (𝟙 V.unop)) =
    Prod.mkHom (homOfLE h) (𝟙 W.unop) := by
    ext <;> simp [ProEtale.VaryingRing.baseChange, W]
  have hp : HEq ((P.obj M).val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x)
      (M.val.map (Prod.mkHom (homOfLE h) (𝟙 W.unop)).op x) := by
    change HEq (M.val.map ((ProEtale.VaryingRing.baseChange g).map
      (Prod.mkHom (homOfLE h) (𝟙 V.unop))).op x) _
    rw [hb]
    rfl
  exact hc.trans (hr.trans (he.trans (hy.trans hp)))

end WeilConjectures
