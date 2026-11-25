/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportOpenScalarRestriction
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectTransition

/-! # Horizontal compatibility of native direct image

Source: Stacks Project, Tags 03DA, 03D3 and 0941; Zheng 4.1.
(blueprint: lem-weil-compact-support-ordinary-direct-image-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf presheafToSheaf
namespace WeilConjectures

private theorem transportDirectImageSquare
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {P Q : C ⥤ D} {P' Q' : C' ⥤ D'} (R : C' ⥤ C) (S : D' ⥤ D)
    (a : P ≅ Q) (b : P' ≅ Q') (d : Q' ⋙ S ≅ R ⋙ Q)
    {A : C} {B : C'} {U : D} {V : D'}
    (t : A ⟶ R.obj B) (s : U ⟶ S.obj V) (e : U ⟶ P.obj A) (e' : V ⟶ P'.obj B)
    (h : s ≫ S.map (e' ≫ b.hom.app B) ≫ d.hom.app B =
      (e ≫ a.hom.app A) ≫ Q.map t) :
    s ≫ S.map e' ≫
        (Functor.isoWhiskerRight b S ≪≫ d ≪≫
          Functor.isoWhiskerLeft R a.symm).hom.app B =
      e ≫ P.map t := by
  apply (cancel_mono (a.hom.app (R.obj B))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id, a.hom.naturality]
  simpa only [Functor.map_comp, Category.assoc] using h

attribute [local irreducible] Functor.ofSequence Functor.ofOpSequence
  Functor.leftAdjoint HasDerivedCategory.standard MorphismProperty.Over.pullback
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  coefficientSequenceEvaluation integralCoefficientSheafTransition
  compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.evaluation SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

attribute [local irreducible] compactSupportDirectModel
  compactSupportOrdinaryCoefficientTransition ProEtale.VaryingRing.moduleEvalP
  proEtaleCoefficientDirectImageComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary horizontal coefficient map commutes with direct image.
Source: Stacks Project, Tags 03DA, 03D3 and 0941.
(blueprint: lem-weil-compact-support-ordinary-direct-image-transition).
Proof: the evaluation and scalar direct-image comparisons preserve each section.
The horizontal coefficient map is the actual restriction of the module presheaf,
and base change of the product site preserves its horizontal arrow. Thus both
composites agree on every section. -/
theorem compactSupportOrdinaryDirectImageTransition {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (M : coefficientSequenceModules.{u, u} l E X) :
    (compactSupportOrdinaryCoefficientTransition l E Y h).app
        ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f).obj M) ≫
      (proEtaleCoefficientRestrictScalars Y (compactSupportLevelQuotient l E m n h)).map
        ((ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f n).hom.app M) ≫
      (compactSupportScalarDirectImage f (compactSupportLevelQuotient l E m n h)).hom.app
        ((coefficientSequenceEvaluation l E X n).obj M) =
    (ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f m).hom.app M ≫
      (ProEtale.StrictTower.moduleDirectImage
        (compactSupportSystemLevel l E m) f).map
          ((compactSupportOrdinaryCoefficientTransition l E X h).app M) := by
  have hs := compactSupportOrdinaryDirectTransition l E f h M
  simp only [compactSupportOrdinaryDirectEvaluation, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] at hs
  exact transportDirectImageSquare
    (proEtaleCoefficientRestrictScalars X (compactSupportLevelQuotient l E m n h))
    (proEtaleCoefficientRestrictScalars Y (compactSupportLevelQuotient l E m n h))
    (compactSupportDirectModel f (Padic.coefficientExtensionRing l E (m + 1)))
    (compactSupportDirectModel f (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleCoefficientDirectImageComparison f (compactSupportLevelQuotient l E m n h))
    ((compactSupportOrdinaryCoefficientTransition l E X h).app M)
    ((compactSupportOrdinaryCoefficientTransition l E Y h).app
      ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f).obj M))
    ((ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f m).hom.app M)
    ((ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f n).hom.app M)
    hs

end WeilConjectures
