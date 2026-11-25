/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarDirectNormalization
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectTransition
import WeilConjectures.SmoothPurity.Compact.CompactSupportRawDirectNormalization

/-! # Coefficient compatibility of native direct evaluation

Source: Stacks 03DI, 0D6E and 0D6J; Zheng 4.1 and 4.10
(blueprint: lem-weil-compact-support-native-direct-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- The direct-image part of the specified native evaluation, in constant-module coordinates.
Source: Stacks 03DI and 0D6E; Zheng, Construction 4.1 and Lemma 4.10.
(blueprint: lem-weil-compact-support-native-direct-transition). -/
def compactSupportNativeDirectEvaluation {Z Y : Scheme.{u}} (g : Z ⟶ Y) (n : ℕ) :
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙
      coefficientSequenceDerivedEvaluation.{u, u} l E Y n ≅
    coefficientSequenceDerivedEvaluation.{u, u} l E Z n ⋙
      proEtaleConstantDerivedDirectImage g
        (Padic.coefficientExtensionRing l E (n + 1)) := by
  have := proEtaleConstantModuleDirectImage_additive g
    (Padic.coefficientExtensionRing l E (n + 1))
  exact ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g n ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
      (compactSupportDirectModel g (Padic.coefficientExtensionRing l E (n + 1))))

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

private instance nativeHasDerived (W : Scheme.{u}) :
    HasDerivedCategory.{u + 2} (ProEtale.VaryingRing.Modules (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) W) :=
  coefficientSequenceHasDerived.{u, u} l E W

attribute [local instance] nativeHasDerived

private theorem unitQ_homotopy
    {A B : Type (v + 1)} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ) :
    F.rightDerivedFunctorUnitQ I =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj I) := by
  change 𝟙 _ ≫ F.rightDerivedFunctorUnit.app _ ≫ F.rightDerivedFunctor.map (𝟙 _) = _
  erw [F.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  rfl

private theorem derivedIso_unitQ
    {A B : Type (v + 1)} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A]
    {F H : A ⥤ B} [F.Additive] [H.Additive] (e : F ≅ H)
    (I : CochainComplex A ℤ) :
    F.rightDerivedFunctorUnitQ I ≫
        (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) ≫
        H.rightDerivedFunctorUnitQ I := by
  have h := Functor.rightDerivedNatTrans_app F.rightDerivedFunctor H.rightDerivedFunctor
    F.rightDerivedFunctorUnit H.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso A (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh)
    ((HomotopyCategory.quotient A (.up ℤ)).obj I)
  simp only [Functor.whiskerRight_app] at h
  change F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≫
        (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) ≫
        H.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient A (.up ℤ)).obj I) at h
  simp only [unitQ_homotopy]
  convert h using 1
  rfl

private theorem normalized_postcompose
    {A B C D : Type (v + 1)}
    [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (F : A ⥤ B) (G H : C ⥤ D) (x : A ⥤ C) (y : B ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [x.Additive] [y.Additive]
    (X : DerivedCategory.{w} A ⥤ DerivedCategory.{w} C)
    (Y : DerivedCategory.{w} B ⥤ DerivedCategory.{w} D)
    (xf : DerivedCategory.Q ⋙ X ≅ x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf : DerivedCategory.Q ⋙ Y ≅ y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F ⋙ y ≅ x ⋙ G) (b : F.rightDerivedFunctor ⋙ Y ≅ X ⋙ G.rightDerivedFunctor)
    (e : G ≅ H)
    (hb : ExactDerivedSquare.unitNormalized F G x y X Y xf yf c.hom b.hom) :
    ExactDerivedSquare.unitNormalized F H x y X Y xf yf
      (c ≪≫ Functor.isoWhiskerLeft x e).hom
      (b ≪≫ Functor.isoWhiskerLeft X (Functor.rightDerivedFunctorNatIso e)).hom := by
  intro I
  have hn := (Functor.rightDerivedFunctorNatIso e).hom.naturality (xf.hom.app I)
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  erw [← hn]
  erw [reassoc_of% (hb I)]
  erw [derivedIso_unitQ e]
  simp only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

-- Compare the native presentation with the specified finite coefficient categories.
private theorem native_normalized {Z Y : Scheme.{u}} (g : Z ⟶ Y) (n : ℕ) :
    @CategoryTheory.ExactDerivedSquare.unitNormalized.{u + 1, u + 2}
      (coefficientSequenceModules.{u, u} l E Z)
      (coefficientSequenceModules.{u, u} l E Y)
      (proEtaleRingModules Z (proEtaleConstantRing Z
        (Padic.coefficientExtensionRing l E (n + 1))))
      (proEtaleRingModules Y (proEtaleConstantRing Y
        (Padic.coefficientExtensionRing l E (n + 1))))
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (coefficientSequenceHasDerived.{u, u} l E Z)
      (coefficientSequenceHasDerived.{u, u} l E Y)
      inferInstance inferInstance
      (ProEtale.VaryingRing.modules_kInjective (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) Z) inferInstance
      (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g)
      (proEtaleConstantModuleDirectImage g
        (Padic.coefficientExtensionRing l E (n + 1)))
      (coefficientSequenceEvaluation.{u, u} l E Z n)
      (coefficientSequenceEvaluation.{u, u} l E Y n)
      (ProEtale.VaryingRing.push_additive (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g)
      (proEtaleConstantModuleDirectImage_additive g
        (Padic.coefficientExtensionRing l E (n + 1)))
      (coefficientSequenceEvaluation_additive l E Z n)
      (coefficientSequenceEvaluation_additive l E Y n)
      (coefficientSequenceDerivedEvaluation l E Z n)
      (coefficientSequenceDerivedEvaluation l E Y n)
      (coefficientSequenceEvaluation.{u, u} l E Z n).mapDerivedCategoryFactors
      (coefficientSequenceEvaluation.{u, u} l E Y n).mapDerivedCategoryFactors
      (compactSupportOrdinaryDirectEvaluation l E g n).hom
      (compactSupportNativeDirectEvaluation l E g n).hom := by
  have := proEtaleConstantModuleDirectImage_additive g
    (Padic.coefficientExtensionRing l E (n + 1))
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  exact normalized_postcompose (ProEtale.VaryingRing.push R q g)
    (ProEtale.StrictTower.moduleDirectImage (R n) g)
    (proEtaleConstantModuleDirectImage g (Padic.coefficientExtensionRing l E (n + 1)))
    (ProEtale.VaryingRing.eval R q Z n) (ProEtale.VaryingRing.eval R q Y n)
    (ProEtale.VaryingRing.ev R q Z n) (ProEtale.VaryingRing.ev R q Y n)
    (ProEtale.VaryingRing.eval R q Z n).mapDerivedCategoryFactors
    (ProEtale.VaryingRing.eval R q Y n).mapDerivedCategoryFactors
    (ProEtale.VaryingRing.moduleEvalP R q g n) (ProEtale.VaryingRing.evalP R q g n)
    (compactSupportDirectModel g (Padic.coefficientExtensionRing l E (n + 1)))
    (compactSupportRawDirectNormalization R q g n)

/-- Direct-image evaluation respects every horizontal coefficient map of a derived system.
Source: Stacks 0D6E and 0D6J; Zheng, Construction 4.1 and Lemma 4.10;
the direct-image step of the native compact-support transition proof.
(blueprint: lem-weil-compact-support-native-direct-transition).
Proof: specialize the restriction-transition calculation for simultaneous direct image to
the positive coefficient sheaves. The all-pair sheaf quotient is the direct quotient by
compactSupportQuotient_eq, and the horizontal transformation is the actual section map,
as in compactSupportOrdinaryCoefficientTransition. Identify the native evaluation mate
with the simultaneous direct-image evaluation using moduleEvalP's identity on sections
and moduleEvalG's unit normalization. The uniqueness of right-derived comparison makes
this identification valid on arbitrary unbounded derived systems. For the coefficient
comparison use the K-injective normalization in systemPushforwardRestrictionTransition:
choose a K-injective complex at level n and a K-injective replacement of its restriction
at level m. The inverse comparison is represented by the ordinary direct-image map of
this replacement. After transport by compactSupportDirectModel, the ordinary coefficient
comparison is still identity on sections. The normalization specifying
proEtaleDerivedDirectImage_restrictScalars therefore gives the very same map; its inverse
is sfDerivedImageRestriction. This compares the named maps, not just their isomorphism
classes. Naturality transports the equality from K-injective representatives to every
derived system, giving the displayed square. No preservation of K-injectives by scalar
restriction or evaluation is used. The calculation includes n=m and noncartesian systems. -/
theorem compactSupportNativeDirectTransition
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (M : coefficientSequenceDerived.{u, u} l E Z) :
    (compactSupportCoefficientTransition l E Y h).app
        ((ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) g).obj M) ≫
      (proEtaleCoefficientRestrictScalars Y
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
          ((compactSupportNativeDirectEvaluation l E g n).hom.app M) =
    (compactSupportNativeDirectEvaluation l E g m).hom.app M ≫
      (proEtaleConstantDerivedDirectImage g
        (Padic.coefficientExtensionRing l E (m + 1))).map
          ((compactSupportCoefficientTransition l E Z h).app M) ≫
      (sfDerivedImageRestriction g (compactSupportLevelQuotient l E m n h)).hom.app
        ((coefficientSequenceDerivedEvaluation l E Z n).obj M) := by
  -- The direct section square also avoids transport through simultaneous coordinates.
  let F : coefficientSequenceModules.{u, u} l E Z ⥤
      coefficientSequenceModules.{u, u} l E Y :=
    ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g
  have : F.Additive := ProEtale.VaryingRing.push_additive (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) g
  have := coefficientSequenceEvaluation_additive l E Z m
  have := coefficientSequenceEvaluation_additive l E Y m
  have := coefficientSequenceEvaluation_additive l E Z n
  have := coefficientSequenceEvaluation_additive l E Y n
  have := proEtaleConstantModuleDirectImage_additive g
    (Padic.coefficientExtensionRing l E (m + 1))
  have := proEtaleConstantModuleDirectImage_additive g
    (Padic.coefficientExtensionRing l E (n + 1))
  apply (cancel_mono
    ((sfDerivedImageRestriction g (compactSupportLevelQuotient l E m n h)).inv.app
      ((coefficientSequenceDerivedEvaluation l E Z n).obj M))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  exact @CategoryTheory.ExactDerivedSquare.normalized_transition.{u + 1, u + 2}
    (coefficientSequenceModules.{u, u} l E Z)
    (coefficientSequenceModules.{u, u} l E Y)
    (proEtaleRingModules Z (proEtaleConstantRing Z
      (Padic.coefficientExtensionRing l E (m + 1))))
    (proEtaleRingModules Y (proEtaleConstantRing Y
      (Padic.coefficientExtensionRing l E (m + 1))))
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (coefficientSequenceHasDerived.{u, u} l E Z)
    (coefficientSequenceHasDerived.{u, u} l E Y) inferInstance inferInstance
    (ProEtale.VaryingRing.modules_kInjective (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) Z) inferInstance
    F
    (proEtaleConstantModuleDirectImage g (Padic.coefficientExtensionRing l E (m + 1)))
    (coefficientSequenceEvaluation.{u, u} l E Z m)
    (coefficientSequenceEvaluation.{u, u} l E Y m)
    (ProEtale.VaryingRing.push_additive (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g)
    (proEtaleConstantModuleDirectImage_additive g
      (Padic.coefficientExtensionRing l E (m + 1)))
    (coefficientSequenceEvaluation_additive l E Z m)
    (coefficientSequenceEvaluation_additive l E Y m)
    (coefficientSequenceEvaluation_limits l E Z m)
    (coefficientSequenceEvaluation_colimits l E Z m)
    (coefficientSequenceEvaluation_limits l E Y m)
    (coefficientSequenceEvaluation_colimits l E Y m)
    (proEtaleRingModules Z (proEtaleConstantRing Z
      (Padic.coefficientExtensionRing l E (n + 1))))
    (proEtaleRingModules Y (proEtaleConstantRing Y
      (Padic.coefficientExtensionRing l E (n + 1))))
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (proEtaleConstantModuleDirectImage g (Padic.coefficientExtensionRing l E (n + 1)))
    (coefficientSequenceEvaluation.{u, u} l E Z n)
    (coefficientSequenceEvaluation.{u, u} l E Y n)
    (proEtaleCoefficientRestrictScalars Z (compactSupportLevelQuotient l E m n h))
    (proEtaleCoefficientRestrictScalars Y (compactSupportLevelQuotient l E m n h))
    (proEtaleConstantModuleDirectImage_additive g
      (Padic.coefficientExtensionRing l E (n + 1)))
    (coefficientSequenceEvaluation_additive l E Z n)
    (coefficientSequenceEvaluation_additive l E Y n)
    inferInstance inferInstance
    (coefficientSequenceEvaluation_limits l E Z n)
    (coefficientSequenceEvaluation_colimits l E Z n)
    (coefficientSequenceEvaluation_limits l E Y n)
    (coefficientSequenceEvaluation_colimits l E Y n)
    inferInstance inferInstance inferInstance inferInstance
    (compactSupportOrdinaryDirectEvaluation l E g m)
    (compactSupportOrdinaryDirectEvaluation l E g n)
    (proEtaleCoefficientDirectImageComparison g (compactSupportLevelQuotient l E m n h))
    (compactSupportNativeDirectEvaluation l E g m)
    (compactSupportNativeDirectEvaluation l E g n)
    (sfDerivedImageRestriction g (compactSupportLevelQuotient l E m n h)).symm
    (native_normalized l E g m) (native_normalized l E g n)
    (compactSupportScalarDirectNormalization g (compactSupportLevelQuotient l E m n h))
    (compactSupportOrdinaryCoefficientTransition l E Z h)
    (compactSupportOrdinaryCoefficientTransition l E Y h)
    (compactSupportCoefficientTransition l E Z h)
    (compactSupportCoefficientTransition l E Y h)
    (compactSupportCoefficientTransition_fac l E Z h)
    (compactSupportCoefficientTransition_fac l E Y h)
    (compactSupportOrdinaryDirectTransition l E g h) M

end WeilConjectures
