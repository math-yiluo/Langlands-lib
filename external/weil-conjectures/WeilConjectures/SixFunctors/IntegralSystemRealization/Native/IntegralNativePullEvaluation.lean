/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeDirectComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeOrdinaryPullEvaluation
import all WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralDirectEvaluationMateInvertible
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived native pullback evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  coefficientSequenceEvaluation_additiveInstance coefficientSequenceEvaluation_limits
  coefficientSequenceEvaluation_colimits sfIntrinsicPullback_additive
  sfIntrinsicPullback_preservesFiniteLimits sfIntrinsicPullback_preservesFiniteColimits
attribute [local irreducible] constantSheaf presheafToSheaf Functor.ofSequence
  Functor.ofOpSequence MorphismProperty.Over.pullback
attribute [local implicit_reducible] ProEtale.StrictTower.modulePullback
  ProEtale.StrictTower.moduleDirectImage

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

private def ordinaryPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceInverse l E f ≅
      ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f :=
  ((pullbackTensorSequenceAdjunction l E f).ofNatIsoRight
    (integralNativeOrdinaryDirectIso l E f)).leftAdjointUniq
      (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f)

private theorem localizePullSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F F' : A ⥤ B} {E : B ⥤ D} {H : A ⥤ C} {G G' : C ⥤ D}
    [F.Additive] [F'.Additive] [E.Additive] [H.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (κ : F ≅ F') (q : G' ≅ G) (δ : F ⋙ E ≅ H ⋙ G) (δ' : F' ⋙ E ≅ H ⋙ G')
    (h : ∀ M, E.map (κ.hom.app M) ≫ δ'.hom.app M ≫ q.hom.app (H.obj M) = δ.hom.app M)
    (M : DerivedCategory A) :
    E.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso κ).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso δ').hom.app M ≫
      (Functor.mapDerivedCategoryNatIso q).hom.app (H.mapDerivedCategory.obj M) =
      (Functor.mapDerivedCategorySquareIso δ).hom.app M := by
  have ho : Functor.isoWhiskerRight κ E ≪≫ δ' ≪≫ Functor.isoWhiskerLeft H q = δ := by
    apply Iso.ext
    ext N
    exact h N
  have hp := Functor.mapDerivedCategoryNatIso_isoWhiskerRight κ E
  have hq := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft H q
  have hp' : Functor.whiskerRight (Functor.mapDerivedCategoryNatIso κ).hom
      E.mapDerivedCategory ≫ (Functor.mapDerivedCategoryCompIso F' E).hom =
      (Functor.mapDerivedCategoryCompIso F E).hom ≫
        (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight κ E)).hom := by
    apply (cancel_epi (Functor.mapDerivedCategoryCompIso F E).inv).1
    rw [Iso.inv_hom_id_assoc, ← reassoc_of% hp, Iso.inv_hom_id, Category.comp_id]
  have hd : Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso κ)
        E.mapDerivedCategory ≪≫ Functor.mapDerivedCategorySquareIso δ' ≪≫
      Functor.isoWhiskerLeft H.mapDerivedCategory (Functor.mapDerivedCategoryNatIso q) =
        Functor.mapDerivedCategorySquareIso δ := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Category.assoc]
    rw [reassoc_of% hp', ← hq]
    simpa only [Functor.mapDerivedCategoryNatIso_trans, Iso.trans_hom, Category.assoc] using
      congrArg (fun z ↦ (Functor.mapDerivedCategoryCompIso F E).hom ≫
        (Functor.mapDerivedCategoryNatIso z).hom ≫
          (Functor.mapDerivedCategoryCompIso H G).inv) ho
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    congrArg (fun z ↦ z.hom.app M) hd

/-- The specified native inverse-image comparison preserves derived finite evaluation.
Source: Stacks 03D2 and 0941; blueprint fix-prop-coherence, coefficient comparisons.
(blueprint: lem-sf-integral-native-pull-evaluation).

Proof: localize the ordinary normalized pullback evaluation square. Localization of
whiskered natural isomorphisms and the standard exact-functor composition isomorphisms
preserves its composite. The cochain normalization of pullbackTensorDerivedEvaluation
identifies the resulting square with the specified comparison, on arbitrary unbounded
systems. No properness or faithfulness of evaluation is needed. -/
theorem integralNativePullEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : System l E Y) :
    let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((integralNativePullIso l E f).hom.app M) ≫
      (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso
        (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f)).hom.app
          ((coefficientSequenceDerivedEvaluation l E Y n).obj M) =
      (pullbackTensorDerivedEvaluation l E f n).hom.app M := by
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let := ProEtale.VaryingRing.pullAdditive (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  let := ProEtale.VaryingRing.pullLimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  let := ProEtale.VaryingRing.pullColimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  let : (coefficientSequenceEvaluation l E X n).Additive :=
    coefficientSequenceEvaluation_additive l E X n
  let : (coefficientSequenceEvaluation l E Y n).Additive :=
    coefficientSequenceEvaluation_additive l E Y n
  let : PreservesFiniteLimits (coefficientSequenceEvaluation l E X n) :=
    (coefficientSequenceEvaluation_exact l E X n).1
  let : PreservesFiniteColimits (coefficientSequenceEvaluation l E X n) :=
    (coefficientSequenceEvaluation_exact l E X n).2
  let : PreservesFiniteLimits (coefficientSequenceEvaluation l E Y n) :=
    (coefficientSequenceEvaluation_exact l E Y n).1
  let : PreservesFiniteColimits (coefficientSequenceEvaluation l E Y n) :=
    (coefficientSequenceEvaluation_exact l E Y n).2
  have h := localizePullSquare (ordinaryPullIso l E f)
    (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f)
    (ordinaryEvaluation l E f n)
    (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f n) (integralNativeOrdinaryPullEvaluation l E f n) M
  rw [derivedEvaluation_eq] at h
  dsimp only [integralNativePullIso, ordinaryPullIso, ProEtale.VaryingRing.evalG,
    Functor.mapDerivedCategorySquareIso, coefficientSequenceDerivedEvaluation,
    ProEtale.VaryingRing.ev, ProEtale.VaryingRing.G] at h ⊢
  exact h

end WeilConjectures.IntegralSystemRealization
