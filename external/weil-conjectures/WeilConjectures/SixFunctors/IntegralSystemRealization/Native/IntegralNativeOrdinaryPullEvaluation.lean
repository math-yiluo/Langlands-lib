/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeDirectComparison
import all WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralDirectEvaluationMateInvertible
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectEvaluationSections

/-! # Ordinary native pullback evaluation -/

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

private theorem compareOpenMates
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L L' : A ⥤ B} {R R' : B ⥤ A} {l l' : C ⥤ D} {r r' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (c : l ⊣ r) (d : l' ⊣ r')
    {E : A ⥤ C} {H : B ⥤ D}
    (e : R ≅ R') (q : r' ≅ r) (k : l' ≅ l)
    (δ : R ⋙ E ⟶ H ⋙ r) (δ' : R' ⋙ E ⟶ H ⋙ r')
    (v : L' ⋙ H ≅ E ⋙ l') (w : L ⋙ H ≅ E ⋙ l)
    (hv : (mateEquiv b d).symm δ' = v.inv)
    (hw : (mateEquiv a c).symm δ = w.inv)
    (hq : ∀ N, d.unit.app N ≫ q.hom.app (l'.obj N) ≫ r.map (k.hom.app N) =
      c.unit.app N)
    (hs : ∀ N, E.map (e.hom.app N) ≫ δ'.app N ≫ q.hom.app (H.obj N) = δ.app N)
    (M : A) :
    H.map (((a.ofNatIsoRight e).leftAdjointUniq b).hom.app M) ≫
      v.hom.app M ≫ k.hom.app (E.obj M) = w.hom.app M := by
  let α := (a.ofNatIsoRight e).leftAdjointUniq b
  have hα : a.unit.app M ≫ e.hom.app (L.obj M) =
      b.unit.app M ≫ R'.map (α.inv.app M) := by
    exact (b.unit_leftAdjointUniq_hom_app (a.ofNatIsoRight e) M).symm
  have hq' : c.unit.app (E.obj M) ≫ r.map (k.inv.app (E.obj M)) =
      d.unit.app (E.obj M) ≫ q.hom.app (l'.obj (E.obj M)) := by
    rw [← hq (E.obj M)]
    simp only [Category.assoc, ← r.map_comp, Iso.hom_inv_id_app,
      r.map_id, Category.comp_id]
  have hv' := unit_mateEquiv_symm b d δ' M
  rw [hv] at hv'
  have hw' := unit_mateEquiv_symm a c δ M
  rw [hw] at hw'
  have hi : k.inv.app (E.obj M) ≫ v.inv.app M ≫ H.map (α.inv.app M) =
      w.inv.app M := by
    apply (c.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [hq']
    simp only [Category.assoc]
    have hn := q.hom.naturality (v.inv.app M)
    rw [← reassoc_of% hn, ← reassoc_of% hv']
    have hn' := δ'.naturality (α.inv.app M)
    dsimp only [Functor.comp_map] at hn'
    rw [← (q.hom.naturality (H.map (α.inv.app M))),
      ← reassoc_of% hn', ← E.map_comp_assoc, ← hα, E.map_comp_assoc,
      hs (L.obj M)]
    exact hw'
  have he : H.mapIso (α.app M) ≪≫ v.app M ≪≫ k.app (E.obj M) = w.app M :=
    Iso.ext_inv (by
      simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hi)
  exact congrArg Iso.hom he

private theorem ordinaryDirectEvaluation_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Functor.isoWhiskerRight (integralNativeOrdinaryDirectIso l E f)
        (coefficientSequenceEvaluation l E Y n) ≪≫
      compactSupportOrdinaryDirectEvaluation l E f n =
        pullbackTensorSequenceDirectEvaluation l E f n := by
  apply (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).unique
  · intro M V x
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    have h := compactSupportOrdinaryDirectEvaluation_sections l E f n M (op V)
      (((coefficientSequenceEvaluation l E Y n).map
        ((integralNativeOrdinaryDirectIso l E f).hom.app M)).val.app (op V) x)
    exact h.trans (by rfl)
  · exact (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec

private theorem nativePullMate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f)
      (proEtaleRingModuleAdjunction f
        (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) Y n)
        (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) X n)
        (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) f))).symm
      (ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom =
      (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).inv := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  apply ((proEtaleRingModuleAdjunction f
    (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) Y n)
    (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) X n)
    (ProEtale.StrictTower.constantRingIso
      (compactSupportSystemLevel l E n) f)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]
  erw [← unit_mateEquiv_symm]
  rw [Adjunction.homEquiv_unit]
  apply (cancel_mono ((ProEtale.StrictTower.moduleDirectImage
    (compactSupportSystemLevel l E n) f).map
      ((ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app M))).1
  change _ = (proEtaleRingModuleAdjunction f
    (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) Y n)
    (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) X n)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) f)).unit.app
      ((ProEtale.VaryingRing.eval (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) Y n).obj M) ≫
    (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).map
      ((ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).inv.app M) ≫
    (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).map
      ((ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app M)
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).map_id,
    Category.comp_id]
  simp only [Category.assoc]
  exact (ProEtale.VaryingRing.moduleEvalG_existsUnique (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f n).choose_spec.1 M

private theorem originalPullMate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (pullbackTensorSequenceAdjunction l E f)
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))).symm
      (pullbackTensorSequenceDirectEvaluation l E f n).hom =
        (ordinaryEvaluation l E f n).inv := by
  let a := pullbackTensorSequenceAdjunction l E f
  let b := sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))
  let b₀ := coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
  let β := pullbackTensorSequenceDirectEvaluation l E f n
  let R := proEtaleConstantModuleDirectImage f (finiteCoefficientRing l E (n + 1))
  have he : (mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β.hom) =
      TwoSquare.mk _ _ _ _ (ordinaryEvaluation l E f n).inv := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    apply (b.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit]
    erw [← unit_mateEquiv_symm]
    dsimp only [ordinaryEvaluation, Iso.trans_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_inv]
    rw [intrinsicComparison_eq, Adjunction.homEquiv_unit]
    let Z := (coefficientSequenceEvaluation l E Y n).obj M
    have hu : b.unit.app Z ≫ R.map ((b₀.leftAdjointUniq b).inv.app Z) =
        b₀.unit.app Z := by
      have h₀ : b₀.unit.app Z ≫ R.map ((b₀.leftAdjointUniq b).hom.app Z) =
          b.unit.app Z := Adjunction.unit_leftAdjointUniq_hom_app b₀ b Z
      have h := congrArg
        (fun z ↦ z ≫ R.map ((b₀.leftAdjointUniq b).inv.app Z)) h₀
      have h₁ := h.symm
      simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at h₁
      erw [R.map_id, Category.comp_id] at h₁
      exact h₁
    rw [Functor.map_comp, ← Category.assoc, hu]
    exact ((pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose_spec
      M).symm
  exact he

private theorem finitePull_unit (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (proEtaleConstantRingAdjunction A f).unit.app M ≫
      (compactSupportDirectModel f A).hom.app ((proEtaleConstantRingPullback A f).obj M) ≫
      (proEtaleConstantModuleDirectImage f A).map
        ((openSquarePullbackModel A f).hom.app M) =
      (sfIntrinsicConstantModuleAdjunction f A).unit.app M := by
  ext V x
  exact (openSquarePullbackModel_existsUnique A f).exists.choose_spec M V.unop x

/-- The ordinary native pullback comparison preserves the normalized finite evaluation.
Source: Stacks 03D2 and 0941; blueprint fix-prop-coherence, coefficient comparisons.
(blueprint: lem-sf-integral-native-ordinary-pull-evaluation).

Proof: the ordinary direct-image comparison and native direct evaluation are identity
on sections. Uniqueness identifies their composite with the prescribed direct evaluation.
The native and intrinsic finite pullback coordinates preserve their adjunction units.
Taking mates and using left-adjoint uniqueness therefore gives the displayed pullback
square. This works for every scheme map and every module, including zero and n = 0. -/
theorem integralNativeOrdinaryPullEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E Y) :
    (coefficientSequenceEvaluation l E X n).map
      ((((pullbackTensorSequenceAdjunction l E f).ofNatIsoRight
      (integralNativeOrdinaryDirectIso l E f)).leftAdjointUniq
        (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f)).hom.app M) ≫
      (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app M ≫
      (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f).hom.app
        ((coefficientSequenceEvaluation l E Y n).obj M) =
      ((pullbackTensorSequenceInverseEvaluation l E f n).symm ≪≫
        Functor.isoWhiskerLeft _ (pullbackTensorLevelIntrinsic l E f n)).hom.app M := by
  apply compareOpenMates
    (E := coefficientSequenceEvaluation l E Y n)
    (H := coefficientSequenceEvaluation l E X n)
    (pullbackTensorSequenceAdjunction l E f)
    (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f)
    (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
    (proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (n + 1)) f)
    (integralNativeOrdinaryDirectIso l E f)
    (compactSupportDirectModel f (Padic.coefficientExtensionRing l E (n + 1)))
    (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f)
    (pullbackTensorSequenceDirectEvaluation l E f n).hom
    (ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f n).hom
    (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f n) (ordinaryEvaluation l E f n)
    (nativePullMate l E f n) (originalPullMate l E f n)
    (finitePull_unit (Padic.coefficientExtensionRing l E (n + 1)) f) ?_ M
  intro N
  change (Functor.isoWhiskerRight (integralNativeOrdinaryDirectIso l E f)
      (coefficientSequenceEvaluation l E Y n) ≪≫
        compactSupportOrdinaryDirectEvaluation l E f n).hom.app N = _
  rw [ordinaryDirectEvaluation_eq]

end WeilConjectures.IntegralSystemRealization
