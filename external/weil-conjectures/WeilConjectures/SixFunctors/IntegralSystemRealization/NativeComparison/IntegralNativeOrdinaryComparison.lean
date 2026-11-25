/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectEvaluationSections
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Ordinary comparison of native inverse images -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v u₁ u₂ u₃ u₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralSystemRealization.NativeComparison
private theorem uniqueness_conjugate
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R R' : B ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (r : R ≅ R') :
    conjugateEquiv a b ((a.ofNatIsoRight r).leftAdjointUniq b).inv = r.hom := by
  let p := (a.ofNatIsoRight r).leftAdjointUniq b
  apply NatTrans.ext
  funext M
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, conjugateEquiv_counit]
  apply (cancel_epi (p.hom.app (R.obj M))).mp
  rw [Iso.hom_inv_id_app_assoc]
  have hn := p.hom.naturality (r.hom.app M)
  rw [← Category.assoc, ← hn, Category.assoc]
  have hc := Adjunction.leftAdjointUniq_hom_app_counit (a.ofNatIsoRight r) b M
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app] at hc
  rw [hc, ← L.map_comp_assoc, Iso.hom_inv_id_app, L.map_id, Category.id_comp]

/-- Transport a right-adjoint mate through isomorphisms of both adjunctions.
Source: Mathlib's mate and conjugate counit characterizations, followed by naturality.
(blueprint: lem-sf-adjoint-mates-transport). -/
theorem transport_mates
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L L' : A ⥤ B} {R R' : B ⥤ A} {K K' : C ⥤ D} {S S' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (a' : L' ⊣ R') (b : K ⊣ S) (b' : K' ⊣ S')
    (p : L ≅ L') (q : K ≅ K')
    (t : TwoSquare G L K H) (t' : TwoSquare G L' K' H)
    (ht : ∀ M, q.inv.app (G.obj M) ≫ t.app M = t'.app M ≫ H.map (p.inv.app M))
    (M : B) :
    (mateEquiv a b t).app M ≫ (conjugateEquiv b b' q.inv).app (H.obj M) =
      G.map ((conjugateEquiv a a' p.inv).app M) ≫ (mateEquiv a' b' t').app M := by
  apply (b'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit]
  rw [← Category.assoc]
  erw [q.inv.naturality]
  rw [Category.assoc, mateEquiv_counit, ← Category.assoc]
  erw [ht]
  rw [Category.assoc, ← H.map_comp]
  rw [mateEquiv_counit, ← Category.assoc]
  erw [t'.naturality]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← H.map_comp, conjugateEquiv_counit]

private theorem transport_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L L' : A ⥤ B} {R R' : B ⥤ A} {K K' : C ⥤ D} {S S' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (a' : L' ⊣ R') (b : K ⊣ S) (b' : K' ⊣ S')
    (p : L ≅ L') (q : K ≅ K') (r : R ≅ R') (s : S ≅ S')
    (hr : conjugateEquiv a a' p.inv = r.hom)
    (hs : conjugateEquiv b b' q.inv = s.hom)
    (e : L ⋙ H ≅ G ⋙ K) (e' : L' ⋙ H ≅ G ⋙ K')
    (β : R ⋙ G ≅ H ⋙ S) (β' : R' ⋙ G ≅ H ⋙ S')
    (hβ : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)) = β.hom)
    (hβ' : (mateEquiv a' b' (TwoSquare.mk _ _ _ _ e'.inv)) = β'.hom)
    (comm : ∀ M, β.hom.app M ≫ s.hom.app (H.obj M) =
      G.map (r.hom.app M) ≫ β'.hom.app M) :
    ∀ M, H.map (p.hom.app M) ≫ e'.hom.app M =
      e.hom.app M ≫ q.hom.app (G.obj M) := by
  let τ := Functor.isoWhiskerRight p H ≪≫ e' ≪≫ Functor.isoWhiskerLeft G q.symm
  have ht (M : A) : q.inv.app (G.obj M) ≫ τ.inv.app M =
      e'.inv.app M ≫ H.map (p.inv.app M) := by
    simp only [τ, Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hh : (mateEquiv a b (TwoSquare.mk _ _ _ _ τ.inv)) = β.hom := by
    apply NatTrans.ext
    funext M
    apply (cancel_mono (s.hom.app (H.obj M))).mp
    have hm := transport_mates a a' b b' p q
      (TwoSquare.mk _ _ _ _ τ.inv) (TwoSquare.mk _ _ _ _ e'.inv) ht M
    rw [hr, hs] at hm
    change (mateEquiv a b (TwoSquare.mk _ _ _ _ τ.inv)).app M ≫ _ =
      G.map (r.hom.app M) ≫
        (mateEquiv a' b' (TwoSquare.mk _ _ _ _ e'.inv)).app M at hm
    rw [hβ'] at hm
    rw [hm]
    exact (comm M).symm
  have hτ : τ = e := by
    apply Iso.ext_inv
    have hi := (mateEquiv a b).injective (show
      mateEquiv a b (TwoSquare.mk _ _ _ _ τ.inv) =
        mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv) by
      exact congrArg (TwoSquare.mk _ _ _ _) (hh.trans hβ.symm))
    exact hi
  intro M
  have h := congrArg (fun z ↦ z.hom.app M ≫ q.hom.app (G.obj M)) hτ
  simp only [τ, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app] at h
  erw [Category.comp_id] at h
  exact h

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] coefficientSequenceEvaluation_additiveInstance

attribute [local irreducible] Functor.ofSequence Functor.ofOpSequence
  constantSheaf presheafToSheaf MorphismProperty.Over.pullback
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition coefficientSequenceEvaluation
  integralCoefficientSheafTransition compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.evaluation SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

/-- Ordinary left-adjoint uniqueness for a specified whole-system direct comparison.
Source: the counit characterization of left-adjoint uniqueness.
(blueprint: lem-sf-integral-native-ordinary-comparison). -/
def ordinaryPullIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : pullbackTensorSequenceDirect l E f ≅
      ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f) :
    pullbackTensorSequenceInverse l E f ≅
      ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f :=
  ((pullbackTensorSequenceAdjunction l E f).ofNatIsoRight r).leftAdjointUniq
    (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f)

/-- The sequence inverse-evaluation comparison in intrinsic finite coordinates.
Source: the two normalized inverse-evaluation comparisons.
(blueprint: lem-sf-integral-native-ordinary-comparison). -/
def ordinaryEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorSequenceInverse l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f :=
  (pullbackTensorSequenceInverseEvaluation l E f n).symm ≪≫
    Functor.isoWhiskerLeft _ (pullbackTensorLevelIntrinsic l E f n)

private theorem intrinsicComparison_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorLevelIntrinsic l E f n =
      (coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).leftAdjointUniq
        (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))) := by
  apply (pullbackTensorLevelIntrinsic_existsUnique l E f n).unique
    (pullbackTensorLevelIntrinsic_existsUnique l E f n).exists.choose_spec
  intro M U x
  exact congrArg (fun a ↦ a.val.app (op U) x)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))) M)

/-- The ordinary native finite pullback in intrinsic constant-module coordinates.
Source: Mathlib left-adjoint uniqueness for the fixed direct-image coordinate change.
(blueprint: lem-sf-integral-native-ordinary-comparison). -/
@[irreducible] def nativeFinitePullIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) f ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f :=
  ((proEtaleRingModuleAdjunction f
    (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) Y n)
    (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) X n)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) f)).ofNatIsoRight
      (compactSupportDirectModel f (finiteCoefficientRing l E (n + 1)))).leftAdjointUniq
        (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))

/-- Ordinary left-adjoint uniqueness is conjugate to the fixed direct-image coordinate change.
Source: Mathlib adjoint uniqueness and the counit equation.
(blueprint: lem-sf-integral-native-ordinary-comparison). -/
theorem nativeFinitePullIso_conjugate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    conjugateEquiv
      (proEtaleRingModuleAdjunction f
        (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) Y n)
        (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) X n)
        (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) f))
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
      (nativeFinitePullIso l E f n).inv =
        (compactSupportDirectModel f (finiteCoefficientRing l E (n + 1))).hom := by
  unfold nativeFinitePullIso
  exact uniqueness_conjugate _ _ _

private theorem ordinary_mate_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (pullbackTensorSequenceAdjunction l E f)
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
      (TwoSquare.mk _ _ _ _ (ordinaryEvaluation l E f n).inv)) =
        (pullbackTensorSequenceDirectEvaluation l E f n).hom := by
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
  have hh := congrArg (mateEquiv a b) he
  rw [Equiv.apply_symm_apply] at hh
  exact (hh).symm

/-- A normalized ordinary direct comparison determines the inverse-evaluation square.
Source: the native and sequence unit normalizations and naturality of adjunction mates.
Proof: transpose both normalized evaluation squares, transport their mates through
ordinary left-adjoint uniqueness, and cancel the finite direct coordinate isomorphism.
(blueprint: lem-sf-integral-native-ordinary-comparison). -/
theorem ordinary_pull_square {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r : pullbackTensorSequenceDirect l E f ≅
      ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f)
    (hr : ∀ N, (coefficientSequenceEvaluation l E Y n).map (r.hom.app N) ≫
      (compactSupportOrdinaryDirectEvaluation l E f n).hom.app N =
        (pullbackTensorSequenceDirectEvaluation l E f n).hom.app N)
    (M : coefficientSequenceModules l E Y) :
    (coefficientSequenceEvaluation l E X n).map
      ((ordinaryPullIso l E f r).hom.app M) ≫
      (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app M =
    (ordinaryEvaluation l E f n).hom.app M ≫
      (nativeFinitePullIso l E f n).inv.app
        ((coefficientSequenceEvaluation l E Y n).obj M) := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let a := pullbackTensorSequenceAdjunction l E f
  let a' := ProEtale.VaryingRing.moduleAdj R q f
  let b := sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))
  let b' := proEtaleRingModuleAdjunction f
    (ProEtale.VaryingRing.coefficients R Y n) (ProEtale.VaryingRing.coefficients R X n)
    (ProEtale.StrictTower.constantRingIso (R n) f)
  let s := compactSupportDirectModel f (finiteCoefficientRing l E (n + 1))
  have hs : conjugateIsoEquiv b' b (nativeFinitePullIso l E f n).symm = s := by
    apply Iso.ext
    exact nativeFinitePullIso_conjugate l E f n
  have hs' : conjugateEquiv b b' (nativeFinitePullIso l E f n).hom = s.inv :=
    congrArg Iso.inv hs
  have hm : (mateEquiv a' b'
      (TwoSquare.mk _ _ _ _ (ProEtale.VaryingRing.moduleEvalG R q f n).inv)) =
        (ProEtale.VaryingRing.moduleEvalP R q f n).hom := by
    have hi := ProEtale.VaryingRing.inverseMateEqOfUnit a' b'
      (ProEtale.VaryingRing.eval R q Y n) (ProEtale.VaryingRing.eval R q X n)
      (ProEtale.VaryingRing.moduleEvalP R q f n).hom
      (ProEtale.VaryingRing.moduleEvalG R q f n)
      (ProEtale.VaryingRing.moduleEvalG_existsUnique R q f n).choose_spec.1
    have hi' : (mateEquiv a' b').symm
        (TwoSquare.mk _ _ _ _ (ProEtale.VaryingRing.moduleEvalP R q f n).hom) =
      TwoSquare.mk _ _ _ _ (ProEtale.VaryingRing.moduleEvalG R q f n).inv := by
      refine NatTrans.ext (funext fun N ↦ ?_)
      exact congr_app hi N
    have h := congrArg (mateEquiv a' b') hi'
    rw [Equiv.apply_symm_apply] at h
    exact (h).symm
  apply transport_square
    (G := coefficientSequenceEvaluation l E Y n)
    (H := coefficientSequenceEvaluation l E X n) a a' b b'
    (ordinaryPullIso l E f r)
    (nativeFinitePullIso l E f n).symm r s.symm
    (uniqueness_conjugate a a' r) hs'
    (ordinaryEvaluation l E f n) (ProEtale.VaryingRing.moduleEvalG R q f n)
    (pullbackTensorSequenceDirectEvaluation l E f n)
    (ProEtale.VaryingRing.moduleEvalP R q f n)
    (ordinary_mate_eq l E f n) hm ?_ M
  intro N
  apply (cancel_mono (s.hom.app ((coefficientSequenceEvaluation l E X n).obj N))).mp
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  exact (hr N).symm

end WeilConjectures.IntegralSystemRealization.NativeComparison
