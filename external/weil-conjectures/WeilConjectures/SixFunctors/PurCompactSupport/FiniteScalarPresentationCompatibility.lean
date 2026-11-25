/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import all WeilConjectures.SmoothPurity.Compact.CompactSupportOpenScalarRestriction
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarDirectNormalization
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence

/-! # Presentation of the finite proper/open scalar comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

private theorem rightDerived_refl
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    Functor.rightDerivedFunctorNatIso (Iso.refl F) = Iso.refl F.rightDerivedFunctor := by
  apply Iso.ext
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]

private theorem derivedSquare_equalityTransport
    {A B Ap Bp : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
    [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} Ap] [HasDerivedCategory.{w} Bp]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
    (F F' : A ⥤ B) (G G' : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [x.Additive] [y.Additive]
    [PreservesFiniteLimits x] [PreservesFiniteColimits x]
    [PreservesFiniteLimits y] [PreservesFiniteColimits y]
    (hf : F = F') (hg : G = G')
    (c : F ⋙ y ≅ x ⋙ G) (c' : F' ⋙ y ≅ x ⋙ G')
    (hc : Functor.isoWhiskerRight (eqToIso hf).symm y ≪≫ c ≪≫
      Functor.isoWhiskerLeft x (eqToIso hg) = c')
    (d : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (d' : F'.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G'.rightDerivedFunctor)
    (hd : ExactDerivedSquare.unitNormalized F G x y
      x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom d.hom)
    (hd' : ExactDerivedSquare.unitNormalized F' G' x y
      x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c'.hom d'.hom) :
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso (eqToIso hf)).symm
        y.mapDerivedCategory ≪≫ d ≪≫
      Functor.isoWhiskerLeft x.mapDerivedCategory
        (Functor.rightDerivedFunctorNatIso (eqToIso hg)) = d' := by
  subst F'
  subst G'
  simp only [eqToIso_refl, Iso.refl_symm, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_trans, Iso.trans_refl] at hc
  subst c'
  simp only [eqToIso_refl, rightDerived_refl, Iso.refl_symm,
    Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl,
    Iso.refl_trans, Iso.trans_refl]
  exact ExactDerivedSquare.square_unique F G x y c d d' hd hd'

attribute [local implicit_reducible] finite sfAmbientCompactSupportCandidate
  sfIntrinsicCompactSupport proEtaleConstantRingMap pbcDerivedRestrict
attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

private theorem pushforwardCongr_eqToIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) RingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    {ρ σ : R ⟶ ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X)).obj S} (h : ρ = σ) :
    eqToIso (congrArg (fun q ↦ SheafOfModules.pushforward.{u + 1} q) h) =
      SheafOfModules.pushforwardCongr h := by
  subst σ
  ext M V x
  rfl

private theorem unit_leftAdjointUniq_ofNatIsoRight
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G')
    (e : G ≅ G') (c : F ≅ F') (hc : c = (a.ofNatIsoRight e).leftAdjointUniq b) (M : C) :
    a.unit.app M ≫ e.hom.app (F.obj M) ≫ G'.map (c.hom.app M) = b.unit.app M := by
  subst c
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] using
    Adjunction.unit_leftAdjointUniq_hom_app (a.ofNatIsoRight e) b M

-- Keep the pullback comparison named while transporting the direct-image unit.
private theorem finitePullback_native
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finitePullbackIso l E n f =
      openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := finite l E (n + 1) (Nat.succ_pos n)
  have hmap : proEtaleRingDirectImageMap f (R.ring Y) (R.ring X) (R.pull f) =
      proEtaleCoefficientDirectImageMap f A :=
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hm := congrArg (fun z ↦
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map z) hmap
  have he : eqToIso (finiteDirectImage_eq l E n f) =
      SheafOfModules.pushforwardCongr hm := pushforwardCongr_eqToIso f hm
  apply (openSquarePullbackModel_existsUnique A f).unique
  · intro M V x
    have h := unit_leftAdjointUniq_ofNatIsoRight
      (proEtaleRingModuleAdjunction f (R.ring Y) (R.ring X) (R.pull f))
      (sfIntrinsicConstantModuleAdjunction f A) (eqToIso (finiteDirectImage_eq l E n f))
      (finitePullbackIso l E n f) rfl M
    rw [he] at h
    have hv := congrArg (fun z ↦ z.val.app (Opposite.op V) x) h
    exact hv
  · exact (openSquarePullbackModel_existsUnique A f).exists.choose_spec

private theorem finiteOpen_native
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    finiteOpenIso l E n j =
      compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)) := by
  rw [finiteOpenIso, finitePullback_native]
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := finite l E (n + 1) (Nat.succ_pos n)
  let e := openSquarePullbackModel A j
  let adj := openAdjunction R j
  let adj' := sfIntrinsicOpenAdjunction A j
  let z := (adj.ofNatIsoRight e).leftAdjointUniq adj'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adj.homEquiv M _).injective
  change adj.unit.app M ≫ (proEtaleConstantRingPullback A j).map (z.hom.app M) =
    adj.unit.app M ≫ (proEtaleConstantRingPullback A j).map
      ((compactSupportOpenModel j A).hom.app M)
  apply (cancel_mono (e.hom.app ((sfIntrinsicExtensionByZero j A).obj M))).1
  have h := Adjunction.unit_leftAdjointUniq_hom_app (adj.ofNatIsoRight e) adj' M
  have hn := e.hom.naturality (z.hom.app M)
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at h
  rw [Category.assoc, hn, ← Category.assoc]
  rw [h]
  have h' := Adjunction.unit_leftAdjointUniq_hom_app
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1, u} A) j)
    (adj'.ofNatIsoRight e.symm) M
  change adj.unit.app M ≫ (proEtaleConstantRingPullback A j).map
    ((compactSupportOpenModel j A).hom.app M) = _ at h'
  rw [h']
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

private theorem constantPush_eq
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingModuleDirectImage f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) =
      proEtaleConstantModuleDirectImage f A := by
  have h : proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) =
      proEtaleCoefficientDirectImageMap f A :=
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  unfold proEtaleRingModuleDirectImage proEtaleConstantModuleDirectImage
  rw [h]

private theorem constantPush_iso_sections
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Y.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange f).op.obj V)) :
    ((eqToIso (constantPush_eq A f)).hom.app M).val.app V x = x := by
  have h : proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) =
      proEtaleCoefficientDirectImageMap f A :=
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hm := congrArg (fun z ↦
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map z) h
  have he : eqToIso (constantPush_eq A f) = SheafOfModules.pushforwardCongr hm :=
    pushforwardCongr_eqToIso f hm
  rw [he]
  rfl

private theorem constantPush_iso_inv_sections
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Y.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange f).op.obj V)) :
    ((eqToIso (constantPush_eq A f)).inv.app M).val.app V x = x := by
  have h := congrArg (fun z ↦ z.val.app V x)
    ((eqToIso (constantPush_eq A f)).inv_hom_id_app M)
  change ((eqToIso (constantPush_eq A f)).hom.app M).val.app V
    (((eqToIso (constantPush_eq A f)).inv.app M).val.app V x) = x at h
  rw [constantPush_iso_sections] at h
  exact h

private theorem constantPush_scalar
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B) :
    Functor.isoWhiskerRight (eqToIso (constantPush_eq B f)).symm
        (proEtaleCoefficientRestrictScalars Y φ) ≪≫
      proEtaleRingRestrictionDirectImage f
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
        (coefficientInverseImage_naturality f φ) ≪≫
      Functor.isoWhiskerLeft (proEtaleCoefficientRestrictScalars X φ)
        (eqToIso (constantPush_eq A f)) = proEtaleCoefficientDirectImageComparison f φ := by
  apply (proEtaleCoefficientDirectImageComparison_existsUnique f φ).unique
  · intro M V x
    change ((eqToIso (constantPush_eq A f)).hom.app _).val.app V
      (((proEtaleRingRestrictionDirectImage f
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
        (coefficientInverseImage_naturality f φ)).hom.app M).val.app V
          (((eqToIso (constantPush_eq B f)).inv.app M).val.app V x)) = x
    rw [constantPush_iso_sections]
    erw [(proEtaleRingRestrictionDirectImage_existsUnique f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (coefficientInverseImage_naturality f φ)).choose_spec.1]
    exact constantPush_iso_inv_sections B f M V x
  · exact (proEtaleCoefficientDirectImageComparison_existsUnique f φ).choose_spec.1

private theorem constantDerivedPush_scalar
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B) :
    Functor.isoWhiskerRight
        (Functor.rightDerivedFunctorNatIso (eqToIso (constantPush_eq B f))).symm
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ≪≫
      proEtaleRingRestrictionDerivedDirectImage f
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
        (coefficientInverseImage_naturality f φ) ≪≫
      Functor.isoWhiskerLeft (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory
        (Functor.rightDerivedFunctorNatIso (eqToIso (constantPush_eq A f))) =
      (sfDerivedImageRestriction f φ).symm := by
  apply derivedSquare_equalityTransport _ _ _ _
    (proEtaleCoefficientRestrictScalars X φ) (proEtaleCoefficientRestrictScalars Y φ)
    (constantPush_eq B f) (constantPush_eq A f) _ _ (constantPush_scalar f φ)
  · exact (proEtaleRingRestrictionDerivedDirectImage_existsUnique f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (coefficientInverseImage_naturality f φ)).choose_spec.1
  · exact compactSupportScalarDirectNormalization f φ

private theorem finiteScalarPull_native
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (a : Change (finite l E (n + 1) (Nat.succ_pos n))
      (finite l L (m + 1) (Nat.succ_pos m)))
    (ha : ∀ T, a.map T = proEtaleConstantRingMap (T := T) φ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    compactSupportScalarPullback f φ =
      proEtaleRingRestrictionPullbackInv f
        ((finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((finite l L (m + 1) (Nat.succ_pos m)).ring Y)
        ((finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((finite l L (m + 1) (Nat.succ_pos m)).ring X)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
        ((finite l E (n + 1) (Nat.succ_pos n)).pull f)
        ((finite l L (m + 1) (Nat.succ_pos m)).pull f)
        (by simpa only [ha] using a.square f) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := Padic.coefficientExtensionRing l L (m + 1)
  let cA := proEtaleConstantRingComparison f A
  let cB := proEtaleConstantRingComparison f B
  let aY := proEtaleConstantRingMap (T := Y) φ
  let aX := proEtaleConstantRingMap (T := X) φ
  let comm := coefficientInverseImage_naturality f φ
  let d := proEtaleRingRestrictionDirectImage f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B) aY aX cA cB comm
  have hd : compactSupportScalarDirectImage f φ = d := by
    apply (proEtaleRingRestrictionDirectImage_existsUnique f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B) aY aX cA cB comm).unique
    · exact compactSupportScalarDirectImage_sections f φ
    · exact (proEtaleRingRestrictionDirectImage_existsUnique f
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B) aY aX cA cB comm).choose_spec.1
  apply (mateEquiv (proEtaleConstantRingAdjunction B f)
    (proEtaleConstantRingAdjunction A f)).injective
  change (mateEquiv _ _ ((mateEquiv _ _).symm
    (compactSupportScalarDirectImage f φ).hom)) = _
  exact (Equiv.apply_symm_apply _ _).trans
    ((congrArg (fun e ↦ TwoSquare.mk _ _ _ _ e.hom) hd).trans
      (congrArg (fun t ↦ TwoSquare.mk _ _ _ _ t)
        (restrictionPullback_mate f _ _ _ _ aY aX cA cB comm)).symm)

private theorem finiteScalarOpen_native
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (a : Change (finite l E (n + 1) (Nat.succ_pos n))
      (finite l L (m + 1) (Nat.succ_pos m)))
    (ha : ∀ T, a.map T = proEtaleConstantRingMap (T := T) φ)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    HEq (openRestrictionMap a j) (scalarJ j φ).hom := by
  cases a with
  | mk amap asquare =>
    have hm : amap = fun T ↦ proEtaleConstantRingMap (T := T) φ := funext ha
    subst amap
    apply heq_of_eq
    apply NatTrans.ext
    funext M
    apply ((openAdjunction (finite l E (n + 1) (Nat.succ_pos n)) j).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit]
    let d := compactSupportScalarPullback j φ
    let : IsIso d := compactSupportScalarPullback_isIso j φ
    apply (cancel_mono (d.app
      ((openExtension (finite l L (m + 1) (Nat.succ_pos m)) j).obj M))).1
    have h := unit_mateEquiv_symm
      (openAdjunction (finite l L (m + 1) (Nat.succ_pos m)) j)
      (openAdjunction (finite l E (n + 1) (Nat.succ_pos n)) j)
      (TwoSquare.mk _ _ _ _ (inv d)) M
    simp only [Category.assoc]
    unfold openRestrictionMap
    simp only [← finiteScalarPull_native l E L n m φ ⟨_, asquare⟩ (fun _ ↦ rfl) j]
    erw [← reassoc_of% h]
    simp only [← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
    exact (scalarJ_unit j φ M).symm

section Generic
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]

private theorem square_precompose
    (U : A ⥤ B) (V V' : B ⥤ D) (E : A ⥤ C) (F : C ⥤ D)
    [U.Additive] [V.Additive] [V'.Additive] [E.Additive] [F.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : V ≅ V') (α : U ⋙ V' ≅ E ⋙ F) :
    Functor.mapDerivedCategorySquareIso (Functor.isoWhiskerLeft U e ≪≫ α) =
      Functor.isoWhiskerLeft U.mapDerivedCategory (Functor.mapDerivedCategoryNatIso e) ≪≫
        Functor.mapDerivedCategorySquareIso α := by
  have he := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft U e
  apply Iso.ext
  apply (cancel_epi (Functor.mapDerivedCategoryCompIso U V).inv).mp
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_trans, Category.assoc,
    Iso.inv_hom_id_assoc, Functor.isoWhiskerLeft_hom]
  rw [← reassoc_of% he, Iso.inv_hom_id_assoc]

private theorem square_postcompose_right
    (U : A ⥤ B) (V : B ⥤ D) (E E' : A ⥤ C) (F : C ⥤ D)
    [U.Additive] [V.Additive] [E.Additive] [E'.Additive] [F.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (α : U ⋙ V ≅ E ⋙ F) (e : E ≅ E') :
    Functor.mapDerivedCategorySquareIso (α ≪≫ Functor.isoWhiskerRight e F) =
      Functor.mapDerivedCategorySquareIso α ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e) F.mapDerivedCategory := by
  apply Iso.ext
  ext M
  have h := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_trans,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
  rw [h]
end Generic
private theorem pastePresentationSquares
    {A B C Ap Bp Cp : Type*}
    [Category A] [Category B] [Category C]
    [Category Ap] [Category Bp] [Category Cp]
    (x : Ap ⥤ A) (z : Bp ⥤ B) (y : Cp ⥤ C)
    (J K : A ⥤ B) (J' K' : Ap ⥤ Bp)
    (P Q : B ⥤ C) (P' Q' : Bp ⥤ Cp)
    (eJ : J ≅ K) (eJ' : J' ≅ K') (eP : P ≅ Q) (eP' : P' ≅ Q')
    (j : x ⋙ J ≅ J' ⋙ z) (jN : x ⋙ K ≅ K' ⋙ z)
    (p : z ⋙ P ≅ P' ⋙ y) (pN : z ⋙ Q ≅ Q' ⋙ y)
    (hj : j = Functor.isoWhiskerLeft x eJ ≪≫ jN ≪≫
      Functor.isoWhiskerRight eJ'.symm z)
    (hp : p = Functor.isoWhiskerLeft z eP ≪≫ pN ≪≫
      Functor.isoWhiskerRight eP'.symm y) :
    Functor.isoWhiskerRight j P ≪≫ Functor.isoWhiskerLeft J' p =
      Functor.isoWhiskerLeft x
          (Functor.isoWhiskerRight eJ P ≪≫ Functor.isoWhiskerLeft K eP) ≪≫
        (Functor.isoWhiskerRight jN Q ≪≫ Functor.isoWhiskerLeft K' pN) ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerRight eJ' P' ≪≫ Functor.isoWhiskerLeft K' eP').symm y := by
  rw [hj, hp]
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (eP.hom.naturality (z.map (eJ'.inv.app M)))]
  have hn := pN.hom.naturality (eJ'.inv.app M)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% (eP.hom.naturality (jN.hom.app M))]
  rw [← y.map_comp]
  rw [eP'.inv.naturality, y.map_comp]

private theorem invertConjugation {C : Type*} [Category C]
    {W X Y Z : C} (a : W ≅ X) (p : X ≅ Y) (b : Y ≅ Z) (q : W ≅ Z)
    (h : a ≪≫ p ≪≫ b = q) : p.symm = b ≪≫ q.symm ≪≫ a := by
  have hi := congrArg Iso.inv h
  simp only [Iso.trans_inv, Category.assoc] at hi
  apply Iso.ext
  change p.inv = b.hom ≫ q.inv ≫ a.hom
  calc
    p.inv = b.hom ≫ (b.inv ≫ p.inv ≫ a.inv) ≫ a.hom := by simp
    _ = b.hom ≫ q.inv ≫ a.hom := by rw [hi]

private theorem finiteDerivedOpen_native
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (a : Change (finite l E (n + 1) (Nat.succ_pos n))
      (finite l L (m + 1) (Nat.succ_pos m)))
    (ha : ∀ T, a.map T = proEtaleConstantRingMap (T := T) φ)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    letI := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).1
    letI := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).2.1
    letI := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).2.2
    letI := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l L (m + 1))).1
    letI := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l L (m + 1))).2.1
    letI := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l L (m + 1))).2.2
    HEq (openRestriction a j)
      (Functor.isoWhiskerLeft (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso (finiteOpenIso l E n j)) ≪≫
        Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ) ≪≫
        Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso (finiteOpenIso l L m j)).symm
          (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory) := by
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).1
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l L (m + 1))).1
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l L (m + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l L (m + 1))).2.2
  cases a with
  | mk amap asquare =>
    have hm : amap = fun T ↦ proEtaleConstantRingMap (T := T) φ := funext ha
    subst amap
    let b : Change (finite l E (n + 1) (Nat.succ_pos n))
        (finite l L (m + 1) (Nat.succ_pos m)) := ⟨_, asquare⟩
    have hi : asIso (openRestrictionMap b j) = scalarJ j φ := by
      apply Iso.ext
      exact eq_of_heq (finiteScalarOpen_native l E L n m φ ⟨_, asquare⟩ (fun _ ↦ rfl) j)
    apply heq_of_eq
    unfold openRestriction
    rw [hi]
    unfold scalarJ
    erw [square_precompose, square_postcompose_right]
    apply Iso.ext
    simp only [finiteOpen_native, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom,
      Functor.mapDerivedCategoryNatIso_symm, proEtaleCoefficientRestrictScalars,
      proEtaleConstantRingMap]

-- Pasting compares the chosen derived proper/open functor models.
private theorem finiteRestriction_native
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (a : Change (finite l E (n + 1) (Nat.succ_pos n))
      (finite l L (m + 1) (Nat.succ_pos m)))
    (ha : ∀ T, a.map T = proEtaleConstantRingMap (T := T) φ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    letI := (sfIntrinsicExtensionByZero_exact c.i
      (Padic.coefficientExtensionRing l E (n + 1))).1
    letI := (sfIntrinsicExtensionByZero_exact c.i
      (Padic.coefficientExtensionRing l E (n + 1))).2.1
    letI := (sfIntrinsicExtensionByZero_exact c.i
      (Padic.coefficientExtensionRing l E (n + 1))).2.2
    letI := (sfIntrinsicExtensionByZero_exact c.i
      (Padic.coefficientExtensionRing l L (m + 1))).1
    letI := (sfIntrinsicExtensionByZero_exact c.i
      (Padic.coefficientExtensionRing l L (m + 1))).2.1
    letI := (sfIntrinsicExtensionByZero_exact c.i
      (Padic.coefficientExtensionRing l L (m + 1))).2.2
    letI := (proEtaleConstantModuleDirectImage_additive_leftExact c.g
      (Padic.coefficientExtensionRing l E (n + 1))).1
    letI := (proEtaleConstantModuleDirectImage_additive_leftExact c.g
      (Padic.coefficientExtensionRing l L (m + 1))).1
    HEq (restriction a c)
      (Functor.isoWhiskerLeft (pbcDerivedRestrict (proEtaleConstantRingMap (T := X) φ))
          (finiteImageIso l E n c) ≪≫ sfCompactSupportRestriction c φ ≪≫
        Functor.isoWhiskerRight (finiteImageIso l L m c).symm
          (pbcDerivedRestrict (proEtaleConstantRingMap (T := Y) φ))) := by
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).1
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l L (m + 1))).1
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l L (m + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l L (m + 1))).2.2
  have := (proEtaleConstantModuleDirectImage_additive_leftExact c.g
    (Padic.coefficientExtensionRing l E (n + 1))).1
  have := (proEtaleConstantModuleDirectImage_additive_leftExact c.g
    (Padic.coefficientExtensionRing l L (m + 1))).1
  cases a with
  | mk amap asquare =>
    have hm : amap = fun T ↦ proEtaleConstantRingMap (T := T) φ := funext ha
    subst amap
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := Padic.coefficientExtensionRing l L (m + 1)
    let RA := finite l E (n + 1) (Nat.succ_pos n)
    let RB := finite l L (m + 1) (Nat.succ_pos m)
    let b : Change RA RB := ⟨fun T ↦ proEtaleConstantRingMap (T := T) φ, asquare⟩
    let x : proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory X A :=
      pbcDerivedRestrict (proEtaleConstantRingMap (T := X) φ)
    let z : proEtaleDerivedCategory c.Z B ⥤ proEtaleDerivedCategory c.Z A :=
      pbcDerivedRestrict (proEtaleConstantRingMap (T := c.Z) φ)
    let y : proEtaleDerivedCategory Y B ⥤ proEtaleDerivedCategory Y A :=
      pbcDerivedRestrict (proEtaleConstantRingMap (T := Y) φ)
    let JA : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory c.Z A :=
      (openExtension RA c.i).mapDerivedCategory
    let KA : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory c.Z A :=
      (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    let JB : proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory c.Z B :=
      (openExtension RB c.i).mapDerivedCategory
    let KB : proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory c.Z B :=
      (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
    let PA : proEtaleDerivedCategory c.Z A ⥤ proEtaleDerivedCategory Y A :=
      proEtaleRingDerivedDirectImage c.g (RA.ring Y) (RA.ring c.Z) (RA.pull c.g)
    let QA : proEtaleDerivedCategory c.Z A ⥤ proEtaleDerivedCategory Y A :=
      proEtaleConstantDerivedDirectImage c.g A
    let PB : proEtaleDerivedCategory c.Z B ⥤ proEtaleDerivedCategory Y B :=
      proEtaleRingDerivedDirectImage c.g (RB.ring Y) (RB.ring c.Z) (RB.pull c.g)
    let QB : proEtaleDerivedCategory c.Z B ⥤ proEtaleDerivedCategory Y B :=
      proEtaleConstantDerivedDirectImage c.g B
    let eJA : JA ≅ KA := Functor.mapDerivedCategoryNatIso (finiteOpenIso l E n c.i)
    let eJB : JB ≅ KB := Functor.mapDerivedCategoryNatIso (finiteOpenIso l L m c.i)
    let ePA : PA ≅ QA :=
      Functor.rightDerivedFunctorNatIso (eqToIso (finiteDirectImage_eq l E n c.g))
    let ePB : PB ≅ QB :=
      Functor.rightDerivedFunctorNatIso (eqToIso (finiteDirectImage_eq l L m c.g))
    let p : PB ⋙ y ≅ z ⋙ PA := proEtaleRingRestrictionDerivedDirectImage c.g
      (RA.ring Y) (RB.ring Y) (RA.ring c.Z) (RB.ring c.Z)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := c.Z) φ)
      (RA.pull c.g) (RB.pull c.g) (asquare c.g)
    let j : x ⋙ JA ≅ JB ⋙ z := openRestriction b c.i
    let jN : x ⋙ KA ≅ KB ⋙ z :=
      Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ)
    let pN : z ⋙ QA ≅ QB ⋙ y := sfDerivedImageRestriction c.g φ
    have hj : j = Functor.isoWhiskerLeft x eJA ≪≫ jN ≪≫
        Functor.isoWhiskerRight eJB.symm z := by
      simpa only [j, jN, x, z, eJA, eJB, JA, KA, JB, KB, A, B, b, RA, RB,
        pbcDerivedRestrict, pbcRestrict, proEtaleCoefficientRestrictScalars,
        proEtaleConstantRingMap] using eq_of_heq
          (finiteDerivedOpen_native l E L n m φ b (fun _ ↦ rfl) c.i)
    have hp : p.symm = Functor.isoWhiskerLeft z ePA ≪≫
        sfDerivedImageRestriction c.g φ ≪≫ Functor.isoWhiskerRight ePB.symm y := by
      exact invertConjugation _ _ _ _ (constantDerivedPush_scalar c.g φ)
    apply heq_of_eq
    exact pastePresentationSquares x z y JA KA JB KB PA QA PB QB
      eJA eJB ePA ePB j jN p.symm pN hj hp

private theorem mate_whisker
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F F' : A ⥤ C} {G G' : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (t : TwoSquare F L₁ L₂ G)
    (f : F' ⟶ F) (g : G ⟶ G') :
    (mateEquiv a₁ a₂ ((t.whiskerTop f).whiskerBottom g)) =
      Functor.whiskerLeft R₁ f ≫ (mateEquiv a₁ a₂ t) ≫
        Functor.whiskerRight g R₂ := by
  ext N
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [← a₂.unit_naturality_assoc]
  simp only [Functor.comp_map]
  have hg := congrArg R₂.map (g.naturality (a₁.counit.app N))
  simp only [R₂.map_comp] at hg
  rw [← reassoc_of% hg]
  simp

-- Normalizing the two presentations expands their derived scalar functor models.
/-- The finite ringed presentation and the intrinsic constant-ring presentation give
exactly the same scalar mate after the canonical presentation isomorphisms.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks Tags 03DI, 0D6E, 0GL6.
Proof: transpose under the scalar adjunctions. Expand both restriction comparisons
as the open square followed by the derived proper square. The finite open comparison
preserves the open units by left-adjoint uniqueness. Transposing its square therefore
identifies the two open restriction maps. The finite direct-image equality identifies
the underived proper coefficient squares on every section. Their K-injective derived
comparisons agree by the uniqueness part of right derivation. Paste these two squares;
the middle presentation maps cancel. The scalar mate bijection is injective and
preserves whiskering, giving the displayed conjugation formula. The equality of the
coefficient maps transports the endpoints; the heterogeneous equality expresses only
that transport, not any change of coefficients or exponent.
(blueprint: lem-sf-finite-scalar-presentation-compatibility). -/
theorem finiteScalarPresentationCompatibility
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Change (finite l E (n + 1) (Nat.succ_pos n))
      (finite l L (m + 1) (Nat.succ_pos m)))
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (hφ : ∀ T : Scheme.{u}, a.map T = proEtaleConstantRingMap (T := T) φ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    HEq (comparison a c)
      ((isoWhiskerRight (finiteImageIso l E n c)
          (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) φ))).hom ≫
        ExceptionalFiniteScalar.leftScalarMap φ c ≫
        (isoWhiskerLeft (pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ))
          (finiteImageIso l L m c).symm).hom) := by
  cases a with
  | mk amap asquare =>
    have hm : amap = fun T ↦ proEtaleConstantRingMap (T := T) φ := funext hφ
    subst amap
    apply heq_of_eq
    apply (mateEquiv (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) φ))
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ))).injective
    have hw := mate_whisker
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) φ))
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ))
      (TwoSquare.mk _ _ _ _ (ExceptionalFiniteScalar.leftScalarMap φ c))
      (finiteImageIso l E n c).hom (finiteImageIso l L m c).inv
    dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.mk] at hw
    simp only [Category.assoc] at hw
    dsimp only [comparison, ExceptionalFiniteScalar.leftScalarMap,
      TwoSquare.mk] at hw ⊢
    dsimp only [pbcDerivedRestrict, pbcRestrict, proEtaleCoefficientRestrictScalars,
      proEtaleConstantRingMap, sfAmbientCompactSupportCandidate,
      sfIntrinsicCompactSupport] at hw ⊢
    simp only [Equiv.apply_symm_apply, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom] at hw ⊢
    dsimp only [TwoSquare] at hw ⊢
    rw [hw]
    simpa only [pbcDerivedRestrict, pbcRestrict, proEtaleCoefficientRestrictScalars,
      proEtaleConstantRingMap, sfAmbientCompactSupportCandidate, sfIntrinsicCompactSupport,
      Equiv.apply_symm_apply, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.symm_hom] using
      congrArg Iso.hom (eq_of_heq
        (finiteRestriction_native l E L n m φ ⟨_, asquare⟩ (fun _ ↦ rfl) c))

end WeilConjectures.PurCompactSupport
