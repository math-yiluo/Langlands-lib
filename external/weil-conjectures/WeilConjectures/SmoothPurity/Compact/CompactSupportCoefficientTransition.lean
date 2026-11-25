/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Native coefficient transitions

Source: Stacks 03DI, 0D6E; Bhatt--Scholze 6.7.6
(blueprint: lem-weil-compact-support-coefficient-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem localizeRestrictionTransition
    {C D X₀ X₁ Y : Type*}
    [Category C] [Category D] [Category X₀] [Category X₁] [Category Y]
    [Abelian C] [Abelian D] [Abelian X₀] [Abelian X₁] [Abelian Y]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory X₀] [HasDerivedCategory X₁] [HasDerivedCategory Y]
    (U : C ⥤ D) (E₀ : C ⥤ X₀) (E₁ : C ⥤ X₁)
    (B₀ B₁ : D ⥤ Y) (F₀ : X₀ ⥤ Y) (F₁ : X₁ ⥤ Y) (p : X₁ ⥤ X₀)
    [U.Additive] [E₀.Additive] [E₁.Additive] [B₀.Additive] [B₁.Additive]
    [F₀.Additive] [F₁.Additive] [p.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits B₀] [PreservesFiniteColimits B₀]
    [PreservesFiniteLimits B₁] [PreservesFiniteColimits B₁]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    (α₀ : U ⋙ B₀ ≅ E₀ ⋙ F₀) (α₁ : U ⋙ B₁ ≅ E₁ ⋙ F₁)
    (γ : p ⋙ F₀ ≅ F₁) (τ : E₀ ⟶ E₁ ⋙ p) (σ : B₀ ⟶ B₁)
    (t : E₀.mapDerivedCategory ⟶ E₁.mapDerivedCategory ⋙ p.mapDerivedCategory)
    (s : B₀.mapDerivedCategory ⟶ B₁.mapDerivedCategory)
    (tfac : ∀ K : CochainComplex C ℤ,
      t.app (DerivedCategory.Q.obj K) ≫
        p.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K) ≫
        p.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj K) =
      E₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K))
    (sfac : ∀ K : CochainComplex D ℤ,
      s.app (DerivedCategory.Q.obj K) ≫ B₁.mapDerivedCategoryFactors.hom.app K =
      B₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app K))
    (htord : ∀ M, σ.app (U.obj M) ≫ α₁.hom.app M =
      α₀.hom.app M ≫ F₀.map (τ.app M) ≫ γ.hom.app (E₁.obj M))
    (M : DerivedCategory C) :
    s.app (U.mapDerivedCategory.obj M) ≫
        (Functor.mapDerivedCategorySquareIso α₁).hom.app M =
      (Functor.mapDerivedCategorySquareIso α₀).hom.app M ≫
        F₀.mapDerivedCategory.map (t.app M) ≫
        (Functor.mapDerivedCategoryCompIso p F₀ ≪≫
          Functor.mapDerivedCategoryNatIso γ).hom.app (E₁.mapDerivedCategory.obj M) := by
  let a₀ := Functor.mapDerivedCategorySquareIso α₀
  let a₁ := Functor.mapDerivedCategorySquareIso α₁
  let β := Functor.mapDerivedCategoryCompIso p F₀ ≪≫
    Functor.mapDerivedCategoryNatIso γ
  have hβ (K : CochainComplex X₁ ℤ) :
      β.hom.app (DerivedCategory.Q.obj K) ≫ F₁.mapDerivedCategoryFactors.hom.app K =
        F₀.mapDerivedCategory.map (p.mapDerivedCategoryFactors.hom.app K) ≫
          F₀.mapDerivedCategoryFactors.hom.app ((p.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app K) := by
    dsimp only [β, Iso.trans_hom, NatTrans.comp_app]
    rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso p F₀).inv.app
      (DerivedCategory.Q.obj K))).1
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors]
    simp only [Category.assoc]
  let l : U.mapDerivedCategory ⋙ B₀.mapDerivedCategory ⟶
      E₁.mapDerivedCategory ⋙ F₁.mapDerivedCategory :=
    Functor.whiskerLeft U.mapDerivedCategory s ≫ a₁.hom
  let r : U.mapDerivedCategory ⋙ B₀.mapDerivedCategory ⟶
      E₁.mapDerivedCategory ⋙ F₁.mapDerivedCategory :=
    a₀.hom ≫ Functor.whiskerRight t F₀.mapDerivedCategory ≫
      Functor.whiskerLeft E₁.mapDerivedCategory β.hom
  have hlr : l = r := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro K
    dsimp only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    let K₁ := (E₁.mapHomologicalComplex (.up ℤ)).obj K
    let UK := (U.mapHomologicalComplex (.up ℤ)).obj K
    have ha₀ := Functor.exactSquare_fac α₀ K
    have ha₁ := Functor.exactSquare_fac α₁ K
    apply (cancel_mono
      (F₁.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₁.mapDerivedCategoryFactors.hom.app K₁)).1
    simp only [Category.assoc]
    have hnβ := β.hom.naturality (E₁.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map] at hnβ
    erw [← reassoc_of% hnβ, hβ]
    rw [← F₀.mapDerivedCategory.map_comp_assoc,
      ← F₀.mapDerivedCategory.map_comp_assoc, Category.assoc]
    erw [tfac K]
    simp only [Functor.map_comp, Category.assoc]
    have hnF := F₀.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K)
    dsimp only [Functor.comp_map] at hnF
    erw [reassoc_of% hnF, reassoc_of% ha₀, ha₁]
    have hns := s.naturality (U.mapDerivedCategoryFactors.hom.app K)
    erw [← reassoc_of% hns, reassoc_of% (sfac UK)]
    have hord : (NatTrans.mapHomologicalComplex σ (.up ℤ)).app UK ≫
        (NatTrans.mapHomologicalComplex α₁.hom (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex α₀.hom (.up ℤ)).app K ≫
        (F₀.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) ≫
        (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app K₁ := by
      apply HomologicalComplex.hom_ext
      intro i
      exact htord (K.X i)
    simpa only [Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ B₀.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        B₀.mapDerivedCategoryFactors.hom.app UK ≫ DerivedCategory.Q.map f) hord
  exact NatTrans.congr_app hlr M

private theorem moduleSheafHomTransport
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M M' N N' : SheafOfModules.{u + 1} R}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : ∀ V : Cᵒᵖ, HEq (fun x ↦ f.val.app V x) (fun x ↦ g.val.app V x)) :
    f = eqToHom hM ≫ g ≫ eqToHom hN.symm := by
  subst M' N'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  ext V x
  exact congrFun (eq_of_heq (h V)) x

/-- All-pair coefficient quotients agree with the direct quotient factor.
Source: Stacks 03DA, 0941
(blueprint: lem-weil-compact-support-coefficient-transition). -/
theorem compactSupportQuotient_eq (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRQuotient l E W h =
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (compactSupportLevelSheafQuotient l E W m n h) := by
  induction m, h using Nat.le_induction with
  | base =>
    simp only [normalizedDVRQuotient, homOfLE_refl, op_id]
    have hq : compactSupportLevelQuotient l E n n le_rfl = RingHom.id _ :=
      Ideal.Quotient.factor_eq
    have hsheaf : compactSupportLevelSheafQuotient l E W n n le_rfl = 𝟙 _ := by
      unfold compactSupportLevelSheafQuotient
      rw [hq]
      exact (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map_id _
    rw [hsheaf]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  | succ m h ih =>
    have hc : normalizedDVRQuotient l E W (h.trans (Nat.le_succ m)) =
        normalizedDVRQuotient l E W (Nat.le_succ m) ≫ normalizedDVRQuotient l E W h := by
      exact ((integralCoefficientSheafSystem l E W).map_comp
        (homOfLE (Nat.le_succ m)).op (homOfLE h).op)
    rw [hc, ih]
    have hs : normalizedDVRQuotient l E W (Nat.le_succ m) =
        (sheafCompose (ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (compactSupportLevelSheafQuotient l E W (m + 1) m (Nat.le_succ m)) := by
      simp only [normalizedDVRQuotient, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      rfl
    rw [hs, ← Functor.map_comp]
    congr 1
    unfold compactSupportLevelSheafQuotient
    rw [← Functor.map_comp]
    congr 1
    ext x
    rcases x with ⟨x⟩
    change (compactSupportLevelQuotient l E m n h)
        ((compactSupportLevelQuotient l E (m + 1) m (Nat.le_succ m)) x) =
      compactSupportLevelQuotient l E (m + 1) n (h.trans (Nat.le_succ m)) x
    refine Quotient.inductionOn x ?_
    intro a
    rfl

/-- Restriction along the direct quotient is the recorded exact finite restriction.
Source: Stacks 03DA
(blueprint: lem-weil-compact-support-coefficient-transition). -/
theorem compactSupportModuleRes_eq (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E W h =
      proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h) := by
  unfold normalizedDVRModuleRes
  rw [compactSupportQuotient_eq]
  rfl

/-- The concrete horizontal map of module sheaves on a sequence site.
Source: Stacks 03DA, 0941 (blueprint: lem-weil-compact-support-coefficient-transition). -/
def compactSupportHorizontalWithCoefficients
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1})
    {m n : ℕ} (S T : Sheaf J RingCat.{u + 1})
    [Functor.IsContinuous (Prod.sectR m C) J (coefficientSequenceTopology J)]
    [Functor.IsContinuous (Prod.sectR n C) J (coefficientSequenceTopology J)]
    (φ : S ⟶ ((Prod.sectR m C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (ψ : T ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (κ : S ⟶ T) (α : Prod.sectR n C ⟶ Prod.sectR m C)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat J
      (coefficientSequenceTopology J)).app R = κ ≫ ψ) :
    SheafOfModules.pushforward.{u + 1} φ ⟶
      SheafOfModules.pushforward.{u + 1} ψ ⋙ SheafOfModules.restrictScalars κ :=
  SheafOfModules.pushforwardNatTrans φ α ≫
    (SheafOfModules.pushforwardCongr he).hom

private theorem compactSupportHorizontalWithCoefficients_sections
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1})
    {m n : ℕ} (S T : Sheaf J RingCat.{u + 1})
    [Functor.IsContinuous (Prod.sectR m C) J (coefficientSequenceTopology J)]
    [Functor.IsContinuous (Prod.sectR n C) J (coefficientSequenceTopology J)]
    (φ : S ⟶ ((Prod.sectR m C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (ψ : T ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (κ : S ⟶ T) (α : Prod.sectR n C ⟶ Prod.sectR m C)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat J
      (coefficientSequenceTopology J)).app R = κ ≫ ψ)
    (M : SheafOfModules.{u + 1} R) (V : Cᵒᵖ) :
    HEq (fun x ↦ ((compactSupportHorizontalWithCoefficients J R S T φ ψ κ α he).app M).val.app V x)
      (fun x : M.val.obj (op (m, V.unop)) ↦ M.val.map (α.app V.unop).op x) := by
  rfl

/-- The horizontal inclusion between coefficient slices.
Source: Stacks 0941 (blueprint: lem-weil-compact-support-coefficient-transition). -/
def compactSupportHorizontalIndex {C : Type*} [Category C]
    {m n : ℕ} (h : n ≤ m) : Prod.sectR n C ⟶ Prod.sectR m C where
  app U := Prod.mkHom (homOfLE h) (𝟙 U)
  naturality := fun {_ _} f ↦ by ext <;> simp

/-- The actual horizontal coefficient square.
Source: Stacks 03DA, 0941 (blueprint: lem-weil-compact-support-coefficient-transition). -/
theorem compactSupportHorizontalRingSquare (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W m).symm ≫
      (Functor.sheafPushforwardContinuousNatTrans (compactSupportHorizontalIndex h) RingCat
        (ProEt.topology W) (coefficientSequenceTopology (ProEt.topology W))).app
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf.{u, u} l E W)) =
      (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (compactSupportLevelSheafQuotient l E W m n h) ≫
          eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W n).symm := by
  rw [← compactSupportQuotient_eq]
  exact coefficientSequenceRingHorizontal.{u, u} l E W h

/-- The actual horizontal map, constructed from the ring-square equality.
Source: Stacks 0941
(blueprint: lem-weil-compact-support-coefficient-transition). -/
def compactSupportOrdinaryCoefficientTransition (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceEvaluation.{u, u} l E W m ⟶
      coefficientSequenceEvaluation.{u, u} l E W n ⋙
        proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h) :=
  compactSupportHorizontalWithCoefficients (ProEt.topology W)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf.{u, u} l E W))
    (integralCoefficientSheaf l E W m) (integralCoefficientSheaf l E W n)
    (eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W m).symm)
    (eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W n).symm)
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (compactSupportLevelSheafQuotient l E W m n h)) (compactSupportHorizontalIndex h)
    (compactSupportHorizontalRingSquare l E W h)

set_option maxHeartbeats 80000 in
-- Keep the sequence rings abstract while applying the section formula.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem compactSupportOrdinaryCoefficientTransition_sections
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules.{u, u} l E W) (V : W.ProEtᵒᵖ) :
    HEq (fun x ↦ ((compactSupportOrdinaryCoefficientTransition l E W h).app M).val.app V x)
      (fun x : M.val.obj (op (m, V.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) :=
  compactSupportHorizontalWithCoefficients_sections (ProEt.topology W)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf.{u, u} l E W))
    (integralCoefficientSheaf l E W m) (integralCoefficientSheaf l E W n)
    (eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W m).symm)
    (eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W n).symm)
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (compactSupportLevelSheafQuotient l E W m n h)) (compactSupportHorizontalIndex h)
    (compactSupportHorizontalRingSquare l E W h) M V

/-- Localization of the actual horizontal coefficient map.
Source: Stacks 0941
(blueprint: lem-weil-compact-support-coefficient-transition). -/
def compactSupportCoefficientTransition (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceDerivedEvaluation.{u, u} l E W m ⟶
      coefficientSequenceDerivedEvaluation.{u, u} l E W n ⋙
        (proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E m n h)).mapDerivedCategory := by
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E m n h)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E m n h)
  exact Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules.{u, u} l E W) (.up ℤ))
    _ _ (coefficientSequenceEvaluation.{u, u} l E W m).mapDerivedCategory
    ((coefficientSequenceEvaluation.{u, u} l E W n ⋙
      proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      (compactSupportOrdinaryCoefficientTransition l E W h) (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation.{u, u} l E W n)
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h))).inv

private theorem compactSupportCoefficientTransition_fac (W : Scheme.{u}) {m n : ℕ}
    (h : n ≤ m) (K : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ) :
    (compactSupportCoefficientTransition l E W h).app (DerivedCategory.Q.obj K) ≫
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
          ((coefficientSequenceEvaluation.{u, u} l E W n).mapDerivedCategoryFactors.hom.app K) ≫
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj K) =
    (coefficientSequenceEvaluation.{u, u} l E W m).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (compactSupportOrdinaryCoefficientTransition l E W h) (.up ℤ)).app K) := by
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E m n h)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E m n h)
  letI : PreservesFiniteLimits (coefficientSequenceEvaluation.{u, u} l E W n ⋙
      proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h)) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (coefficientSequenceEvaluation.{u, u} l E W n ⋙
      proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h)) :=
    comp_preservesFiniteColimits _ _
  dsimp only [compactSupportCoefficientTransition, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Localization.liftNatTrans_app]
  simp only [Category.assoc]
  change _ ≫ _ ≫
    (Functor.mapDerivedCategoryFactors
      (coefficientSequenceEvaluation.{u, u} l E W n ⋙
        proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E m n h))).inv.app K ≫ _ = _
  simp only [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private def ordinaryRestrictionComp (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h) ⋙
        scalarReductionRestriction l E W m ≅ scalarReductionRestriction l E W n :=
  pbcRestrictComp
    (completedIntegralCommRingProjectionUnrestricted l E W m)
    (compactSupportLevelSheafQuotient l E W m n h)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (compactSupportProjection_comp l E W m n h)

private theorem restrictCompMapSections {W : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : pbcModules W S) (N : pbcModules W B)
    (f : M ⟶ (pbcRestrict ψ).obj N) (V : W.ProEtᵒᵖ) :
    HEq (fun x ↦ (((pbcRestrict φ).map f ≫
        (pbcRestrictComp φ ψ χ h).hom.app N).val.app V) x)
      (fun x : M.val.obj V ↦ f.val.app V x) := by
  exact heq_of_eq (funext (fun x ↦
    (pbcRestrictComp_exists φ ψ χ h).exists.choose_spec N V (f.val.app V x)))

set_option maxHeartbeats 100000 in
-- Unfolding the normalized section comparisons traverses the scalar restriction models.
private theorem ordinaryRestrictionTransition (W : Scheme.{u}) {m n : ℕ}
    (h : n ≤ m) (M : coefficientSequenceModules.{u, u} l E W) :
    (((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE h).op).app
        ((coefficientSequenceRestriction l E W).obj M)) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation.{u, u} l E W n)).hom.app M =
    (eqToIso (coefficientSequenceRestriction_evaluation.{u, u} l E W m)).hom.app M ≫
      (scalarReductionRestriction l E W m).map
        ((compactSupportOrdinaryCoefficientTransition l E W h).app M) ≫
      (ordinaryRestrictionComp l E W h).hom.app
        ((coefficientSequenceEvaluation.{u, u} l E W n).obj M) := by
  let hU := (coefficientSequenceRestriction_exists.{u, u} l E W).exists.choose_spec
  let em := hU.1 M m
  let en := hU.1 M n
  let g := (scalarReductionRestriction l E W m).map
    ((compactSupportOrdinaryCoefficientTransition l E W h).app M) ≫
    (ordinaryRestrictionComp l E W h).hom.app
      ((coefficientSequenceEvaluation.{u, u} l E W n).obj M)
  have hg (V : W.ProEtᵒᵖ) :
      HEq (fun x ↦ g.val.app V x)
        (fun x : M.val.obj (op (m, V.unop)) ↦
          M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) := by
    exact (restrictCompMapSections
      (completedIntegralCommRingProjectionUnrestricted l E W m)
      (compactSupportLevelSheafQuotient l E W m n h)
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (compactSupportProjection_comp l E W m n h) _ _
      ((compactSupportOrdinaryCoefficientTransition l E W h).app M) V).trans
        (compactSupportOrdinaryCoefficientTransition_sections l E W h M V)
  have ht := moduleSheafHomTransport em en
    (((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op) g
    (fun V ↦ (hU.2.1 M m n h V).trans (hg V).symm)
  have ht' : (((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op) ≫
      eqToHom en = eqToHom em ≫ g := by
    rw [ht]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  dsimp only [g, em, en, hU, coefficientSequenceRestriction] at ht' ⊢
  simp only [eqToIso.hom, eqToHom_app]
  change (((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op) ≫
      eqToHom en = eqToHom em ≫ g
  exact ht'

private theorem towerTransition_fac (W : Scheme.{u}) (m n : ℕ)
    (h : n ≤ m) (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    (pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h).app
        (DerivedCategory.Q.obj I) ≫
      (coefficientConstantTowerEvaluationFactors.{u, u} l E W n).hom.app I =
    (coefficientConstantTowerEvaluationFactors.{u, u} l E W m).hom.app I ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE h).op)
        (.up ℤ)).app I) := by
  change _ ≫ (((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj
    (op n)).mapDerivedCategoryFactors.hom.app I) = _
  simp only [pbcTowerTransition, Localization.liftNatTrans_app, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

/-- Exact completed restriction carries the actual horizontal map to the derived
strict-tower transition, with its canonical scalar composition comparison.
Source: Stacks 03DA, 0941; proof: localize the sectionwise horizontal square.
(blueprint: lem-weil-compact-support-coefficient-transition). -/
theorem compactSupportCoefficientTransition_restricted (W : Scheme.{u}) {m n : ℕ}
    (h : n ≤ m) (M : coefficientSequenceDerived.{u, u} l E W) :
    (pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h).app
        ((coefficientSequenceDerivedRestriction l E W).obj M) ≫
      (coefficientRestrictedEvaluationIso l E W n).hom.app M =
    (coefficientRestrictedEvaluationIso l E W m).hom.app M ≫
      (scalarReductionDerivedRestriction l E W m).map
        ((compactSupportCoefficientTransition l E W h).app M) ≫
      (compactSupportRestrictionComp l E W m n h).hom.app
        ((coefficientSequenceDerivedEvaluation l E W n).obj M) := by
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E m n h)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E m n h)
  exact localizeRestrictionTransition
    (coefficientSequenceRestriction l E W)
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op m))
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (scalarReductionRestriction l E W m) (scalarReductionRestriction l E W n)
    (proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h))
    (eqToIso (coefficientSequenceRestriction_evaluation l E W m))
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n))
    (ordinaryRestrictionComp l E W h)
    (compactSupportOrdinaryCoefficientTransition l E W h)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE h).op)
    (compactSupportCoefficientTransition l E W h)
    (pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h)
    (compactSupportCoefficientTransition_fac l E W h)
    (towerTransition_fac l E W m n h)
    (ordinaryRestrictionTransition l E W h) M

end WeilConjectures
