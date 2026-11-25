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
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryOpenTransition

/-! # Coefficient compatibility of native open evaluation

Source: Stacks 03DI, 0D6E and 0D6J; Zheng 4.1 and 4.10
(blueprint: lem-weil-compact-support-native-open-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open ProEtale.VaryingRing
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftAdjoint exactAdj

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem localizeOpenTransition
    {C D X₀ X₁ Y₀ Y₁ : Type*}
    [Category C] [Category D] [Category X₀] [Category X₁] [Category Y₀] [Category Y₁]
    [Abelian C] [Abelian D] [Abelian X₀] [Abelian X₁] [Abelian Y₀] [Abelian Y₁]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory X₀] [HasDerivedCategory X₁]
    [HasDerivedCategory Y₀] [HasDerivedCategory Y₁]
    (U : C ⥤ D) (E₀ : C ⥤ X₀) (E₁ : C ⥤ X₁)
    (B₀ : D ⥤ Y₀) (B₁ : D ⥤ Y₁) (F₀ : X₀ ⥤ Y₀) (F₁ : X₁ ⥤ Y₁)
    (p : X₁ ⥤ X₀) (q : Y₁ ⥤ Y₀)
    [U.Additive] [E₀.Additive] [E₁.Additive] [B₀.Additive] [B₁.Additive]
    [F₀.Additive] [F₁.Additive] [p.Additive] [q.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits B₀] [PreservesFiniteColimits B₀]
    [PreservesFiniteLimits B₁] [PreservesFiniteColimits B₁]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    (α₀ : U ⋙ B₀ ≅ E₀ ⋙ F₀) (α₁ : U ⋙ B₁ ≅ E₁ ⋙ F₁)
    (γ : p ⋙ F₀ ≅ F₁ ⋙ q) (τ : E₀ ⟶ E₁ ⋙ p) (σ : B₀ ⟶ B₁ ⋙ q)
    (t : E₀.mapDerivedCategory ⟶ E₁.mapDerivedCategory ⋙ p.mapDerivedCategory)
    (s : B₀.mapDerivedCategory ⟶ B₁.mapDerivedCategory ⋙ q.mapDerivedCategory)
    (tfac : ∀ K : CochainComplex C ℤ,
      t.app (DerivedCategory.Q.obj K) ≫
        p.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K) ≫
        p.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj K) =
      E₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K))
    (sfac : ∀ K : CochainComplex D ℤ,
      s.app (DerivedCategory.Q.obj K) ≫
        q.mapDerivedCategory.map (B₁.mapDerivedCategoryFactors.hom.app K) ≫
        q.mapDerivedCategoryFactors.hom.app ((B₁.mapHomologicalComplex (.up ℤ)).obj K) =
      B₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app K))
    (htord : ∀ M, σ.app (U.obj M) ≫ q.map (α₁.hom.app M) =
      α₀.hom.app M ≫ F₀.map (τ.app M) ≫ γ.hom.app (E₁.obj M))
    (M : DerivedCategory C) :
    s.app (U.mapDerivedCategory.obj M) ≫
        q.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso α₁).hom.app M) =
      (Functor.mapDerivedCategorySquareIso α₀).hom.app M ≫
        F₀.mapDerivedCategory.map (t.app M) ≫
        (Functor.mapDerivedCategorySquareIso γ).hom.app (E₁.mapDerivedCategory.obj M) := by
  let a₀ := Functor.mapDerivedCategorySquareIso α₀
  let a₁ := Functor.mapDerivedCategorySquareIso α₁
  let β := Functor.mapDerivedCategorySquareIso γ
  let l : U.mapDerivedCategory ⋙ B₀.mapDerivedCategory ⟶
      (E₁.mapDerivedCategory ⋙ F₁.mapDerivedCategory) ⋙ q.mapDerivedCategory :=
    Functor.whiskerLeft U.mapDerivedCategory s ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight a₁.hom q.mapDerivedCategory
  let r : U.mapDerivedCategory ⋙ B₀.mapDerivedCategory ⟶
      (E₁.mapDerivedCategory ⋙ F₁.mapDerivedCategory) ⋙ q.mapDerivedCategory :=
    a₀.hom ≫ Functor.whiskerRight t F₀.mapDerivedCategory ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft E₁.mapDerivedCategory β.hom ≫ (Functor.associator _ _ _).inv
  have hlr : l = r := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro K
    dsimp only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    let K₁ := (E₁.mapHomologicalComplex (.up ℤ)).obj K
    let UK := (U.mapHomologicalComplex (.up ℤ)).obj K
    have ha₀ := Functor.exactSquare_fac α₀ K
    have ha₁ := Functor.exactSquare_fac α₁ K
    have hβ := Functor.exactSquare_fac γ K₁
    have ht := tfac K
    have hs := sfac UK
    apply (cancel_mono
      (q.mapDerivedCategory.map
          (F₁.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K)) ≫
        q.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K₁) ≫
        q.mapDerivedCategoryFactors.hom.app
          ((F₁.mapHomologicalComplex (.up ℤ)).obj K₁))).1
    simp only [Category.assoc]
    have hnβ := β.hom.naturality (E₁.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map] at hnβ
    erw [← reassoc_of% hnβ, hβ]
    rw [← F₀.mapDerivedCategory.map_comp_assoc,
      ← F₀.mapDerivedCategory.map_comp_assoc, Category.assoc]
    erw [ht]
    simp only [Functor.map_comp, Category.assoc]
    have hnF := F₀.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K)
    dsimp only [Functor.comp_map] at hnF
    erw [reassoc_of% hnF]
    erw [reassoc_of% ha₀]
    rw [← q.mapDerivedCategory.map_comp_assoc,
      ← q.mapDerivedCategory.map_comp_assoc, Category.assoc]
    erw [ha₁]
    simp only [Functor.map_comp, Category.assoc]
    have hnq := q.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex α₁.hom (.up ℤ)).app K)
    dsimp only [Functor.comp_map] at hnq
    erw [hnq]
    have hns := s.naturality (U.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map] at hns
    erw [← reassoc_of% hns, reassoc_of% hs]
    have hord :
        (NatTrans.mapHomologicalComplex σ (.up ℤ)).app UK ≫
          (q.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex α₁.hom (.up ℤ)).app K) =
        (NatTrans.mapHomologicalComplex α₀.hom (.up ℤ)).app K ≫
          (F₀.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) ≫
          (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app K₁ := by
      ext i
      exact htord (K.X i)
    simpa only [Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ B₀.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        B₀.mapDerivedCategoryFactors.hom.app UK ≫ DerivedCategory.Q.map f) hord
  simpa only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app hlr M

private theorem exactAdj_unit_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    ((a.mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
      R.rightDerivedFunctorIsoMapDerivedCategory).unit = (exactAdj a).unit := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
    R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K))).mp
  have hn := R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app K)
  have ha := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso A (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit K
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj K) ≫
    R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K) = _ at ha
  have he := NatTrans.congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((L.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at he
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  rw [← reassoc_of% hn, reassoc_of% ha, reassoc_of% he,
    Iso.inv_hom_id_app]
  exact (CategoryTheory.Category.comp_id _).trans (exactAdj_unit a K).symm

private theorem inverseMate_localize
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {P : B ⥤ A} {L' : C ⥤ D} {P' : D ⥤ C}
    [L.Additive] [P.Additive] [L'.Additive] [P'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    (a : L ⊣ P) (b : L' ⊣ P') (E : A ⥤ C) (E' : B ⥤ D)
    [E.Additive] [E'.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
    (d : P ⋙ E ≅ E' ⋙ P')
    [IsIso ((mateEquiv a b).symm d.hom)] :
    ((mateEquiv
      ((a.mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
        P.rightDerivedFunctorIsoMapDerivedCategory)
      ((b.mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
        P'.rightDerivedFunctorIsoMapDerivedCategory)).symm
      (Functor.mapDerivedCategorySquareIso d).hom) =
    (Functor.mapDerivedCategorySquareIso
      (asIso ((mateEquiv a b).symm d.hom))).hom := by
  have ha := Adjunction.ext (exactAdj_unit_eq a)
  have hb := Adjunction.ext (exactAdj_unit_eq b)
  rw [ha, hb]
  let β := asIso ((mateEquiv a b).symm d.hom)
  have hβ (M : A) : b.unit.app (E.obj M) ≫ P'.map (β.hom.app M) =
      E.map (a.unit.app M) ≫ d.hom.app (L.obj M) :=
    (unit_mateEquiv_symm a b d.hom M).symm
  have hd := exactDerivedMate a b d β hβ
  ext M
  apply ((exactAdj b).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (exactAdj a) (exactAdj b)
    (Functor.mapDerivedCategorySquareIso d).hom M).symm.trans (hd M).symm

private theorem square_postcompose
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (V : B ⥤ D) (E : A ⥤ C) (F F' : C ⥤ D)
    [U.Additive] [V.Additive] [E.Additive] [F.Additive] [F'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : U ⋙ V ≅ E ⋙ F) (e : F ≅ F') :
    Functor.mapDerivedCategorySquareIso (α ≪≫ Functor.isoWhiskerLeft E e) =
      Functor.mapDerivedCategorySquareIso α ≪≫
        Functor.isoWhiskerLeft E.mapDerivedCategory (Functor.mapDerivedCategoryNatIso e) := by
  apply Iso.ext
  ext M
  have h := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft E e) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_trans,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  rw [h]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The open part of the specified native evaluation, with its original unit normalization.
Source: Stacks 03DI; Zheng, Construction 4.1 and Lemma 4.10.
(blueprint: lem-weil-compact-support-native-open-transition). -/
def compactSupportNativeOpenEvaluation {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j ⋙
      coefficientSequenceDerivedEvaluation.{u, u} l E Z n ≅
    coefficientSequenceDerivedEvaluation.{u, u} l E X n ⋙
      (sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory := by
  have := sfIntrinsicExtensionByZero_additive j
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  exact ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1))))

-- Give evaluation its canonical properties with the native source expression.
-- This also fixes the abelian structures selected by exact-square localization.
private local instance nativeEvalAdditive (W : Scheme.{u}) (n : ℕ) :
    @Functor.Additive
      (Modules (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) W)
      (normalizedDVRModules.{u, u} l E W n) _ _
      (inferInstance : Abelian (Modules (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) W)).toPreadditive
      (inferInstance : Abelian (normalizedDVRModules.{u, u} l E W n)).toPreadditive
      (coefficientSequenceEvaluation.{u, u} l E W n) := by
  constructor
  intro M N f g
  ext V x
  rfl

private local instance nativeEvalLimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (show Modules (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) W ⥤ normalizedDVRModules.{u, u} l E W n from
      coefficientSequenceEvaluation.{u, u} l E W n) := by
  exact (coefficientSequenceEvaluation_exact l E W n).1

private local instance nativeEvalColimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (show Modules (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) W ⥤ normalizedDVRModules.{u, u} l E W n from
      coefficientSequenceEvaluation.{u, u} l E W n) := by
  exact (coefficientSequenceEvaluation_exact l E W n).2

private local instance levelOpenAdditive {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    @Functor.Additive (normalizedDVRModules.{u, u} l E X n)
      (normalizedDVRModules.{u, u} l E Z n) _ _
      (inferInstance : Abelian (normalizedDVRModules.{u, u} l E X n)).toPreadditive
      (inferInstance : Abelian (normalizedDVRModules.{u, u} l E Z n)).toPreadditive
      (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1))) := by
  exact sfIntrinsicExtensionByZero_additive j
    (Padic.coefficientExtensionRing l E (n + 1))

private local instance levelOpenLimits {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    PreservesFiniteLimits (show normalizedDVRModules.{u, u} l E X n ⥤
      normalizedDVRModules.{u, u} l E Z n from
      sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1))) := by
  exact (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1

private local instance levelOpenColimits {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    PreservesFiniteColimits (show normalizedDVRModules.{u, u} l E X n ⥤
      normalizedDVRModules.{u, u} l E Z n from
      sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1))) := by
  exact (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2

private theorem nativeOpenEvaluation_localize
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    compactSupportNativeOpenEvaluation l E j n =
      Functor.mapDerivedCategorySquareIso (compactSupportOrdinaryOpenEvaluation l E j n) := by
  have := sfIntrinsicExtensionByZero_additive j
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let a := moduleJAdj R q j
  let b := ProEtale.StrictTower.moduleJAdj (R n) j
  let d := moduleEvalG R q j n
  have := (ProEtale.StrictTower.moduleJAdj (R n) j).left_adjoint_additive
  have := (ProEtale.StrictTower.moduleJ_exact (R n) j).2.1
  have := (ProEtale.StrictTower.moduleJ_exact (R n) j).2.2
  have := ProEtale.StrictTower.modulePullback_additive (R n) j
  have := ProEtale.StrictTower.modulePullback_finiteLimits (R n) j
  have := ProEtale.StrictTower.modulePullback_finiteColimits (R n) j
  have := ordinaryOpenMateIso R q j n
  let β := asIso ((mateEquiv a b).symm d.hom)
  have hj : evalJ R q j n = Functor.mapDerivedCategorySquareIso β.symm := by
    apply Iso.ext_inv
    change evalJInv R q j n = _
    rw [← Functor.square_symm_hom]
    exact inverseMate_localize a b (eval R q X n) (eval R q Z n) d
  change evalJ R q j n ≪≫
      Functor.isoWhiskerLeft (ev R q X n) (Functor.mapDerivedCategoryNatIso
        (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)))) =
    Functor.mapDerivedCategorySquareIso (β.symm ≪≫
      Functor.isoWhiskerLeft (eval R q X n)
        (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1))))
  rw [square_postcompose, hj]

-- The horizontal transformations use the coefficient-site abelian structure.
private abbrev nativeCoefficientAbelian (W : Scheme.{u}) :
    Abelian (coefficientSequenceModules.{u, u} l E W) :=
  SheafOfModules.instAbelian _

private local instance nativeExtensionAdditive {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] :
    @Functor.Additive
      (Modules (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) X)
      (Modules (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) Z) _ _
      (inferInstance : Abelian (Modules (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) X)).toPreadditive
      (inferInstance : Abelian (Modules (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) Z)).toPreadditive
      (extension (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j) := by
  exact extensionAdditive (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j

-- Keep conversion from expanding the localization choices during specialization.
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategoryNatIso
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Specialize exact localization with the coefficient-site structures fixed explicitly. -/
private theorem localizedOrdinaryOpenTransition
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {m n : ℕ} (h : n ≤ m) (M : coefficientSequenceDerived.{u, u} l E X) :
    (compactSupportCoefficientTransition l E Z h).app
        ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj M) ≫
      (proEtaleCoefficientRestrictScalars Z
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso
            (compactSupportOrdinaryOpenEvaluation l E j n)).hom.app M) =
    (Functor.mapDerivedCategorySquareIso
      (compactSupportOrdinaryOpenEvaluation l E j m)).hom.app M ≫
      (sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
          ((compactSupportCoefficientTransition l E X h).app M) ≫
      (Functor.mapDerivedCategorySquareIso
        (sfOpenRestriction j (compactSupportLevelQuotient l E m n h))).hom.app
          ((coefficientSequenceDerivedEvaluation l E X n).obj M) :=
  @localizeOpenTransition
    (coefficientSequenceModules.{u, u} l E X)
    (coefficientSequenceModules.{u, u} l E Z)
    (normalizedDVRModules.{u, u} l E X m) (normalizedDVRModules.{u, u} l E X n)
    (normalizedDVRModules.{u, u} l E Z m) (normalizedDVRModules.{u, u} l E Z n)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (nativeCoefficientAbelian l E X) (nativeCoefficientAbelian l E Z)
    (SheafOfModules.instAbelian _) (SheafOfModules.instAbelian _)
    (SheafOfModules.instAbelian _) (SheafOfModules.instAbelian _)
    (@HasDerivedCategory.standard (coefficientSequenceModules.{u, u} l E X) _
      (nativeCoefficientAbelian l E X))
    (@HasDerivedCategory.standard (coefficientSequenceModules.{u, u} l E Z) _
      (nativeCoefficientAbelian l E Z))
    (@HasDerivedCategory.standard (normalizedDVRModules.{u, u} l E X m) _
      (SheafOfModules.instAbelian _))
    (@HasDerivedCategory.standard (normalizedDVRModules.{u, u} l E X n) _
      (SheafOfModules.instAbelian _))
    (@HasDerivedCategory.standard (normalizedDVRModules.{u, u} l E Z m) _
      (SheafOfModules.instAbelian _))
    (@HasDerivedCategory.standard (normalizedDVRModules.{u, u} l E Z n) _
      (SheafOfModules.instAbelian _))
    (extension (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
    (coefficientSequenceEvaluation l E X m) (coefficientSequenceEvaluation l E X n)
    (coefficientSequenceEvaluation l E Z m) (coefficientSequenceEvaluation l E Z n)
    (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (m + 1)))
    (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleCoefficientRestrictScalars X (compactSupportLevelQuotient l E m n h))
    (proEtaleCoefficientRestrictScalars Z (compactSupportLevelQuotient l E m n h))
    (extensionAdditive (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (coefficientSequenceEvaluation_additive l E X m)
    (coefficientSequenceEvaluation_additive l E X n)
    (coefficientSequenceEvaluation_additive l E Z m)
    (coefficientSequenceEvaluation_additive l E Z n)
    (sfIntrinsicExtensionByZero_additive j (Padic.coefficientExtensionRing l E (m + 1)))
    (sfIntrinsicExtensionByZero_additive j (Padic.coefficientExtensionRing l E (n + 1)))
    (by
      constructor
      intro M₀ N₀ f g
      ext V x
      rfl)
    (by
      constructor
      intro M₀ N₀ f g
      ext V x
      rfl)
    (extension_exact (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j).2.1
    (extension_exact (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j).2.2
    (coefficientSequenceEvaluation_exact l E X m).1
    (coefficientSequenceEvaluation_exact l E X m).2
    (coefficientSequenceEvaluation_exact l E X n).1
    (coefficientSequenceEvaluation_exact l E X n).2
    (coefficientSequenceEvaluation_exact l E Z m).1
    (coefficientSequenceEvaluation_exact l E Z m).2
    (coefficientSequenceEvaluation_exact l E Z n).1
    (coefficientSequenceEvaluation_exact l E Z n).2
    (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (m + 1))).2.1
    (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (m + 1))).2.2
    (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).2.1
    (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).2.2
    (proEtaleCoefficientRestrictScalars_preservesFiniteLimits X
      (compactSupportLevelQuotient l E m n h))
    (proEtaleCoefficientRestrictScalars_preservesFiniteColimits X
      (compactSupportLevelQuotient l E m n h))
    (proEtaleCoefficientRestrictScalars_preservesFiniteLimits Z
      (compactSupportLevelQuotient l E m n h))
    (proEtaleCoefficientRestrictScalars_preservesFiniteColimits Z
      (compactSupportLevelQuotient l E m n h))
    (compactSupportOrdinaryOpenEvaluation l E j m)
    (compactSupportOrdinaryOpenEvaluation l E j n)
    (sfOpenRestriction j (compactSupportLevelQuotient l E m n h))
    (compactSupportOrdinaryCoefficientTransition l E X h)
    (compactSupportOrdinaryCoefficientTransition l E Z h)
    (compactSupportCoefficientTransition l E X h) (compactSupportCoefficientTransition l E Z h)
    (compactSupportCoefficientTransition_fac l E X h)
    (compactSupportCoefficientTransition_fac l E Z h)
    (compactSupportOrdinaryOpenTransition l E j h) M

/-- Open evaluation respects every horizontal coefficient map of an arbitrary derived system.
Source: Stacks 03DI, 03DA, 0941; Zheng, Construction 4.1 and Lemma 4.10;
the open-extension step of the native compact-support transition proof.
(blueprint: lem-weil-compact-support-native-open-transition).
Proof: first work with module sheaves on the sequence site. Transpose the proposed square
under the open-extension/restriction adjunctions. The horizontal transformation is the
actual map of sections along (n,U) to (m,U); evaluation of ordinary direct image preserves
sections. Naturality of the system adjunction unit therefore identifies the transposes.
The unit equations defining moduleEvalG and the inverse mate defining evalJ identify this
open square with the native one. Transport the single-level adjunctions along
compactSupportOpenModel. Its left-adjoint uniqueness normalization, together with the
section normalization of sfRealizationRestriction and the units defining
sfFixedOpenRestriction, identifies the transported coefficient square with sfOpenRestriction.
All open extensions, evaluations and scalar restrictions are exact. Apply the degreewise
square to complexes, then localize at quasi-isomorphisms. The localization factorization
of compactSupportCoefficientTransition and mapDerivedCategorySquareIso gives precisely
the displayed equation. Localization natural-transformation extensionality extends it to
all derived objects. The argument uses only n <= m, so includes equality and arbitrary,
noncartesian systems, without any flatness assumption. -/
theorem compactSupportNativeOpenTransition
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {m n : ℕ} (h : n ≤ m) (M : coefficientSequenceDerived.{u, u} l E X) :
    (compactSupportCoefficientTransition l E Z h).app
        ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj M) ≫
      (proEtaleCoefficientRestrictScalars Z
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
          ((compactSupportNativeOpenEvaluation l E j n).hom.app M) =
    (compactSupportNativeOpenEvaluation l E j m).hom.app M ≫
      (sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
          ((compactSupportCoefficientTransition l E X h).app M) ≫
      (Functor.mapDerivedCategorySquareIso
        (sfOpenRestriction j (compactSupportLevelQuotient l E m n h))).hom.app
          ((coefficientSequenceDerivedEvaluation l E X n).obj M) := by
  have := sfIntrinsicExtensionByZero_additive j
    (Padic.coefficientExtensionRing l E (m + 1))
  have := sfIntrinsicExtensionByZero_additive j
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (m + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (m + 1))).2.2
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  have := proEtaleCoefficientRestrictScalars_preservesFiniteLimits X
    (compactSupportLevelQuotient l E m n h)
  have := proEtaleCoefficientRestrictScalars_preservesFiniteColimits X
    (compactSupportLevelQuotient l E m n h)
  have := proEtaleCoefficientRestrictScalars_preservesFiniteLimits Z
    (compactSupportLevelQuotient l E m n h)
  have := proEtaleCoefficientRestrictScalars_preservesFiniteColimits Z
    (compactSupportLevelQuotient l E m n h)
  rw [nativeOpenEvaluation_localize, nativeOpenEvaluation_localize]
  dsimp only [coefficientSequenceDerivedEvaluation, J]
  exact localizedOrdinaryOpenTransition l E j h M

end WeilConjectures
