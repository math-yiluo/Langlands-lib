/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
public import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
import WeilConjectures.TraceFormula.Supporting.NormalizedIntegralMixedCoherence
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackCompletionNormalization

/-! # The coefficient transition equation for normalized automorphism squares

Source: the Weil-structures paragraph of the open-closed localization proof,
steps 7--9 of lem-sf-automorphism-constructible-stage-equivalence.
(blueprint: lem-sf-automorphism-square-stage-compatibility).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u v a₀ a₁ b₀ b₁
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  integralDerivedPullback integralScalarExtensionOfUniverses integralComparisonComposition
  integralComparisonScalar scalarPullbackCompleted
attribute [local implicit_reducible] constructibleIntegralPullback
  integralComparisonConstructibleScalar sfConstructibleIntegralScalarExtension
open AlgebraicallyClosedCoefficients (Index Coefficient)

-- Endpoint transport and scalar-one formulas, adapted from AutomorphismSquareRationalScalar.
private theorem dependent_heq {A : Type*} {B : A → Sort*}
    (f : (a : A) → B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  subst b
  rfl

private theorem map_heq
    {C : Type a₀} {D : Type b₀} [Category C] [Category D]
    (F : C ⥤ D) {A A' B B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst A'
  subst B'
  cases h
  rfl

private theorem pullback_map_localized
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {K J : sfIntegralConstructibleCategory l E Y} (r : K ⟶ J) :
    HEq ((rationalDerivedPullback l E f).map
      ((sfRationalConstructibleLocalization l E Y).map r))
      ((sfRationalConstructibleLocalization l E X).map
        ((constructibleIntegralPullback l E f).map r)) := by
  have hr := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K J r 1
  simp only [sfRationalConstructibleLocalization, ScalarLocalization.localization] at hr ⊢
  exact hr

private theorem scalar_map_localized
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u})
    {K J : sfIntegralConstructibleCategory l E X} (r : K ⟶ J) :
    HEq ((sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
      ((sfRationalConstructibleLocalization l E X).map r))
      ((sfRationalConstructibleLocalization l L X).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map r)) := by
  have hs := (sfRationalScalarExtension_existsUnique l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 K J r 1
  simp only [sfRationalConstructibleLocalization,
    ScalarLocalization.localization, map_one] at hs ⊢
  exact hs

private theorem scalar_comparison_hom
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralPullbackScalarComparison l E L ι f K).hom.hom =
      (integralComparisonScalar l E L ι C f K).hom := by
  change (scalarPullbackCompleted l E L ι f K.obj K.property.1
    ((constructibleIntegralPullback l E f).obj K).property.1).hom = _
  apply (cancel_mono (integralComparisonMu l E L ι C f K).hom).1
  simpa only [integralComparisonScalar, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    integralScalarPullbackCompletion_normalization l E L ι C f K
      ((constructibleIntegralPullback l E f).obj K).property.1

private theorem map_transport_naturality
    {I : Type*} {A B : Type*} [Category A] [Category B]
    (T : A ⥤ B) (F : I → A) (G : I → B)
    (c : ∀ i, T.obj (F i) ⟶ G i) {i j : I} (h : i = j) :
    T.map (eqToHom (congrArg F h)) ≫ c j = c i ≫ eqToHom (congrArg G h) := by
  subst j
  simp only [eqToHom_refl, T.map_id, Category.id_comp, Category.comp_id]

private theorem mixed_square_cancel
    {A B : Type*} [Category A] [Category B] (T : A ⥤ B)
    {P Q R S : A} {P' Q' R' S' : B}
    (c : P ≅ Q) (d : R ≅ S) (c' : P' ≅ Q') (d' : R' ≅ S')
    (e : P ⟶ R) (e' : P' ⟶ R')
    (p : T.obj P ⟶ P') (q : T.obj Q ⟶ Q')
    (r : T.obj R ⟶ R') (s : T.obj S ⟶ S')
    (hc : T.map c.hom ≫ q = p ≫ c'.hom)
    (hd : T.map d.hom ≫ s = r ≫ d'.hom)
    (he : T.map e ≫ r = p ≫ e') :
    T.map (c.inv ≫ e ≫ d.hom) ≫ s = q ≫ c'.inv ≫ e' ≫ d'.hom := by
  apply (cancel_epi (T.map c.hom)).1
  simp only [T.map_comp, Category.assoc]
  rw [← T.map_comp_assoc, c.hom_inv_id, T.map_id, Category.id_comp]
  rw [reassoc_of% hc, Iso.hom_inv_id_assoc, hd, reassoc_of% he]

private theorem integral_square
    (l : ℕ) [Fact l.Prime]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom)
    (a : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E eY.asIso.hom ≅
        constructibleIntegralPullback l E eX.asIso.hom ⋙ constructibleIntegralPullback l E f)
    (ha : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfIntegralConstructibleCategory l E X),
      ((a E).hom.app K).hom =
        (integralComparisonComposition l E C eY.asIso.hom f K).inv ≫
          eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
            (integralComparisonComposition l E C f eX.asIso.hom K).hom)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (K : sfIntegralConstructibleCategory l E X) :
    (integralScalarExtension l E L ι Y).map
        ((a E).hom.app K).hom ≫
      (integralComparisonScalar l E L ι C f
        ((constructibleIntegralPullback l E eX.asIso.hom).obj K)).hom ≫
      (integralDerivedPullback l L f).map
        (integralComparisonScalar l E L ι C eX.asIso.hom K).hom =
    (integralComparisonScalar l E L ι C eY.asIso.hom
        ((constructibleIntegralPullback l E f).obj K)).hom ≫
      (integralDerivedPullback l L eY.asIso.hom).map
        (integralComparisonScalar l E L ι C f K).hom ≫
      ((a L).hom.app
        ((integralComparisonConstructibleScalar l E L ι X).obj K)).hom := by
  have h₁ := congrArg (fun r ↦ r.hom)
    ((normalizedIntegralMixedCoherence l C E L ι).2 eY.asIso.hom f K)
  have h₂ := congrArg (fun r ↦ r.hom)
    ((normalizedIntegralMixedCoherence l C E L ι).2 f eX.asIso.hom K)
  dsimp only [integralComparisonScalarSquareLeft, integralComparisonScalarSquareRight,
    ObjectProperty.homMk_hom] at h₁ h₂
  have ht (g g' : Y ⟶ X) (w : g = g') :
      (integralScalarExtension l E L ι Y).map
          (eqToHom (congrArg (fun a ↦ (integralDerivedPullback l E a).obj K.obj) w)) ≫
        (integralComparisonScalar l E L ι C g' K).hom =
      (integralComparisonScalar l E L ι C g K).hom ≫
        eqToHom (congrArg (fun a ↦ (integralDerivedPullback l L a).obj
          ((integralComparisonConstructibleScalar l E L ι X).obj K).obj) w) := by
    exact map_transport_naturality (integralScalarExtension l E L ι Y)
      (fun g ↦ (integralDerivedPullback l E g).obj K.obj)
      (fun g ↦ (integralDerivedPullback l L g).obj
        ((integralComparisonConstructibleScalar l E L ι X).obj K).obj)
      (fun g ↦ (integralComparisonScalar l E L ι C g K).hom) w
  have hbE := ha E K
  have hbL := ha L ((integralComparisonConstructibleScalar l E L ι X).obj K)
  rw [hbE, hbL]
  simpa only [Category.assoc, integralComparisonConstructibleScalar,
    sfConstructibleIntegralScalarExtension, constructibleIntegralPullback,
    Functor.comp_obj, ObjectProperty.lift_obj_obj, ObjectProperty.ι_obj] using
    mixed_square_cancel (integralScalarExtension l E L ι Y)
    (integralComparisonComposition l E C eY.asIso.hom f K)
    (integralComparisonComposition l E C f eX.asIso.hom K)
    (integralComparisonComposition l L C eY.asIso.hom f
      ((integralComparisonConstructibleScalar l E L ι X).obj K))
    (integralComparisonComposition l L C f eX.asIso.hom
      ((integralComparisonConstructibleScalar l E L ι X).obj K))
    _ _ _ _ _ _ h₁ h₂ (ht (eY.asIso.hom ≫ f) (f ≫ eX.asIso.hom) h)

private theorem rational_square
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (a : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E eY.asIso.hom ≅
        constructibleIntegralPullback l E eX.asIso.hom ⋙ constructibleIntegralPullback l E f)
    (b : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E eY.asIso.hom ≅
        rationalDerivedPullback l E eX.asIso.hom ⋙ rationalDerivedPullback l E f)
    (hb : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfRationalConstructibleCategory l E X),
      HEq ((b E).hom.app K)
        ((sfRationalConstructibleLocalization l E Y).map ((a E).hom.app K.obj)))
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (hi : ∀ K : sfIntegralConstructibleCategory l E X,
      (integralScalarExtension l E L ι Y).map ((a E).hom.app K).hom ≫
        (integralPullbackScalarComparison l E L ι f
          ((constructibleIntegralPullback l E eX.asIso.hom).obj K)).hom.hom ≫
        (integralDerivedPullback l L f).map
          (integralPullbackScalarComparison l E L ι eX.asIso.hom K).hom.hom =
      (integralPullbackScalarComparison l E L ι eY.asIso.hom
          ((constructibleIntegralPullback l E f).obj K)).hom.hom ≫
        (integralDerivedPullback l L eY.asIso.hom).map
          (integralPullbackScalarComparison l E L ι f K).hom.hom ≫
        ((a L).hom.app ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K)).hom) :
    ∀ K : sfRationalConstructibleCategory l E X,
      (sfRationalScalarExtension l E Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
          ((b E).hom.app K) ≫
        (rationalPullbackScalarComparison l E L ι f).hom.app
          ((rationalDerivedPullback l E eX.asIso.hom).obj K) ≫
        (rationalDerivedPullback l L f).map
          ((rationalPullbackScalarComparison l E L ι eX.asIso.hom).hom.app K) =
      (rationalPullbackScalarComparison l E L ι eY.asIso.hom).hom.app
          ((rationalDerivedPullback l E f).obj K) ≫
        (rationalDerivedPullback l L eY.asIso.hom).map
          ((rationalPullbackScalarComparison l E L ι f).hom.app K) ≫
        (b L).hom.app
          ((sfRationalScalarExtension l E X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) := by
  intro K
  let T (Z : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Z
  let U (Z : Scheme.{u}) := sfRationalScalarExtension l E Z 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  have hp (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (J : sfRationalConstructibleCategory l A W) :
      (rationalDerivedPullback l A g).obj J =
        (sfRationalConstructibleLocalization l A V).obj
          ((constructibleIntegralPullback l A g).obj J.obj) :=
    (rationalDerivedPullback_existsUnique l A g).exists.choose_spec.2.1 J
  have hs (Z : Scheme.{u}) (J : sfRationalConstructibleCategory l E Z) :
      (sfRationalScalarExtension l E Z 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj J =
        (sfRationalConstructibleLocalization l L Z).obj ((T Z).obj J.obj) :=
    (sfRationalScalarExtension_existsUnique l E Z 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 J
  let aE := a E
  let aL := a L
  have haE : HEq ((b E).hom.app K)
      ((sfRationalConstructibleLocalization l E Y).map (aE.hom.app K.obj)) := hb E K
  have h₁ := (map_heq (U Y) (by simp only [Functor.comp_obj, hp,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, hp,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) haE).trans
    (scalar_map_localized l E L ι Y (aE.hom.app K.obj))
  have h₂ := (rationalPullbackScalarComparison_existsUnique l E L ι f).exists.choose_spec
    ((rationalDerivedPullback l E eX.asIso.hom).obj K)
  have hobj : ((rationalDerivedPullback l E eX.asIso.hom).obj K).obj =
      (constructibleIntegralPullback l E eX.asIso.hom).obj K.obj :=
    congrArg ScalarLocalization.obj (hp E eX.asIso.hom K)
  have h₂' : HEq
      ((rationalPullbackScalarComparison l E L ι f).hom.app
        ((rationalDerivedPullback l E eX.asIso.hom).obj K))
      ((sfRationalConstructibleLocalization l L Y).map
        (integralPullbackScalarComparison l E L ι f
          ((constructibleIntegralPullback l E eX.asIso.hom).obj K.obj)).hom) := by
    have hb : HEq ((rationalPullbackScalarComparison l E L ι f).hom.app
        ((rationalDerivedPullback l E eX.asIso.hom).obj K))
        ((sfRationalConstructibleLocalization l L Y).map
          (integralPullbackScalarComparison l E L ι f
            ((rationalDerivedPullback l E eX.asIso.hom).obj K).obj).hom) := by
      simpa only [rationalPullbackScalarComparison] using h₂
    exact hb.trans (dependent_heq (fun J ↦ (sfRationalConstructibleLocalization l L Y).map
      (integralPullbackScalarComparison l E L ι f J).hom) hobj)
  have hα {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (J : sfRationalConstructibleCategory l E W) :
      HEq ((rationalPullbackScalarComparison l E L ι g).hom.app J)
        ((sfRationalConstructibleLocalization l L V).map
          (integralPullbackScalarComparison l E L ι g J.obj).hom) := by
    simpa only [rationalPullbackScalarComparison] using
      (rationalPullbackScalarComparison_existsUnique l E L ι g).exists.choose_spec J
  have h₃ := (map_heq (rationalDerivedPullback l L f)
    (by simp only [Functor.comp_obj, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
    (hα eX.asIso.hom K)).trans
      (pullback_map_localized l L f
        (integralPullbackScalarComparison l E L ι eX.asIso.hom K.obj).hom)
  have h₄ := (rationalPullbackScalarComparison_existsUnique l E L ι eY.asIso.hom).exists.choose_spec
    ((rationalDerivedPullback l E f).obj K)
  have hobj₄ : ((rationalDerivedPullback l E f).obj K).obj =
      (constructibleIntegralPullback l E f).obj K.obj :=
    congrArg ScalarLocalization.obj (hp E f K)
  have h₄' : HEq
      ((rationalPullbackScalarComparison l E L ι eY.asIso.hom).hom.app
        ((rationalDerivedPullback l E f).obj K))
      ((sfRationalConstructibleLocalization l L Y).map
        (integralPullbackScalarComparison l E L ι eY.asIso.hom
          ((constructibleIntegralPullback l E f).obj K.obj)).hom) := by
    have hb : HEq ((rationalPullbackScalarComparison l E L ι eY.asIso.hom).hom.app
        ((rationalDerivedPullback l E f).obj K))
        ((sfRationalConstructibleLocalization l L Y).map
          (integralPullbackScalarComparison l E L ι eY.asIso.hom
            ((rationalDerivedPullback l E f).obj K).obj).hom) := by
      simpa only [rationalPullbackScalarComparison] using h₄
    exact hb.trans (dependent_heq (fun J ↦ (sfRationalConstructibleLocalization l L Y).map
      (integralPullbackScalarComparison l E L ι eY.asIso.hom J).hom) hobj₄)
  have h₅ := (map_heq (rationalDerivedPullback l L eY.asIso.hom)
    (by simp only [Functor.comp_obj, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
    (hα f K)).trans
      (pullback_map_localized l L eY.asIso.hom
        (integralPullbackScalarComparison l E L ι f K.obj).hom)
  have h₆ := hb L ((U X).obj K)
  have hobj₆ : ((U X).obj K).obj = (T X).obj K.obj :=
    congrArg ScalarLocalization.obj (hs X K)
  have h₆' : HEq
      ((b L).hom.app ((U X).obj K))
      ((sfRationalConstructibleLocalization l L Y).map
        (aL.hom.app ((T X).obj K.obj))) := by
    have hb : HEq ((b L).hom.app ((U X).obj K))
        ((sfRationalConstructibleLocalization l L Y).map
          (aL.hom.app ((U X).obj K).obj)) := by
      exact h₆
    exact hb.trans (dependent_heq (fun J ↦
      (sfRationalConstructibleLocalization l L Y).map (aL.hom.app J)) hobj₆)
  have hleft := heq_comp (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
    (by simp only [Functor.comp_obj, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) h₁
    (heq_comp (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
      (by simp only [Functor.comp_obj, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) h₂' h₃)
  have hright := heq_comp (by simp only [Functor.comp_obj, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
    (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) h₄'
    (heq_comp (by simp only [Functor.comp_obj, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
      (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) h₅ h₆')
  have hint : (T Y).map (aE.hom.app K.obj) ≫
      (integralPullbackScalarComparison l E L ι f
        ((constructibleIntegralPullback l E eX.asIso.hom).obj K.obj)).hom ≫
      (constructibleIntegralPullback l L f).map
        (integralPullbackScalarComparison l E L ι eX.asIso.hom K.obj).hom =
    (integralPullbackScalarComparison l E L ι eY.asIso.hom
        ((constructibleIntegralPullback l E f).obj K.obj)).hom ≫
      (constructibleIntegralPullback l L eY.asIso.hom).map
        (integralPullbackScalarComparison l E L ι f K.obj).hom ≫
      aL.hom.app ((T X).obj K.obj) := by
    apply ObjectProperty.hom_ext (sfIntegralConstructible l L Y)
    exact hi K.obj
  have hloc := congrArg (sfRationalConstructibleLocalization l L Y).map hint
  simp only [Functor.map_comp] at hloc
  exact eq_of_heq (hleft.trans ((heq_of_eq hloc).trans hright.symm))

-- Pasting a square is unchanged by natural isomorphisms of the transition functors.
private theorem conjugate_square
    {A₀ : Type a₀} {A₁ : Type a₁} {B₀ : Type b₀} {B₁ : Type b₁}
    [Category A₀] [Category A₁] [Category B₀] [Category B₁]
    (F : A₀ ⥤ B₀) (F' : A₁ ⥤ B₁)
    (G : A₀ ⥤ A₀) (G' : A₁ ⥤ A₁)
    (H : B₀ ⥤ B₀) (H' : B₁ ⥤ B₁)
    (TX SX : A₀ ⥤ A₁) (TY SY : B₀ ⥤ B₁)
    (tX : TX ≅ SX) (tY : TY ≅ SY)
    (αF : F ⋙ SY ≅ SX ⋙ F') (αG : G ⋙ SX ≅ SX ⋙ G')
    (αH : H ⋙ SY ≅ SY ⋙ H')
    (b : F ⋙ H ≅ G ⋙ F) (b' : F' ⋙ H' ≅ G' ⋙ F') (K : A₀)
    (hr : SY.map (b.hom.app K) ≫ αF.hom.app (G.obj K) ≫ F'.map (αG.hom.app K) =
      αH.hom.app (F.obj K) ≫ H'.map (αF.hom.app K) ≫ b'.hom.app (SX.obj K)) :
    TY.map (b.hom.app K) ≫
      (Functor.isoWhiskerLeft F tY ≪≫ αF ≪≫
        Functor.isoWhiskerRight tX.symm F').hom.app (G.obj K) ≫
      F'.map ((Functor.isoWhiskerLeft G tX ≪≫ αG ≪≫
        Functor.isoWhiskerRight tX.symm G').hom.app K) =
    ((Functor.isoWhiskerLeft H tY ≪≫ αH ≪≫
        Functor.isoWhiskerRight tY.symm H').hom.app (F.obj K) ≫
      H'.map ((Functor.isoWhiskerLeft F tY ≪≫ αF ≪≫
        Functor.isoWhiskerRight tX.symm F').hom.app K)) ≫
      b'.hom.app (TX.obj K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← F'.map_comp_assoc, tX.inv_hom_id_app, F'.map_id, Category.id_comp]
  rw [← H'.map_comp_assoc, tY.inv_hom_id_app, H'.map_id, Category.id_comp]
  rw [reassoc_of% (tY.hom.naturality (b.hom.app K))]
  rw [reassoc_of% hr]
  have nb := b'.hom.naturality (tX.inv.app K)
  dsimp only [Functor.comp_map] at nb
  rw [nb]

/-- The localized normalized integral square satisfies the scalar transition square.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md,
Weil-structures paragraph; steps 7--9 of the automorphism stage-equivalence proof
(blueprint: lem-sf-automorphism-square-stage-compatibility).

Proof: first use the normalized mixed scalar/composition equation for the pairs
(eY,f) and (f,eX). Their composite scheme maps are equal by h. Cancel the two
invertible compositors; the equality gives compatibility of the integral square
with the two composite scalar comparisons. The representative normalization of
IntegralComparisonSystem identifies these scalar comparisons with the prescribed
integralPullbackScalarComparison, independently of the chosen system C.
Apply rational localization to this full morphism equation. The component formula
hb identifies the square components with the localized integral components. The
prescribed object and pure-tensor formulas for rational pullback and coefficient
extension identify the other four arrows with their localized integral maps.
Functoriality of localization then gives the raw rational scalar equation.
Finally substitute commonStagePullbackTransition: each is the raw scalar comparison
conjugated by operationStageTransitionIso. Naturality of these identifications
moves them past the square components. The two intermediate identifications cancel,
leaving exactly the equation below. This includes identity fields, empty schemes,
and semilinear automorphisms, and uses no faithfulness of finite reduction. -/
theorem automorphismSquareStageCompatibility
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom)
    (a : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E eY.asIso.hom ≅
        constructibleIntegralPullback l E eX.asIso.hom ⋙ constructibleIntegralPullback l E f)
    (ha : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfIntegralConstructibleCategory l E X),
      ((a E).hom.app K).hom =
        (integralComparisonComposition l E C eY.asIso.hom f K).inv ≫
          eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
            (integralComparisonComposition l E C f eX.asIso.hom K).hom)
    (b : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E eY.asIso.hom ≅
        rationalDerivedPullback l E eX.asIso.hom ⋙ rationalDerivedPullback l E f)
    (hb : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfRationalConstructibleCategory l E X),
      HEq ((b E).hom.app K)
        ((sfRationalConstructibleLocalization l E Y).map ((a E).hom.app K.obj)))
    (E L : Index l Ω) (w : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T w).map
        ((b (Coefficient.{u} l Ω E)).hom.app K) ≫
      (commonStagePullbackTransition l Ω f w).hom.app
        ((rationalDerivedPullback l (Coefficient.{u} l Ω E) eX.asIso.hom).obj K) ≫
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map
        ((commonStagePullbackTransition l Ω eX.asIso.hom w).hom.app K) =
    ((commonStagePullbackTransition l Ω eY.asIso.hom w).hom.app
        ((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).obj K) ≫
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) eY.asIso.hom).map
        ((commonStagePullbackTransition l Ω f w).hom.app K)) ≫
      (b (Coefficient.{u} l Ω L)).hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T w).obj K) := by
  let ι := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L w
  have hi (J : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) :=
    integral_square l C f eX eY h a ha
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) ι J
  have hi' (J : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) :
      (integralScalarExtension l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) ι Y).map
          ((a (Coefficient.{u} l Ω E)).hom.app J).hom ≫
        (integralPullbackScalarComparison l _ _ ι f
          ((constructibleIntegralPullback l _ eX.asIso.hom).obj J)).hom.hom ≫
        (integralDerivedPullback l _ f).map
          (integralPullbackScalarComparison l _ _ ι eX.asIso.hom J).hom.hom =
      (integralPullbackScalarComparison l _ _ ι eY.asIso.hom
          ((constructibleIntegralPullback l _ f).obj J)).hom.hom ≫
        (integralDerivedPullback l _ eY.asIso.hom).map
          (integralPullbackScalarComparison l _ _ ι f J).hom.hom ≫
        ((a (Coefficient.{u} l Ω L)).hom.app
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) ι X).obj J)).hom := by
    simp only [scalar_comparison_hom l _ _ ι C]
    exact hi J
  have hr := rational_square l f eX eY a b hb
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) ι hi' K
  exact conjugate_square
    (rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) f)
    (rationalDerivedPullback l (Coefficient.{u} l Ω E) eX.asIso.hom)
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) eX.asIso.hom)
    (rationalDerivedPullback l (Coefficient.{u} l Ω E) eY.asIso.hom)
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) eY.asIso.hom)
    _ _ _ _ (operationStageTransitionIso l Ω X E L w)
    (operationStageTransitionIso l Ω Y E L w)
    (rationalPullbackScalarComparison l _ _ ι f)
    (rationalPullbackScalarComparison l _ _ ι eX.asIso.hom)
    (rationalPullbackScalarComparison l _ _ ι eY.asIso.hom)
    (b (Coefficient.{u} l Ω E)) (b (Coefficient.{u} l Ω L)) K hr

end WeilConjectures
