/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison

/-! # Associativity of a fully faithful integral lift

Source: Stacks Project, Tag 0D6D and the naturality calculation in step 6 of
lem-pod-integral-pullback-composition
(blueprint: lem-pod-integral-system-pullback-lift-associativity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option allowUnsafeReducibility true in
attribute [local irreducible] finiteSystemDerivedPullback finiteSystemDerivedEvaluation
  integralSystemReduction integralSystemReductionEvaluation
  finiteSystemDerivedComposition constructibleIntegralPullback integralDerivedPullback

private theorem liftAssociativity
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (R₂ : C₂ ⥤ D₂) (R₃ : C₃ ⥤ D₃)
    [R₃.Faithful]
    (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₂₃ : C₂ ⥤ C₃)
    (F₀₂ : C₀ ⥤ C₂) (F₁₃ : C₁ ⥤ C₃) (F₀₃ F₀₃' : C₀ ⥤ C₃)
    (U₀₁ : D₀ ⥤ D₁) (U₁₂ : D₁ ⥤ D₂) (U₂₃ : D₂ ⥤ D₃)
    (U₀₂ : D₀ ⥤ D₂) (U₁₃ : D₁ ⥤ D₃) (U₀₃ U₀₃' : D₀ ⥤ D₃)
    (β₀₁ : F₀₁ ⋙ R₁ ≅ R₀ ⋙ U₀₁) (β₁₂ : F₁₂ ⋙ R₂ ≅ R₁ ⋙ U₁₂)
    (β₂₃ : F₂₃ ⋙ R₃ ≅ R₂ ⋙ U₂₃) (β₀₂ : F₀₂ ⋙ R₂ ≅ R₀ ⋙ U₀₂)
    (β₁₃ : F₁₃ ⋙ R₃ ≅ R₁ ⋙ U₁₃) (β₀₃ : F₀₃ ⋙ R₃ ≅ R₀ ⋙ U₀₃)
    (β₀₃' : F₀₃' ⋙ R₃ ≅ R₀ ⋙ U₀₃')
    (c₀₂ : F₀₂ ≅ F₀₁ ⋙ F₁₂) (c₁₃ : F₁₃ ≅ F₁₂ ⋙ F₂₃)
    (c₀₃ : F₀₃ ≅ F₀₂ ⋙ F₂₃) (c₀₃' : F₀₃' ≅ F₀₁ ⋙ F₁₃)
    (a₀₂ : U₀₂ ≅ U₀₁ ⋙ U₁₂) (a₁₃ : U₁₃ ≅ U₁₂ ⋙ U₂₃)
    (a₀₃ : U₀₃ ≅ U₀₂ ⋙ U₂₃) (a₀₃' : U₀₃' ≅ U₀₁ ⋙ U₁₃)
    (eF : F₀₃ ⟶ F₀₃') (eU : U₀₃ ⟶ U₀₃') (K : C₀)
    (h₀₂ : R₂.map (c₀₂.hom.app K) ≫ β₁₂.hom.app (F₀₁.obj K) ≫
      U₁₂.map (β₀₁.hom.app K) = β₀₂.hom.app K ≫ a₀₂.hom.app (R₀.obj K))
    (h₁₃ : R₃.map (c₁₃.hom.app (F₀₁.obj K)) ≫
      β₂₃.hom.app (F₁₂.obj (F₀₁.obj K)) ≫ U₂₃.map (β₁₂.hom.app (F₀₁.obj K)) =
      β₁₃.hom.app (F₀₁.obj K) ≫ a₁₃.hom.app (R₁.obj (F₀₁.obj K)))
    (h₀₃ : R₃.map (c₀₃.hom.app K) ≫ β₂₃.hom.app (F₀₂.obj K) ≫
      U₂₃.map (β₀₂.hom.app K) = β₀₃.hom.app K ≫ a₀₃.hom.app (R₀.obj K))
    (h₀₃' : R₃.map (c₀₃'.hom.app K) ≫ β₁₃.hom.app (F₀₁.obj K) ≫
      U₁₃.map (β₀₁.hom.app K) = β₀₃'.hom.app K ≫ a₀₃'.hom.app (R₀.obj K))
    (he : R₃.map (eF.app K) ≫ β₀₃'.hom.app K =
      β₀₃.hom.app K ≫ eU.app (R₀.obj K))
    (ha : a₀₃.hom.app (R₀.obj K) ≫ U₂₃.map (a₀₂.hom.app (R₀.obj K)) =
      eU.app (R₀.obj K) ≫ a₀₃'.hom.app (R₀.obj K) ≫
        a₁₃.hom.app (U₀₁.obj (R₀.obj K))) :
    c₀₃.hom.app K ≫ F₂₃.map (c₀₂.hom.app K) =
      eF.app K ≫ c₀₃'.hom.app K ≫ c₁₃.hom.app (F₀₁.obj K) := by
  apply R₃.map_injective
  simp only [Functor.map_comp]
  apply (cancel_mono (β₂₃.hom.app (F₁₂.obj (F₀₁.obj K)))).1
  apply (cancel_mono (U₂₃.map (β₁₂.hom.app (F₀₁.obj K)))).1
  apply (cancel_mono (U₂₃.map (U₁₂.map (β₀₁.hom.app K)))).1
  simp only [Category.assoc]
  have hn := β₂₃.hom.naturality (c₀₂.hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hm := congrArg U₂₃.map h₀₂
  simp only [Functor.map_comp] at hm
  rw [hm, reassoc_of% h₀₃, reassoc_of% h₁₃]
  have hn' := a₁₃.hom.naturality (β₀₁.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn'
  rw [← hn', reassoc_of% h₀₃', reassoc_of% he, ha]

private theorem comparisonTransport
    {I : Sort*} {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) (F : I → C) (U : I → D) (b : ∀ i, R.obj (F i) ⟶ U i)
    {i j : I} (e : i = j) :
    R.map (eqToHom (congrArg F e)) ≫ b j = b i ≫ eqToHom (congrArg U e) := by
  subst e
  simp

/-- Any lift satisfying the defining whole-system equation is associative.
This concerns a fixed lift; it asserts neither existence nor a reduction formula.
Source: Stacks Tag 0D6D; original integral composition proof step 6
(blueprint: lem-pod-integral-system-pullback-lift-associativity).

Proof: apply faithful coherent reduction to the two integral composites. Postcompose
both with beta_j at F_h F_k K, then U_j(beta_h), then U_j U_h(beta_k).
These are invertible. Naturality of beta_j and the defining equation for (h,k)
turn the first composite into beta_(j,hk) followed by a_(j,hk) and U_j(a_(h,k)).
For the second composite, the defining equation for (j,h), naturality of a_(j,h)
at beta_k, and the defining equation for (jh,k) give beta_(jh,k) followed by
a_(jh,k) and a_(j,h) at U_k(RK). Naturality with respect to the equality
(j >> h) >> k = j >> (h >> k) transports beta across the displayed eqToHom.
The whole-system associativity clause of finiteSystemPullbackCoherence identifies
the two resulting maps. Cancel the common invertible postcomposition and use
integralSystemReduction_fullyFaithful to reflect their equality. No equality of
derived maps is inferred merely from their separate finite evaluations. -/
theorem integralSystemPullbackLift_associativity
    (β : ∀ {X Y : Scheme.{u}}
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y),
      constructibleIntegralPullback l E f ⋙ integralSystemReduction l E X ≅
        integralSystemReduction l E Y ⋙
          finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E) f)
    (c : ∀ {V W Z : Scheme.{u}}
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)] (h : Z ⟶ W) (k : W ⟶ V),
      constructibleIntegralPullback l E (h ≫ k) ≅
        constructibleIntegralPullback l E k ⋙ constructibleIntegralPullback l E h)
    (hc : ∀ {V W Z : Scheme.{u}}
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)] (h : Z ⟶ W) (k : W ⟶ V)
      (K : sfIntegralConstructibleCategory l E V),
      (integralSystemReduction l E Z).map ((c h k).hom.app K) ≫
          (β h).hom.app ((constructibleIntegralPullback l E k).obj K) ≫
          (finiteSystemDerivedPullback (integralSystemRings l E)
            (integralSystemTransition l E) h).map ((β k).hom.app K) =
        (β (h ≫ k)).hom.app K ≫
          (finiteSystemDerivedComposition (integralSystemRings l E)
            (integralSystemTransition l E) h k).hom.app ((integralSystemReduction l E V).obj K)) :
    ∀ {V W Z Y : Scheme.{u}}
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)]
      [∀ y : Y, Invertible (l : Y.residueField y)]
      (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V)
      (K : sfIntegralConstructibleCategory l E V),
      (c j (h ≫ k)).hom.app K ≫
          (constructibleIntegralPullback l E j).map ((c h k).hom.app K) =
        eqToHom (congrArg
          (fun f : Y ⟶ V ↦ (constructibleIntegralPullback l E f).obj K)
          (Category.assoc j h k).symm) ≫
          (c (j ≫ h) k).hom.app K ≫
            (c j h).hom.app ((constructibleIntegralPullback l E k).obj K) := by
  classical
  let A := integralSystemRings l E
  let τ := integralSystemTransition l E
  let R := integralSystemReduction l E
  let U {X Y : Scheme.{u}} (f : X ⟶ Y) := finiteSystemDerivedPullback A τ f
  intro V W Z Y hV hW hZ hY j h k K
  let : (R Y).Faithful := (integralSystemReduction_fullyFaithful l E Y).2
  have result := liftAssociativity
    (C₀ := sfIntegralConstructibleCategory l E V)
    (C₁ := sfIntegralConstructibleCategory l E W)
    (C₂ := sfIntegralConstructibleCategory l E Z)
    (C₃ := sfIntegralConstructibleCategory l E Y)
    (D₀ := finiteSystemDerived A τ V) (D₁ := finiteSystemDerived A τ W)
    (D₂ := finiteSystemDerived A τ Z) (D₃ := finiteSystemDerived A τ Y)
    (R V) (R W) (R Z) (R Y)
    (constructibleIntegralPullback l E k) (constructibleIntegralPullback l E h)
    (constructibleIntegralPullback l E j) (constructibleIntegralPullback l E (h ≫ k))
    (constructibleIntegralPullback l E (j ≫ h))
    (constructibleIntegralPullback l E (j ≫ (h ≫ k)))
    (constructibleIntegralPullback l E ((j ≫ h) ≫ k))
    (U k) (U h) (U j) (U (h ≫ k)) (U (j ≫ h))
    (U (j ≫ (h ≫ k))) (U ((j ≫ h) ≫ k))
    (@β W V hW hV k) (@β Z W hZ hW h) (@β Y Z hY hZ j)
    (@β Z V hZ hV (h ≫ k)) (@β Y W hY hW (j ≫ h))
    (@β Y V hY hV (j ≫ (h ≫ k))) (@β Y V hY hV ((j ≫ h) ≫ k))
    (@c V W Z hV hW hZ h k) (@c W Z Y hW hZ hY j h)
    (@c V Z Y hV hZ hY j (h ≫ k)) (@c V W Y hV hW hY (j ≫ h) k)
    (finiteSystemDerivedComposition A τ h k) (finiteSystemDerivedComposition A τ j h)
    (finiteSystemDerivedComposition A τ j (h ≫ k))
    (finiteSystemDerivedComposition A τ (j ≫ h) k)
    (eqToHom (congrArg (fun f : Y ⟶ V ↦ constructibleIntegralPullback l E f)
      (Category.assoc j h k).symm))
    (eqToHom (congrArg (fun f : Y ⟶ V ↦ U f) (Category.assoc j h k).symm))
    K (@hc V W Z hV hW hZ h k K)
    (@hc W Z Y hW hZ hY j h ((constructibleIntegralPullback l E k).obj K))
    (@hc V Z Y hV hZ hY j (h ≫ k) K) (@hc V W Y hV hW hY (j ≫ h) k K) (by
      simpa only [eqToHom_app] using comparisonTransport (R Y)
        (fun f : Y ⟶ V ↦ (constructibleIntegralPullback l E f).obj K)
        (fun f : Y ⟶ V ↦ (U f).obj ((R V).obj K))
        (fun f ↦ (@β Y V hY hV f).hom.app K) (Category.assoc j h k).symm) (by
      have ha := (finiteSystemPullbackCoherence A τ j h k).2.2.2 ((R V).obj K)
      have hb := congrArg (fun z ↦
        eqToHom (congrArg (fun f : Y ⟶ V ↦ (U f).obj ((R V).obj K))
          (Category.assoc j h k).symm) ≫ z) ha
      simpa only [← Category.assoc, eqToHom_app, eqToHom_trans, eqToHom_refl,
        Category.id_comp] using hb)
  exact result

end WeilConjectures
