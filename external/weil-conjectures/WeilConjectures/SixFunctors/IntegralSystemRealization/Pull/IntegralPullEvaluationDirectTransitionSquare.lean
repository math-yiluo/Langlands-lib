/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations

/-! The direct-image transition equation underlying the pullback evaluation square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem transfer_inv_sections
    {A B D C : Type*} [Category A] [Category B] [Category D] [Category C]
    {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}}
    {T T₀ : A ⥤ B} {S S₀ : D ⥤ SheafOfModules.{u + 1} R}
    {G : A ⥤ D} {G' : B ⥤ SheafOfModules.{u + 1} R}
    (hS : S = S₀) (hT : T = T₀)
    (e : T ⋙ G' ≅ G ⋙ S) (e₀ : T₀ ⋙ G' ≅ G ⋙ S₀) (he : HEq e e₀)
    (h : ∀ (N : A) (U : Cᵒᵖ) (x : ((G ⋙ S₀).obj N).val.obj U),
      HEq ((e₀.inv.app N).val.app U x) x) :
    ∀ (N : A) (U : Cᵒᵖ) (x : ((G ⋙ S).obj N).val.obj U),
      HEq ((e.inv.app N).val.app U x) x := by
  subst S₀ T₀
  cases eq_of_heq he
  exact h

private theorem canonical_comparison_sections
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B)
    (N : proEtaleRingModules X (proEtaleConstantRing X B)) (U : Y.ProEtᵒᵖ)
    (x : ((proEtaleConstantModuleDirectImage f B ⋙
      proEtaleCoefficientRestrictScalars Y φ).obj N).val.obj U) :
    HEq (((proEtaleCoefficientDirectImageComparison f φ).hom.app N).val.app U x) x := by
  exact heq_of_eq
    ((proEtaleCoefficientDirectImageComparison_existsUnique f φ).choose_spec.1 N U x)

attribute [local irreducible] proEtaleCoefficientDirectImageComparison

private theorem adjacent_restriction_eq (W : Scheme.{u}) (n : ℕ) :
    proEtaleCoefficientRestrictScalars W (Padic.coefficientExtensionTransition l E (n + 1)) =
      normalizedDVRModuleRes l E W (Nat.le_succ n) :=
  congrArg (fun q : integralCoefficientSheaf l E W (n + 1) ⟶
      integralCoefficientSheaf l E W n ↦ SheafOfModules.restrictScalars.{u + 1} q)
    (Functor.ofOpSequence_map_homOfLE_succ (integralCoefficientSheafTransition l E W) n).symm

private theorem scalar_comparison_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n))
    (hr : HEq r (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm) :
    ∀ (N : normalizedDVRModules l E X n) (U : Y.ProEtᵒᵖ)
      (x : ((proEtaleConstantModuleDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          normalizedDVRModuleRes l E Y (Nat.le_succ n)).obj N).val.obj U),
      HEq ((r.inv.app N).val.app U x) x := by
  apply transfer_inv_sections
    (adjacent_restriction_eq l E Y n).symm
    (adjacent_restriction_eq l E X n).symm
    r (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm hr
  intro N U x
  exact canonical_comparison_sections f
    (Padic.coefficientExtensionTransition l E (n + 1)) N U x

private theorem direct_evaluation_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∀ (N : coefficientSequenceModules l E X) (U : Y.ProEtᵒᵖ)
      (x : ((pullbackTensorSequenceDirect l E f ⋙
        coefficientSequenceEvaluation l E Y n).obj N).val.obj U),
      HEq (((pullbackTensorSequenceDirectEvaluation l E f n).hom.app N).val.app U x) x := by
  intro N U x
  exact (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec
    N U.unop x

attribute [local irreducible] constantSheaf presheafToSheaf Functor.leftAdjoint
  coefficientSequenceCommRingSystem coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSheaf pullbackTensorSequenceRing
  pullbackTensorSequenceDirectEvaluation
attribute [local implicit_reducible] coefficientSequenceEvaluation
  pullbackTensorSequenceDirect pullbackTensorSequenceBase coefficientProEtaleModuleDirectImage
  proEtaleConstantModuleDirectImage integralCoefficientSheaf integralCoefficientCommRingSheaf
  SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

private theorem ab_conjugate_apply_heq
    {A B A' B' : AddCommGrpCat.{u + 1}} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g)
    (x : A) (y : A') (hxy : HEq x y) : HEq (f x) (g y) := by
  subst A' B'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst g
  have hx : x = y := eq_of_heq hxy
  subst y
  rfl

private theorem transition_section (W : Scheme.{u})
    {m n : ℕ} (h : n ≤ m) (N : coefficientSequenceModules l E W)
    (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W m).obj N).val.obj U) :
    ((coefficientSequenceTransition l E W h).app N).val.app U x =
      N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  have ht := (coefficientSequenceTransition_exists l E W h).exists.choose_spec N U
  have hh := ab_conjugate_apply_heq
    (coefficientSequenceEvaluationAb_eq l E W N m U)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W N h U)
    ((forget₂ (ModuleCat.{u + 1} ((integralCoefficientSheaf l E W m).obj.obj U))
      AddCommGrpCat).map (((coefficientSequenceTransition l E W h).app N).val.app U))
    (N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) ht x x (HEq.refl x)
  exact eq_of_heq hh

attribute [local irreducible] coefficientSequenceTransition

private theorem system_transition_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (N : coefficientSequenceModules l E X) (U : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E Y m).obj
      ((pullbackTensorSequenceDirect l E f).obj N)).val.obj U)
    (y : ((coefficientSequenceEvaluation l E X m).obj N).val.obj
      ((proEtaleBaseChange f).op.obj U)) (hxy : HEq x y) :
    HEq (((coefficientSequenceTransition l E Y h).app
      ((pullbackTensorSequenceDirect l E f).obj N)).val.app U x)
      (((coefficientSequenceTransition l E X h).app N).val.app
        ((proEtaleBaseChange f).op.obj U) y) := by
  have hh : x = y := eq_of_heq hxy
  subst y
  apply heq_of_eq
  refine (transition_section l E Y h
    ((pullbackTensorSequenceDirect l E f).obj N) U x).trans ?_
  refine Eq.trans ?_ (transition_section l E X h N
    ((proEtaleBaseChange f).op.obj U) x).symm
  change N.val.map ((pullbackTensorSequenceBase f).map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop))).op x =
    N.val.map (Prod.mkHom (homOfLE h)
      (𝟙 ((proEtaleBaseChange f).op.obj U).unop)).op x
  have hm : (pullbackTensorSequenceBase f).map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)) =
      Prod.mkHom (homOfLE h) (𝟙 ((proEtaleBaseChange f).obj U.unop)) := by
    dsimp only [pullbackTensorSequenceBase, Functor.prod_map, Functor.id_map]
    exact congrArg (fun k ↦ Prod.mkHom (homOfLE h) k)
      ((proEtaleBaseChange f).map_id U.unop)
  exact N.val.congr_map_apply (congrArg Quiver.Hom.op hm) x

private theorem restrict_identity
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (φ : R ⟶ S)
    {M N : SheafOfModules.{u + 1} S} (a : M ⟶ N)
    (ha : ∀ (U : Cᵒᵖ) (x : M.val.obj U), HEq (a.val.app U x) x)
    (U : Cᵒᵖ) (x : ((SheafOfModules.restrictScalars φ).obj M).val.obj U) :
    HEq ((((SheafOfModules.restrictScalars φ).map a).val.app U) x) x :=
  ha U x

private theorem pushforward_apply_heq
    {C C' : Type*} [Category C] [Category C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'} {F : C ⥤ C'}
    [F.IsContinuous J J'] {R : Sheaf J' RingCat.{u + 1}} {S : Sheaf J RingCat.{u + 1}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J J').obj R)
    {M N : SheafOfModules.{u + 1} R} (a : M ⟶ N) (U : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward φ).obj M).val.obj U)
    (y : M.val.obj (Opposite.op (F.obj U.unop))) (hxy : HEq x y) :
    HEq ((((SheafOfModules.pushforward φ).map a).val.app U) x)
      (a.val.app (Opposite.op (F.obj U.unop)) y) := by
  have hh : x = y := eq_of_heq hxy
  subst y
  rfl

private theorem pushforward_element
    {C C' : Type*} [Category C] [Category C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'} {F : C ⥤ C'}
    [F.IsContinuous J J'] {R : Sheaf J' RingCat.{u + 1}} {S : Sheaf J RingCat.{u + 1}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J J').obj R)
    (M : SheafOfModules.{u + 1} R) (U : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward φ).obj M).val.obj U) :
    ∃ y : M.val.obj (Opposite.op (F.obj U.unop)), HEq x y :=
  ⟨x, HEq.refl x⟩

private theorem sheaf_square_identity
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M₀ M₁ M₂ M₃ M₄ : SheafOfModules.{u + 1} R}
    (f₁ : M₀ ⟶ M₁) (f₂ : M₁ ⟶ M₂) (f₃ : M₂ ⟶ M₃)
    (g₁ : M₀ ⟶ M₄) (g₂ : M₄ ⟶ M₃)
    (hf₂ : ∀ (U : Cᵒᵖ) (x : M₁.val.obj U), HEq (f₂.val.app U x) x)
    (hf₃ : ∀ (U : Cᵒᵖ) (x : M₂.val.obj U), HEq (f₃.val.app U x) x)
    (hg₁ : ∀ (U : Cᵒᵖ) (x : M₀.val.obj U), HEq (g₁.val.app U x) x)
    (hs : ∀ (U : Cᵒᵖ) (x : M₀.val.obj U) (y : M₄.val.obj U),
      HEq x y → HEq (f₁.val.app U x) (g₂.val.app U y)) :
    f₁ ≫ f₂ ≫ f₃ = g₁ ≫ g₂ := by
  ext U x
  exact eq_of_heq ((hf₃ U _).trans
    ((hf₂ U _).trans (hs U x _ (hg₁ U x).symm)))

/-- Direct image and evaluation commute with the adjacent coefficient transition.
Source: Zheng Construction 4.1, the section calculation preceding Lemma 4.10;
Stacks Tags 03DI and 0941.
(blueprint: stage3-integral-pull-evaluation-direct-transition-square).

Proof: evaluate both composites at a pro-étale object U and a section x. Each direct
evaluation comparison is the identity on underlying sections by its normalization.
Transport hr along the equality between normalizedDVRQuotient and the adjacent
integralCoefficientSheafTransition. The inverse of r is then the coefficient direct-image
comparison, also identity on sections. Each coefficient transition is the presheaf
restriction along the horizontal sequence arrow. The product base-change functor
sends that arrow to the horizontal arrow at the base-changed object, so both paths
give the same restriction of x. Extensionality of module-sheaf morphisms concludes.
This argument also applies when n = 0 and to the zero module. -/
theorem integralPullEvaluation_directTransitionSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n))
    (hr : HEq r (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm) :
    let d : pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
        coefficientSequenceEvaluation l E X n ⋙
          proEtaleConstantModuleDirectImage f (finiteCoefficientRing l E (n + 1)) :=
      pullbackTensorSequenceDirectEvaluation l E f n
    let d' : pullbackTensorSequenceDirect l E f ⋙
        coefficientSequenceEvaluation l E Y (n + 1) ≅
        coefficientSequenceEvaluation l E X (n + 1) ⋙
          proEtaleConstantModuleDirectImage f (finiteCoefficientRing l E (n + 2)) :=
      pullbackTensorSequenceDirectEvaluation l E f (n + 1)
    ∀ N : coefficientSequenceModules l E X,
      (coefficientSequenceTransition l E Y (Nat.le_succ n)).app
          ((pullbackTensorSequenceDirect l E f).obj N) ≫
        (normalizedDVRModuleRes l E Y (Nat.le_succ n)).map (d.hom.app N) ≫
        r.inv.app ((coefficientSequenceEvaluation l E X n).obj N) =
      d'.hom.app N ≫
        (proEtaleConstantModuleDirectImage f (finiteCoefficientRing l E (n + 2))).map
          ((coefficientSequenceTransition l E X (Nat.le_succ n)).app N) := by
  dsimp only
  intro N
  apply sheaf_square_identity
  · intro U x
    exact restrict_identity (normalizedDVRQuotient l E Y (Nat.le_succ n))
      ((pullbackTensorSequenceDirectEvaluation l E f n).hom.app N)
      (direct_evaluation_sections l E f n N) U x
  · exact scalar_comparison_sections l E f n r hr
      ((coefficientSequenceEvaluation l E X n).obj N)
  · exact direct_evaluation_sections l E f (n + 1) N
  · intro U x y hxy
    obtain ⟨z, hz⟩ := pushforward_element _
      ((coefficientSequenceEvaluation l E X (n + 1)).obj N) U y
    exact (system_transition_sections l E f (Nat.le_succ n) N U x z
      (hxy.trans hz)).trans
      (pushforward_apply_heq _ ((coefficientSequenceTransition l E X (Nat.le_succ n)).app N)
        U y z hz).symm

end WeilConjectures.IntegralSystemRealization
