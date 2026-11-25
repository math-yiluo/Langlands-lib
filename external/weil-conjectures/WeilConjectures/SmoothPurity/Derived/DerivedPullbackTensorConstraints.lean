/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraintCore

import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorCoherentReduction
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorUnit
import WeilConjectures.SmoothPurity.Common.CommonStageUnitorTransport
import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence

/-! # Normalized higher pullback tensor constraints

The unchanged constructions and structural predicates from the parent module.
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.privateModule false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v r

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Preserve the cached additive-group data while comparing stage Hom types.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

-- Match the category-wrapper proof context used by DerivedPullbackTensorHom.
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

private theorem coefficientPrime_isUnit (l : ℕ) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] : IsUnit (l : Γ(W, ⊤)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply RingedSpace.isUnit_of_isUnit_germ W.toSheafedSpace ⊤
    intro x hx
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (isUnit_of_invertible (l : W.residueField x)).ne_zero

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  integralCoefficientLinear integralScalarConstant sfIntegralCoefficientLinear
  sfIntegralConstructibleLinear
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  commonStageTensorComparison commonStagePullbackComparison
  operationStageTransitionIso commonStageDerivedTensor commonStageDerivedPullback

private theorem existsUnique_iso_of_eq {C : Type*} [Category* C]
    {A B A' B' : C} (hA : A = A') (hB : B = B') (e : A' ≅ B') :
    ∃! d : A ≅ B, HEq d.hom e.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    subst A'
    subst B'
    exact ⟨e, HEq.rfl, fun d hd ↦ Iso.ext (eq_of_heq hd)⟩

private theorem existsUnique_iso_of_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {A B : C} (e : F.obj A ≅ F.obj B) :
    ∃! d : A ≅ B, F.map d.hom = e.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    refine ⟨F.preimageIso e, F.map_preimage _, ?_⟩
    intro d hd
    exact Iso.ext (F.map_injective (hd.trans (F.map_preimage e.hom).symm))

private theorem existsUnique_iso_of_map_comp {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {A B : C} {T : D}
    (a : F.obj A ≅ T) (b : F.obj B ≅ T) :
    ∃! d : A ≅ B, F.map d.hom ≫ b.hom = a.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨d, hd, hu⟩ := existsUnique_iso_of_map F (a ≪≫ b.symm)
    refine ⟨d, ?_, ?_⟩
    · change F.map d.hom ≫ b.hom = a.hom
      rw [hd]
      simp
    · intro e he
      apply hu
      exact (Iso.eq_comp_inv b).mpr he

private theorem existsUnique_iso_of_map_constraints {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {A B : C} {U V W T : D}
    (a₁ : F.obj A ≅ U) (a₂ : U ≅ V) (a₃ : V ≅ T)
    (b₁ : F.obj B ≅ W) (b₂ : W ≅ T) :
    ∃! d : A ≅ B, F.map d.hom ≫ b₁.hom ≫ b₂.hom =
      a₁.hom ≫ a₂.hom ≫ a₃.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simpa only [Iso.trans_hom, Category.assoc] using
      existsUnique_iso_of_map_comp F (a₁ ≪≫ a₂ ≪≫ a₃) (b₁ ≪≫ b₂)

private theorem existsUnique_iso_of_map_constraint {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {A B : C} {U T : D} (a₁ : F.obj A ≅ U) (a₂ : U ≅ T) (b : F.obj B ≅ T) :
    ∃! d : A ≅ B, F.map d.hom ≫ b.hom = a₁.hom ≫ a₂.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact existsUnique_iso_of_map_comp F (a₁ ≪≫ a₂) b

private def closedTensorUnitIso {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S T : CoefficientClosedStructure H) :
    S.monoidal.tensorUnit ≅ T.monoidal.tensorUnit :=
  (T.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    ((T.adjunction T.monoidal.tensorUnit).leftAdjointUniq
      (S.adjunction T.monoidal.tensorUnit)).app S.monoidal.tensorUnit ≪≫
    S.monoidal.leftUnitor T.monoidal.tensorUnit

private theorem map_localized_heq
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (F : C ⥤ D) (F' : C' ⥤ D') (Q : C ⥤ C') (R : D ⥤ D')
    (hF : ∀ {A B : C} (f : A ⟶ B), HEq (F'.map (Q.map f)) (R.map (F.map f)))
    {A B : C'} {A' B' : C} (hA : A = Q.obj A') (hB : B = Q.obj B')
    (f : A ⟶ B) (g : A' ⟶ B') (hfg : HEq f (Q.map g)) :
    HEq (F'.map f) (R.map (F.map g)) := by
  subst A B
  cases hfg
  exact hF g

section CoherentReductionCache
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def coherentReduction (W : Scheme.{u}) :
    sfIntegralConstructibleCategory l E W ⥤ coefficientSequenceDerived l E W :=
  (sfIntegralConstructible l E W).ι ⋙ (pullbackTensorCalculus l E W).reduction
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentReduction_fullyFaithful (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    (coherentReduction l E W).Full ∧ (coherentReduction l E W).Faithful := by
  simpa only [coherentReduction, integralSystemReduction, pullbackTensorCalculus] using
    integralSystemReduction_fullyFaithful l E W
end CoherentReductionCache

section HigherCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralComparison_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    canonicalIntegralPullbackTensor_reduction l E f M N := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let := ((pullbackTensorComparisonCounits l E f) M N).1
    let := ((pullbackTensorComparisonCounits l E f) M N).2.1
    let := ((pullbackTensorComparisonCounits l E f) M N).2.2
    have hh := reduction_comparison
      (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E X)
      (pullbackTensorCalculus l E X).adjunction
      (pullbackTensorCalculus l E Y).reduction (coefficientSequenceLimit l E Y)
      (pullbackTensorCalculus l E Y).adjunction
      (integralDerivedPullback l E f) (pullbackTensorSequenceDerived l E f)
      (integralCompletedTensor l E Y) (integralCompletedTensor l E X)
      (pullbackTensorCalculus l E Y).systemClosed.tensor
      (pullbackTensorCalculus l E X).systemClosed.tensor
      (pullbackTensorIntegralPullbackModel l E f)
      (pullbackTensorIntegralTensorModel l E Y)
      (pullbackTensorIntegralTensorModel l E X)
      (pullbackTensorSystemComparison l E f) M.obj N.obj
    unfold canonicalIntegralPullbackTensor_reduction
    dsimp only [canonicalIntegralPullbackTensor, ObjectProperty.isoMk,
      ObjectProperty.homMk, pullbackTensorIntegralReductionTensor,
      pullbackTensorIntegralReductionPullback, pullbackTensorReferenceComparison,
      Iso.trans_hom, Functor.mapIso_hom, asIso_hom, asIso_inv, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Iso.prod_hom, Functor.prod_map, Functor.comp_map,
      pullbackTensorReferencePullback, pullbackTensorReferenceTensor,
      constructibleIntegralPullback, constructibleIntegralTensor,
      ObjectProperty.lift, ObjectProperty.ι_obj, Functor.comp_obj, Functor.prod_obj,
      Functor.id_obj]
    simpa only [Functor.map_comp, Category.assoc, Iso.prod_hom, Iso.symm_hom,
      Iso.app_inv, asIso_inv, Functor.comp_map, Functor.prod_map, Functor.id_obj] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def reduction_tensor (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    constructibleIntegralTensor l E W ⋙ coherentReduction l E W ≅
      (coherentReduction l E W).prod (coherentReduction l E W) ⋙
        (pullbackTensorCalculus l E W).systemClosed.tensor :=
  NatIso.ofComponents (fun MN ↦ pullbackTensorIntegralReductionTensor l E W MN.1 MN.2) (by
    intro MN PQ k
    dsimp only [pullbackTensorIntegralReductionTensor, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom]
    simpa only [Category.assoc, Iso.app_hom, coherentReduction,
      constructibleIntegralTensor, ObjectProperty.lift, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      ObjectProperty.homMk, Functor.prod_map, Functor.prod_obj, pullbackTensorCalculus] using
      counit_model_naturality
        (pullbackTensorCalculus l E W).reduction (coefficientSequenceLimit l E W)
        (pullbackTensorCalculus l E W).adjunction (integralCompletedTensor l E W)
        (((pullbackTensorCalculus l E W).reduction.prod
          (pullbackTensorCalculus l E W).reduction) ⋙
          (pullbackTensorCalculus l E W).systemClosed.tensor)
        (pullbackTensorIntegralTensorModel l E W) (Prod.mkHom k.1.hom k.2.hom))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def reduction_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E f ⋙ coherentReduction l E X ≅
      coherentReduction l E Y ⋙ pullbackTensorSequenceDerived l E f :=
  NatIso.ofComponents (pullbackTensorIntegralReductionPullback l E f) (by
    intro M N k
    dsimp only [pullbackTensorIntegralReductionPullback, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom]
    simpa only [Category.assoc, Iso.app_hom, coherentReduction,
      constructibleIntegralPullback, ObjectProperty.lift, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      ObjectProperty.homMk, pullbackTensorCalculus] using counit_model_naturality
      (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E X)
      (pullbackTensorCalculus l E X).adjunction (integralDerivedPullback l E f)
      ((pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f)
      (pullbackTensorIntegralPullbackModel l E f) k.hom)

private theorem reducedBraiding_natural
    {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D) [Q.Faithful]
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    (b : T ⋙ Q ≅ (Q.prod Q) ⋙ S)
    (β : ∀ A B, S.obj (A, B) ⟶ S.obj (B, A))
    (hβ : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      S.map (Prod.mkHom f g) ≫ β A' B' = β A B ≫ S.map (Prod.mkHom g f))
    (bi : ∀ A B, T.obj (A, B) ⟶ T.obj (B, A))
    (hb : ∀ A B, Q.map (bi A B) ≫ b.hom.app (B, A) =
      b.hom.app (A, B) ≫ β (Q.obj A) (Q.obj B))
    (M M' N N' : C) (f : M ⟶ M') (g : N ⟶ N') :
    T.map (Prod.mkHom f g) ≫ bi M' N' = bi M N ≫ T.map (Prod.mkHom g f) := by
  have hn := b.hom.naturality (Prod.mkHom f g)
  have hn' := b.hom.naturality (Prod.mkHom g f)
  change Q.map (T.map (Prod.mkHom f g)) ≫ b.hom.app (M', N') =
    b.hom.app (M, N) ≫ S.map (Prod.mkHom (Q.map f) (Q.map g)) at hn
  change Q.map (T.map (Prod.mkHom g f)) ≫ b.hom.app (N', M') =
    b.hom.app (N, M) ≫ S.map (Prod.mkHom (Q.map g) (Q.map f)) at hn'
  apply Q.map_injective
  apply (cancel_mono (b.hom.app (N', M'))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [hb, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [hβ, hn']
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ S.map (Prod.mkHom (Q.map g) (Q.map f))) (hb M N).symm

private theorem representative_braiding
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (T : C × C ⥤ C) (S : D × D ⥤ D)
    (β : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (γ : ∀ P Q, S.obj (P, Q) ≅ S.obj (Q, P))
    (μ : ∀ M N, F.obj (T.obj (M, N)) ≅ S.obj (F.obj M, F.obj N))
    (hc : ∀ M N, F.map (β M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (γ (F.obj M) (F.obj N)).hom)
    (hn : ∀ P P' Q Q' (f : P ⟶ P') (g : Q ⟶ Q'),
      S.map (Prod.mkHom f g) ≫ (γ P' Q').hom =
        (γ P Q).hom ≫ S.map (Prod.mkHom g f))
    (M N : C) {A B : C} {U V P Q X Y : D}
    (a : A ≅ T.obj (M, N)) (b : B ≅ T.obj (N, M))
    (u : U ≅ F.obj A) (v : V ≅ F.obj B)
    (p : P ≅ F.obj M) (q : Q ≅ F.obj N)
    (x : X ≅ S.obj (P, Q)) (y : Y ≅ S.obj (Q, P)) :
    (u.hom ≫ F.map (a.hom ≫ (β M N).hom ≫ b.inv) ≫ v.inv) ≫
      (v.hom ≫ F.map b.hom ≫ (μ N M).hom ≫
        S.map (Prod.mkHom q.inv p.inv) ≫ y.inv) =
    (u.hom ≫ F.map a.hom ≫ (μ M N).hom ≫
      S.map (Prod.mkHom p.inv q.inv) ≫ x.inv) ≫
      (x.hom ≫ (γ P Q).hom ≫ y.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_map_assoc]
  rw [reassoc_of% (hc M N), ← reassoc_of% (hn _ _ _ _ p.inv q.inv)]

private theorem localizedBraiding_natural
    {R : Type*} [CommRing R] {A : Type*} [Category* A] [Preadditive A] [Linear R A]
    (p : R) (T : A × A ⥤ A) (bi : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (hn : ∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (bi M' N').hom =
        (bi M N).hom ≫ T.map (Prod.mkHom g f))
    (F : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (br : ∀ M N, F.obj (M, N) ≅ F.obj (N, M))
    (ho : ∀ MN, F.obj MN = ⟨T.obj (MN.1.obj, MN.2.obj)⟩)
    (hm : ∀ M M' N N', ∃ b : (M ⟶ M') →ₗ[Localization.Away p]
        (N ⟶ N') →ₗ[Localization.Away p] (F.obj (M, N) ⟶ F.obj (M', N')),
      (∀ f g, F.map (Prod.mkHom f g) = b f g) ∧
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (a b' : Localization.Away p),
        HEq (b (a ⊗ₜ[R] f) (b' ⊗ₜ[R] g))
          ((a * b') ⊗ₜ[R] T.map (Prod.mkHom f g)))
    (hb : ∀ M N, HEq (br M N).hom
      ((ScalarLocalization.localization R A p).map (bi M.obj N.obj).hom)) :
    ∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
      F.map (Prod.mkHom f g) ≫ (br M' N').hom =
        (br M N).hom ≫ F.map (Prod.mkHom g f) := by
  intro M M' N N' f g
  obtain ⟨b, he, hp⟩ := hm M M' N N'
  obtain ⟨b', he', hp'⟩ := hm N N' M M'
  rw [he, he']
  have ht (a : Localization.Away p) (f : M.obj ⟶ M'.obj)
      (c : Localization.Away p) (g : N.obj ⟶ N'.obj) :
      b (a ⊗ₜ[R] f) (c ⊗ₜ[R] g) ≫ (br M' N').hom =
        (br M N).hom ≫ b' (c ⊗ₜ[R] g) (a ⊗ₜ[R] f) := by
    have hl := heq_comp (ho (M, N)) (ho (M', N')) (ho (N', M'))
      (hp f g a c) (hb M' N')
    have hr := heq_comp (ho (M, N)) (ho (N, M)) (ho (N', M'))
      (hb M N) (hp' g f c a)
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ScalarLocalization.composition R A p _ _ _
        (1 ⊗ₜ[R] (bi M'.obj N'.obj).hom)
        ((a * c) ⊗ₜ[R] T.map (Prod.mkHom f g)) =
      ScalarLocalization.composition R A p _ _ _
        ((c * a) ⊗ₜ[R] T.map (Prod.mkHom g f))
        (1 ⊗ₜ[R] (bi M.obj N.obj).hom)
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
      one_mul, mul_one, mul_comm c a, hn]
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | tmul c g => exact ht a f c g
    | add g g' hg hg' =>
      simp only [map_add, LinearMap.add_apply, Preadditive.add_comp,
        Preadditive.comp_add, hg, hg']
  | add f f' hf hf' =>
    simp only [map_add, LinearMap.add_apply, Preadditive.add_comp,
      Preadditive.comp_add, hf, hf']

attribute [local irreducible] pullbackTensorIntegralComposition
  pullbackTensorIntegralReductionTensor pullbackTensorIntegralReductionPullback
  pullbackTensorCommonLeft pullbackTensorCommonRight pullbackTensorCommonAssociator

private theorem normalizedCoefficientSequence_of_iso (W : Scheme.{u})
    {A B : coefficientSequenceDerived l E W} (e : B ≅ A)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsNormalizedCoefficientSequence l E W B := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    intro m n h P
    let en := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
    let em := (coefficientSequenceDerivedEvaluation l E W m).mapIso e
    let R := normalizedDVRRes l E W h
    have ht := (coefficientSequenceDerivedTransition l E W h).naturality e.hom
    change em.hom ≫ _ = _ ≫ R.map en.hom at ht
    have hti := (coefficientSequenceDerivedTransition l E W h).naturality e.inv
    change em.inv ≫ _ = _ ≫ R.map en.inv at hti
    constructor
    · intro f g hfg
      apply (cancel_epi en.inv).mp
      apply (hA h P).injective
      change _ ≫ R.map (en.inv ≫ f) = _ ≫ R.map (en.inv ≫ g)
      have hh (k : (coefficientSequenceDerivedEvaluation l E W n).obj B ⟶ P) :
          (coefficientSequenceDerivedTransition l E W h).app A ≫ R.map (en.inv ≫ k) =
            em.inv ≫ (coefficientSequenceDerivedTransition l E W h).app B ≫ R.map k := by
        rw [Functor.map_comp, ← Category.assoc, ← hti, Category.assoc]
      rw [hh, hh]
      exact congrArg (fun k ↦ em.inv ≫ k) hfg
    · intro a
      obtain ⟨b, hb⟩ := (hA h P).surjective (em.inv ≫ a)
      refine ⟨en.hom ≫ b, ?_⟩
      change _ ≫ R.map (en.hom ≫ b) = a
      change _ ≫ R.map b = em.inv ≫ a at hb
      rw [Functor.map_comp, ← Category.assoc, ← ht, Category.assoc, hb]
      simp

private theorem pullbackTensorSystemUnit_normalized (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    IsNormalizedCoefficientSequence l E W
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨M, hM⟩ := CompletedOperations.normalizedCompletedOperationModels l E
      (fun _ : Unit ↦ W) (fun _ x ↦ isUnit_of_invertible (l : W.residueField x))
    let e : (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
        CompletedOperations.unit l E (W := fun _ : Unit ↦ W) () :=
      closedTensorUnitIso
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose).systemClosed
        (M.system ()).closed ≪≫
        (M.system ()).unitIso
    intro m n h P
    exact normalizedCoefficientSequence_of_iso l E W e
      (fun {m n} h P ↦ hM.unit () h P) h P

private def pushUnitIso {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r})
    {S : Sheaf J RingCat.{r}}
    (h : (F.sheafPushforwardContinuous RingCat.{r} J K).obj R = S) :
    (SheafOfModules.pushforward (F := F) (eqToHom h.symm)).obj
      (SheafOfModules.unit R) ≅ SheafOfModules.unit S := by
  subst S
  exact Iso.refl _

private def evaluationUnitIso (W : Scheme.{u}) (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).obj
      (SheafOfModules.unit
        ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E W))) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n) :=
  pushUnitIso (Prod.sectR n W.ProEt) _ (coefficientSequenceEvaluationRing_eq l E W n)

private theorem systemUnitEvaluationIso (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] (n : ℕ) :
    Nonempty ((coefficientSequenceDerivedEvaluation l E W n).obj
      ((coefficientDerivedSystemEvaluationCalculus l E W).choose).systemClosed.monoidal.tensorUnit ≅
      finiteConstantCoefficientObject l E W n) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨M, hM⟩ := CompletedOperations.normalizedCompletedOperationModels l E
      (fun _ : Unit ↦ W) (fun _ x ↦ isUnit_of_invertible (l : W.residueField x))
    let e := closedTensorUnitIso
      ((coefficientDerivedSystemEvaluationCalculus l E W).choose).systemClosed
      (M.system ()).closed ≪≫ (M.system ()).unitIso
    exact ⟨(coefficientSequenceDerivedEvaluation l E W n).mapIso e ≪≫
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (evaluationUnitIso l E W n)⟩

/-- The limit of the coherent ring unit is constructible and complete.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: The coherent ring unit is the
constant
  rank-one finite coefficient tower. Its quotient transitions are normalized. Normalized DVR
  effectivity computes its limit as the completed rank-one coefficient module, whose reductions are
  the finite constructible ring units; these have uniform amplitude zero. -/
theorem pullbackTensorIntegralUnit_constructible (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let S := (coefficientDerivedSystemEvaluationCalculus l E W).choose
    let U := S.systemClosed.monoidal.tensorUnit
    let K := (coefficientSequenceLimit l E W).obj U
    have hl := coefficientPrime_isUnit l W
    have hn : IsNormalizedCoefficientSequence l E W U :=
      fun {m n} h P ↦ pullbackTensorSystemUnit_normalized l E W h P
    obtain ⟨hcomplete, hcounit⟩ := (purNormalizedReconstruction l E W hl S).1 U hn
    obtain ⟨D, hlp, hD⟩ := hcomplete
    refine ⟨(sfDerivedComplete_iff_legacy l E W D hlp K).mpr hD,
      0, 0, le_refl _, ?_⟩
    intro n
    let := hcounit
    obtain ⟨en⟩ := systemUnitEvaluationIso l E W n
    let e : (scalarReductionDerivedExtension l E W n).obj K ≅
        finiteConstantCoefficientObject l E W n :=
      (S.reductionEvaluation n).symm.app K ≪≫
        (coefficientSequenceDerivedEvaluation l E W n).mapIso
          (asIso (S.adjunction.counit.app U)) ≪≫ en
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) W) :=
      (AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated W
        (Padic.coefficientExtensionRing l E (n + 1))).1
    refine ⟨ObjectProperty.prop_of_iso _ e.symm
      (finiteConstantCoefficient_constructible l E W n).1, ?_⟩
    intro i hi
    have hi' : i ∈ proEtaleCohomologicalSupport
        (finiteConstantCoefficientObject l E W n) := by
      intro hz
      exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mpr hz)
    have he : i = 0 := by
      by_contra h
      apply hi'
      unfold finiteConstantCoefficientObject
      rcases lt_or_gt_of_ne h with h | h
      · exact DerivedCategory.isZero_of_isGE _ 0 i h
      · exact DerivedCategory.isZero_of_isLE _ 0 i h
    simp [he]

/-- The actual derived limit of the coherent coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] : sfIntegralConstructibleCategory l E W :=
  ⟨_, @pullbackTensorIntegralUnit_constructible l _ E _ _ _ W hW⟩

/-- The reduction counit of the normalized coefficient-ring unit is invertible.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: The finite ring units and their
quotient
  tensor comparisons form a normalized system. Apply normalized DVR effectivity to this system. The
  reconstruction isomorphism is precisely the reduction/limit adjunction counit. -/
theorem pullbackTensorIntegralUnit_counit (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] : IsIso ((pullbackTensorCalculus l E
      W).adjunction.counit.app
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hl := coefficientPrime_isUnit l W
    exact ((purNormalizedReconstruction l E W hl
      (coefficientDerivedSystemEvaluationCalculus l E W).choose).1 _
        (fun {m n} h P ↦ pullbackTensorSystemUnit_normalized l E W h P)).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed identification of the reduced integral unit with the coherent ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralUnitReduction (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    (pullbackTensorCalculus l E W).reduction.obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W
      hW)).obj ≅
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit :=
  letI := (@pullbackTensorIntegralUnit_counit l _ E _ _ _ W hW)
  asIso ((pullbackTensorCalculus l E W).adjunction.counit.app _)

/-- The rational unit is the localization of the completed coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :=
  (sfRationalConstructibleLocalization l E W).obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W hW))

attribute [local irreducible] pullbackTensorIntegralUnitReduction

-- Keep the category instances folded after constructing the unit evaluation map.
set_option allowUnsafeReducibility true in
attribute [local irreducible] instCategoryDerivedCategory DerivedCategory.instPreadditive
  SheafOfModules.instAbelian SheafOfModules.instCategory

/-- The integral left unitor is fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Conjugate the coherent unitor by
the actual
  tensor-reduction and unit-reduction isomorphisms. Reduction is fully faithful on the complete
  constructible subcategory by normalized effectivity, so this arrow and its inverse lift uniquely.
  Faithfulness gives the inverse identities. -/
theorem pullbackTensorIntegralLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorIntegralUnit l _ E
      _ _ _ W hW),M) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) ((@pullbackTensorIntegralUnit l _
          E _ _ _ W hW)) M).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    let target : (coherentReduction l E W).obj
        ((constructibleIntegralTensor l E W).obj (pullbackTensorIntegralUnit l E W,M)) ≅
        (coherentReduction l E W).obj M :=
      pullbackTensorIntegralReductionTensor l E W (pullbackTensorIntegralUnit l E W) M ≪≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
          (Iso.prod (pullbackTensorIntegralUnitReduction l E W) (Iso.refl _)) ≪≫
        (pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor _
    obtain ⟨d, hd, hu⟩ := existsUnique_iso_of_map (coherentReduction l E W) target
    refine ⟨d, ?_, ?_⟩
    · change (coherentReduction l E W).map
        d.hom = _
      rw [hd]
      rfl
    · intro d' hd'
      apply hu
      exact hd'

/-- The normalized completed left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralLeftUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The rational left unitor is the localized completed one.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Use the prescribed rational
tensor object
  equality and localize the integral unitor and its inverse. The displayed hom equality uniquely
  determines the iso. -/
theorem pullbackTensorRationalLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorRationalUnit l _ E _ _ _
      W hW),M) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ W hW) M.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
        (pullbackTensorRationalUnit l E W,M)) rfl
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralLeftUnitor l E W M.obj))

/-- The localized completed left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalLeftUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The integral right unitor is fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Conjugate the coherent unitor by
the actual
  tensor-reduction and unit-reduction isomorphisms. Reduction is fully faithful on the complete
  constructible subcategory by normalized effectivity, so this arrow and its inverse lift uniquely.
  Faithfulness gives the inverse identities. -/
theorem pullbackTensorIntegralRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorIntegralUnit l _
      E _ _ _ W hW)) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M ((@pullbackTensorIntegralUnit l
          _ E _ _ _ W hW))).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    let target : (coherentReduction l E W).obj
        ((constructibleIntegralTensor l E W).obj (M,pullbackTensorIntegralUnit l E W)) ≅
        (coherentReduction l E W).obj M :=
      pullbackTensorIntegralReductionTensor l E W M (pullbackTensorIntegralUnit l E W) ≪≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
          (Iso.prod (Iso.refl _) (pullbackTensorIntegralUnitReduction l E W)) ≪≫
        (pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor _
    obtain ⟨d, hd, hu⟩ := existsUnique_iso_of_map (coherentReduction l E W) target
    refine ⟨d, ?_, ?_⟩
    · change (coherentReduction l E W).map
        d.hom = _
      rw [hd]
      rfl
    · intro d' hd'
      apply hu
      exact hd'

/-- The normalized completed right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralRightUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The rational right unitor is the localized completed one.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Use the prescribed rational
tensor object
  equality and localize the integral unitor and its inverse. The displayed hom equality uniquely
  determines the iso. -/
theorem pullbackTensorRationalRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorRationalUnit l _ E _ _
      _ W hW)) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ W hW) M.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
        (M,pullbackTensorRationalUnit l E W)) rfl
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralRightUnitor l E W M.obj))

/-- The localized completed right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalRightUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

-- Conjugating both inputs of a reduced tensor comparison respects its square.
private theorem scalarConjugate_tensor_comparison
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : U ⋙ R ≅ R.prod R ⋙ J) (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (p : F ⋙ Q ≅ R ⋙ H) (ν : J ⋙ H ≅ H.prod H ⋙ I)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
        p.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
          ν.hom.app (R.obj M, R.obj N))
    (M N : C) (A B : D) (K L : S)
    (d : F.obj M ≅ A) (e : F.obj N ≅ B)
    (x : Q.obj A ≅ H.obj K) (y : Q.obj B ≅ H.obj L)
    (r : R.obj M ≅ K) (s : R.obj N ≅ L)
    (hd : Q.map d.hom ≫ x.hom = p.hom.app M ≫ H.map r.hom)
    (he : Q.map e.hom ≫ y.hom = p.hom.app N ≫ H.map s.hom) :
    Q.map ((μ M N).hom ≫ V.map (Prod.mkHom d.hom e.hom)) ≫
        b.hom.app (A, B) ≫ I.map (Prod.mkHom x.hom y.hom) =
      p.hom.app (U.obj (M, N)) ≫
        H.map (a.hom.app (M, N) ≫ J.map (Prod.mkHom r.hom s.hom)) ≫
        ν.hom.app (K, L) := by
  have hb := b.hom.naturality (Prod.mkHom d.hom e.hom)
  change Q.map (V.map (Prod.mkHom d.hom e.hom)) ≫ b.hom.app (A, B) =
    b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (Q.map d.hom) (Q.map e.hom)) at hb
  rw [Q.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hb, ← I.map_comp]
  simp only [prod_comp, hd, he]
  rw [← map_pair_comp I (p.hom.app M) (p.hom.app N)
    (H.map r.hom) (H.map s.hom)]
  rw [reassoc_of% (hμ M N)]
  have hn := ν.hom.naturality (Prod.mkHom r.hom s.hom)
  change H.map (J.map (Prod.mkHom r.hom s.hom)) ≫ ν.hom.app (K, L) =
    ν.hom.app (R.obj M, R.obj N) ≫
      I.map (Prod.mkHom (H.map r.hom) (H.map s.hom)) at hn
  rw [← hn, H.map_comp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Integral scalar extension preserves the coefficient-ring unit, compatibly with both
integral unitors and the prescribed integral scalar tensor comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: apply coherent reduction.
The coherent scalar tensor normalization identifies the reduced tensor comparison with the
whole-system scalar tensorator, whose unit equations are `systemScalarTensorUnit`. Insert the
unit reductions and use full faithfulness of coherent reduction. -/
theorem integralScalarTensorUnit_exists
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    ∃ ε : (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι W).obj (pullbackTensorIntegralUnit l E W) ≅ pullbackTensorIntegralUnit l L W,
      ∀ M : sfIntegralConstructibleCategory l E W,
        ((integralTensorScalarComparison l E L ι W (pullbackTensorIntegralUnit l E W) M).hom ≫
          (constructibleIntegralTensor l L W).map (Prod.mkHom ε.hom (𝟙 _)) ≫
          (pullbackTensorIntegralLeftUnitor l L W
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)).hom =
        (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι W).map (pullbackTensorIntegralLeftUnitor l E W M).hom) ∧
        ((integralTensorScalarComparison l E L ι W M (pullbackTensorIntegralUnit l E W)).hom ≫
          (constructibleIntegralTensor l L W).map (Prod.mkHom (𝟙 _) ε.hom) ≫
          (pullbackTensorIntegralRightUnitor l L W
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)).hom =
        (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι W).map (pullbackTensorIntegralRightUnitor l E W M).hom) := by
  have := (coherentReduction_fullyFaithful l L W).1
  have := (coherentReduction_fullyFaithful l L W).2
  let R := coherentReduction l E W
  let Q := coherentReduction l L W
  let F := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  let U := constructibleIntegralTensor l E W
  let V := constructibleIntegralTensor l L W
  let J := (pullbackTensorCalculus l E W).systemClosed.tensor
  let I := (pullbackTensorCalculus l L W).systemClosed.tensor
  let a := reduction_tensor l E W
  let b := reduction_tensor l L W
  obtain ⟨p₀, hp₀⟩ := integralScalarTensorCoherentReduction l E L ι W
  let p : F ⋙ Q ≅ R ⋙ H := p₀
  let ν := ScalarExtensionTower.derivedSigma l E L ι W
    (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
  let μ := integralTensorScalarComparison l E L ι W
  have hμ : ∀ M N, Q.map (μ M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
        p.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
          ν.hom.app (R.obj M, R.obj N) := fun M N ↦ hp₀ M N
  let UE := pullbackTensorIntegralUnit l E W
  let UL := pullbackTensorIntegralUnit l L W
  let eE := pullbackTensorIntegralUnitReduction l E W
  let eL := pullbackTensorIntegralUnitReduction l L W
  obtain ⟨εS, hS⟩ := systemScalarTensorUnit l E L ι W
  let ε : F.obj UE ≅ UL := Q.preimageIso
    (p.app UE ≪≫ H.mapIso eE ≪≫ εS ≪≫ eL.symm)
  have hε : Q.map ε.hom ≫ (eL ≪≫ εS.symm).hom =
      p.hom.app UE ≫ H.map eE.hom := by
    dsimp only [ε, Functor.preimageIso]
    rw [Functor.map_preimage]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id, Iso.app_hom]
  refine ⟨ε, fun M ↦ ?_⟩
  constructor
  · let a₀ := a.app (UE, M) ≪≫ J.mapIso (Iso.prod eE (Iso.refl (R.obj M)))
    let b₀ := b.app (UL, F.obj M) ≪≫
      I.mapIso (Iso.prod (eL ≪≫ εS.symm) (p.app M))
    let δ := I.mapIso (Iso.prod εS (Iso.refl (H.obj (R.obj M)))) ≪≫
      (pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor _
    have hs := reduced_square R Q F H p a₀ (Iso.refl (R.obj M)) b₀ (p.app M)
      (pullbackTensorIntegralLeftUnitor l E W M)
      (pullbackTensorIntegralLeftUnitor l L W (F.obj M))
      ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor (R.obj M)) δ
      (μ UE M ≪≫ V.mapIso (Iso.prod ε (Iso.refl (F.obj M))))
      (Iso.refl (F.obj M)) (ν.app (_, R.obj M)) (Iso.refl (H.obj (R.obj M)))
    have h := hs ?_ ?_ ?_ ?_ ?_
    · simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
        Category.comp_id, Category.assoc] using h.symm
    · simpa only [a₀, a, reduction_tensor, R, coherentReduction, UE, eE, J,
        pullbackTensorIntegralLeftUnitor, Iso.trans_hom, Functor.mapIso_hom,
        Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc,
        Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
        NatIso.ofComponents_hom_app] using
        (pullbackTensorIntegralLeftUnitor_existsUnique l E W M).exists.choose_spec
    · have hu : Q.map (pullbackTensorIntegralLeftUnitor l L W (F.obj M)).hom =
          b.hom.app (UL, F.obj M) ≫ I.map (Prod.mkHom eL.hom (𝟙 _)) ≫
            ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor
              (Q.obj (F.obj M))).hom :=
        (pullbackTensorIntegralLeftUnitor_existsUnique l L W (F.obj M)).exists.choose_spec
      let := (pullbackTensorCalculus l L W).systemClosed.monoidal
      have hn : I.map (Prod.mkHom (𝟙 _) (p.hom.app M)) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor
            (H.obj (R.obj M))).hom =
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor
            (Q.obj (F.obj M))).hom ≫ p.hom.app M := by
        simpa only [I, Q, R, F, H, Functor.comp_obj, MonoidalCategory.tensor_obj,
          CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
          MonoidalCategory.id_tensorHom] using
          MonoidalCategory.leftUnitor_naturality (p.hom.app M)
      dsimp only [b₀, δ, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Iso.symm_hom]
      rw [hu]
      simp only [Category.assoc]
      rw [← hn]
      simp only [← I.map_comp_assoc, prod_comp, Category.assoc, Category.id_comp,
        Category.comp_id, Iso.inv_hom_id, H, R, Functor.comp_obj, Iso.prod_hom, Iso.trans_hom,
        Iso.symm_hom, Iso.refl_hom, Iso.inv_hom_id_assoc, Iso.app_hom]
    · simpa only [a₀, b₀, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Category.assoc] using
        scalarConjugate_tensor_comparison R Q F H U V J I a b p ν μ hμ
          UE M UL (F.obj M) _ (R.obj M)
          ε (Iso.refl _) (eL ≪≫ εS.symm) (p.app M) eE (Iso.refl _) hε
          (by simp)
    · simp
    · simpa only [δ, H, I, J, ν, Functor.comp_obj,
        Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc] using (hS (R.obj M)).1.symm
  · let a₀ := a.app (M, UE) ≪≫ J.mapIso (Iso.prod (Iso.refl (R.obj M)) eE)
    let b₀ := b.app (F.obj M, UL) ≪≫
      I.mapIso (Iso.prod (p.app M) (eL ≪≫ εS.symm))
    let δ := I.mapIso (Iso.prod (Iso.refl (H.obj (R.obj M))) εS) ≪≫
      (pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor _
    have hs := reduced_square R Q F H p a₀ (Iso.refl (R.obj M)) b₀ (p.app M)
      (pullbackTensorIntegralRightUnitor l E W M)
      (pullbackTensorIntegralRightUnitor l L W (F.obj M))
      ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor (R.obj M)) δ
      (μ M UE ≪≫ V.mapIso (Iso.prod (Iso.refl (F.obj M)) ε))
      (Iso.refl (F.obj M)) (ν.app (R.obj M, _)) (Iso.refl (H.obj (R.obj M)))
    have h := hs ?_ ?_ ?_ ?_ ?_
    · simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
        Category.comp_id, Category.assoc] using h.symm
    · simpa only [a₀, a, reduction_tensor, R, coherentReduction, UE, eE, J,
        pullbackTensorIntegralRightUnitor, Iso.trans_hom, Functor.mapIso_hom,
        Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc,
        Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
        NatIso.ofComponents_hom_app] using
        (pullbackTensorIntegralRightUnitor_existsUnique l E W M).exists.choose_spec
    · have hu : Q.map (pullbackTensorIntegralRightUnitor l L W (F.obj M)).hom =
          b.hom.app (F.obj M, UL) ≫ I.map (Prod.mkHom (𝟙 _) eL.hom) ≫
            ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor
              (Q.obj (F.obj M))).hom :=
        (pullbackTensorIntegralRightUnitor_existsUnique l L W (F.obj M)).exists.choose_spec
      let := (pullbackTensorCalculus l L W).systemClosed.monoidal
      have hn : I.map (Prod.mkHom (p.hom.app M) (𝟙 _)) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor
            (H.obj (R.obj M))).hom =
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor
            (Q.obj (F.obj M))).hom ≫ p.hom.app M := by
        simpa only [I, Q, R, F, H, Functor.comp_obj, MonoidalCategory.tensor_obj,
          CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
          MonoidalCategory.tensorHom_id] using
          MonoidalCategory.rightUnitor_naturality (p.hom.app M)
      dsimp only [b₀, δ, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Iso.symm_hom]
      rw [hu]
      simp only [Category.assoc]
      rw [← hn]
      simp only [← I.map_comp_assoc, prod_comp, Category.assoc, Category.id_comp,
        Category.comp_id, Iso.inv_hom_id, H, R, Functor.comp_obj, Iso.prod_hom, Iso.trans_hom,
        Iso.symm_hom, Iso.refl_hom, Iso.inv_hom_id_assoc, Iso.app_hom]
    · simpa only [a₀, b₀, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Category.assoc] using
        scalarConjugate_tensor_comparison R Q F H U V J I a b p ν μ hμ
          M UE (F.obj M) UL (R.obj M) _
          (Iso.refl _) ε (p.app M) (eL ≪≫ εS.symm) (Iso.refl _) eE
          (by simp) hε
    · simp
    · simpa only [δ, H, I, J, ν, Functor.comp_obj,
        Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc] using (hS (R.obj M)).2.symm

private theorem scalarUnit_chosen_spec {A : Sort*} {p : A → Prop}
    (h : ∃! a, p a) (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

-- Naturality descends through the specified tensor and unit reduction maps.
private theorem scalarUnit_reducedLeftUnitor_natural
    {C D : Type*} [Category* C] [Category* D]
    (Q : C ⥤ D) [Q.Faithful] (T : C × C ⥤ C) (S : D × D ⥤ D)
    (b : T ⋙ Q ≅ (Q.prod Q) ⋙ S) (U : C) (V : D) (e : Q.obj U ≅ V)
    (lu : ∀ M, S.obj (V, M) ≅ M)
    (hn : ∀ {M N} (f : M ⟶ N),
      S.map (Prod.mkHom (𝟙 V) f) ≫ (lu N).hom = (lu M).hom ≫ f)
    (li : ∀ M, T.obj (U, M) ≅ M)
    (hi : ∀ M, Q.map (li M).hom = b.hom.app (U, M) ≫
      S.map (Prod.mkHom e.hom (𝟙 _)) ≫ (lu (Q.obj M)).hom)
    {M N : C} (f : M ⟶ N) :
    T.map (Prod.mkHom (𝟙 U) f) ≫ (li N).hom = (li M).hom ≫ f := by
  have hb := b.hom.naturality (Prod.mkHom (𝟙 U) f)
  change Q.map (T.map (Prod.mkHom (𝟙 U) f)) ≫ b.hom.app (U, N) =
    b.hom.app (U, M) ≫ S.map (Prod.mkHom (Q.map (𝟙 U)) (Q.map f)) at hb
  apply Q.map_injective
  simp only [Functor.map_comp, hi, Category.assoc]
  rw [← Category.assoc, hb, Q.map_id]
  simp only [Category.assoc]
  have hs : S.map (Prod.mkHom (𝟙 (Q.obj U)) (Q.map f)) ≫
      S.map (Prod.mkHom e.hom (𝟙 (Q.obj N))) =
    S.map (Prod.mkHom e.hom (𝟙 (Q.obj M))) ≫
      S.map (Prod.mkHom (𝟙 V) (Q.map f)) := by
    simp only [← S.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  rw [reassoc_of% hs, hn]

-- Tensoring by an object isomorphic to the unit is faithful.
private theorem scalarUnit_unitIso_unique
    {C : Type*} [Category* C] (T : C × C ⥤ C) (U A : C)
    (lu : ∀ M, T.obj (U, M) ≅ M)
    (hn : ∀ {M N} (f : M ⟶ N),
      T.map (Prod.mkHom (𝟙 U) f) ≫ (lu N).hom = (lu M).hom ≫ f)
    (j k : A ≅ U)
    (h : T.map (Prod.mkHom (𝟙 A) j.hom) =
      T.map (Prod.mkHom (𝟙 A) k.hom)) : j = k := by
  have ht := congrArg (fun z ↦ T.map (Prod.mkHom j.inv (𝟙 A)) ≫ z ≫
    T.map (Prod.mkHom j.hom (𝟙 U))) h
  simp only [← T.map_comp, prod_comp, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id] at ht
  have he := congrArg (fun z ↦ z ≫ (lu U).hom) ht
  rw [hn, hn] at he
  exact Iso.ext ((cancel_epi (lu A).hom).mp he)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarUnit_integralLeftUnitor_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N : sfIntegralConstructibleCategory l E W} (f : M ⟶ N) :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom (𝟙 (pullbackTensorIntegralUnit l E W)) f) ≫
        (pullbackTensorIntegralLeftUnitor l E W N).hom =
      (pullbackTensorIntegralLeftUnitor l E W M).hom ≫ f := by
  have := (coherentReduction_fullyFaithful l E W).2
  apply scalarUnit_reducedLeftUnitor_natural (coherentReduction l E W)
    (constructibleIntegralTensor l E W) (pullbackTensorCalculus l E W).systemClosed.tensor
    (reduction_tensor l E W) (pullbackTensorIntegralUnit l E W) _
    (pullbackTensorIntegralUnitReduction l E W)
    (pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
  · intro M N f
    let := (pullbackTensorCalculus l E W).systemClosed.monoidal
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.id_tensorHom] using MonoidalCategory.leftUnitor_naturality f
  · intro M
    exact (pullbackTensorIntegralLeftUnitor_existsUnique l E W M).exists.choose_spec

private theorem scalarUnit_rationalLeftUnitor_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N : sfRationalConstructibleCategory l E W} (f : M ⟶ N) :
    (rationalDerivedTensor l E W).map
        (Prod.mkHom (𝟙 (pullbackTensorRationalUnit l E W)) f) ≫
        (pullbackTensorRationalLeftUnitor l E W N).hom =
      (pullbackTensorRationalLeftUnitor l E W M).hom ≫ f := by
  let T := rationalDerivedTensor l E W
  let I := constructibleIntegralTensor l E W
  let R := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  let U := pullbackTensorRationalUnit l E W
  let U₀ := pullbackTensorIntegralUnit l E W
  have spec := scalarUnit_chosen_spec (rationalDerivedTensor_existsUnique l E W) T rfl
  have ho (MN : sfRationalConstructibleCategory l E W ×
      sfRationalConstructibleCategory l E W) :
      T.obj MN = ScalarLocalization.mk (I.obj (MN.1.obj, MN.2.obj)) := spec.1 MN
  obtain ⟨b, hb, hp⟩ := spec.2 U U M N
  change T.map (Prod.mkHom (𝟙 U) f) ≫ _ = _
  rw [hb]
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    change (b (𝟙 U)) (f + g) ≫ _ = _ ≫ (f + g)
    rw [map_add, Preadditive.add_comp]
    rw [hf, hg]
    exact (Preadditive.comp_add _ _ _
      (pullbackTensorRationalLeftUnitor l E W M).hom f g).symm
  | tmul a f =>
    have ht : HEq (b (𝟙 U) (a ⊗ₜ[R] f))
        ((1 * a) ⊗ₜ[R] I.map (Prod.mkHom (𝟙 U₀) f)) := hp (𝟙 U₀) f 1 a
    have hL := (pullbackTensorRationalLeftUnitor_existsUnique l E W N).exists.choose_spec
    have hM := (pullbackTensorRationalLeftUnitor_existsUnique l E W M).exists.choose_spec
    have hl := heq_comp (ho (U, M)) (ho (U, N)) rfl ht hL
    have hr := heq_comp (ho (U, M)) rfl rfl hM (HEq.rfl (a := a ⊗ₜ[R] f))
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ScalarLocalization.composition R _ p _ _ _
        (1 ⊗ₜ[R] (pullbackTensorIntegralLeftUnitor l E W N.obj).hom)
        ((1 * a) ⊗ₜ[R] I.map (Prod.mkHom (𝟙 U₀) f)) =
      ScalarLocalization.composition R _ p _ _ _ (a ⊗ₜ[R] f)
        (1 ⊗ₜ[R] (pullbackTensorIntegralLeftUnitor l E W M.obj).hom)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    rw [scalarUnit_integralLeftUnitor_natural l E W f]

/-- Rational form of `integralScalarTensorUnit_exists`, with uniqueness.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem rationalScalarUnit_existsUnique_aux
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    ∃! e : (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((@pullbackTensorRationalUnit l _ E _ _ _ W hW)) ≅ (@pullbackTensorRationalUnit l _ L _ _
            _ W hW),
      ∀ M : sfRationalConstructibleCategory l E W,
        ((rationalTensorScalarComparison l E L ι W).hom.app ((@pullbackTensorRationalUnit l _ E _ _
          _ W hW),M) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom e.hom (𝟙 _)) ≫
          ((@pullbackTensorRationalLeftUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalLeftUnitor l
              _ E _ _ _ W hW) M).hom) ∧
        ((rationalTensorScalarComparison l E L ι W).hom.app (M,(@pullbackTensorRationalUnit l _ E _
          _ _ W hW)) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom (𝟙 _) e.hom) ≫
          ((@pullbackTensorRationalRightUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalRightUnitor l
              _ E _ _ _ W hW) M).hom) := by
  let G := sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let S := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let Q := sfRationalConstructibleLocalization l L W
  let QE := sfRationalConstructibleLocalization l E W
  let U := pullbackTensorRationalUnit l E W
  let UL := pullbackTensorIntegralUnit l L W
  have hG (K : sfRationalConstructibleCategory l E W) : G.obj K = Q.obj (S.obj K.obj) :=
    sfRationalScalarExtension_obj l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι K
  have hTE (MN) : (rationalDerivedTensor l E W).obj MN =
      QE.obj ((constructibleIntegralTensor l E W).obj (MN.1.obj, MN.2.obj)) :=
    (scalarUnit_chosen_spec (rationalDerivedTensor_existsUnique l E W)
      (rationalDerivedTensor l E W) rfl).1 MN
  have hTL (MN) : (rationalDerivedTensor l L W).obj MN =
      Q.obj ((constructibleIntegralTensor l L W).obj (MN.1.obj, MN.2.obj)) :=
    (scalarUnit_chosen_spec (rationalDerivedTensor_existsUnique l L W)
      (rationalDerivedTensor l L W) rfl).1 MN
  have hα := scalarUnit_chosen_spec (rationalTensorScalarComparison_existsUnique l E L ι W)
    (rationalTensorScalarComparison l E L ι W) rfl
  -- Localize the integral unit comparison, retaining its prescribed hom.
  obtain ⟨εI, hI⟩ := integralScalarTensorUnit_exists l E L ι W
  obtain ⟨ε, hε, _⟩ := existsUnique_iso_of_eq (hG U) rfl (Q.mapIso εI)
  change ∃! ε : G.obj U ≅ Q.obj UL, _
  have hbase (M : sfRationalConstructibleCategory l E W) : (G.obj M).obj = S.obj M.obj := by
    rw [hG]; rfl
  have hid (M : sfRationalConstructibleCategory l E W) :
      HEq (𝟙 (G.obj M)) (Q.map (𝟙 (S.obj M.obj))) := by
    have hh {A : sfRationalConstructibleCategory l L W}
        {B : sfIntegralConstructibleCategory l L W} (h : A = Q.obj B) :
        HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
    exact hh (hG M)
  have htmap {A B C D : sfRationalConstructibleCategory l L W}
      {A' B' C' D' : sfIntegralConstructibleCategory l L W}
      (hA : A = Q.obj A') (hB : B = Q.obj B')
      (hC : C = Q.obj C') (hD : D = Q.obj D')
      (a : A ⟶ B) (b : C ⟶ D) (a' : A' ⟶ B') (b' : C' ⟶ D')
      (ha : HEq a (Q.map a')) (hb : HEq b (Q.map b')) :
      HEq ((rationalDerivedTensor l L W).map (Prod.mkHom a b))
        (Q.map ((constructibleIntegralTensor l L W).map (Prod.mkHom a' b'))) := by
    subst A B C D
    have ha' := eq_of_heq ha
    have hb' := eq_of_heq hb
    subst a b
    obtain ⟨bil, hbil, hbil'⟩ :=
      (scalarUnit_chosen_spec (rationalDerivedTensor_existsUnique l L W)
        (rationalDerivedTensor l L W) rfl).2
        (Q.obj A') (Q.obj B') (Q.obj C') (Q.obj D')
    rw [hbil]
    convert hbil' a' b' 1 1 using 1
    simp only [one_mul]
    rfl
  have hmap {A B : sfRationalConstructibleCategory l E W}
      {A' B' : sfIntegralConstructibleCategory l E W}
      (hA : A = QE.obj A') (hB : B = QE.obj B')
      (a : A ⟶ B) (b : A' ⟶ B') (hab : HEq a (QE.map b)) :
      HEq (G.map a) (Q.map (S.map b)) := by
    refine map_localized_heq S G QE Q (fun {K K'} c ↦ ?_) hA hB a b hab
    have h := sfRationalScalarExtension_map_tmul l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι K K' c 1
    have h1 : (sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E 1)) = 1 := by
      simp only [map_one]
    rw [h1] at h
    exact h
  have equations : ∀ M,
      ((rationalTensorScalarComparison l E L ι W).hom.app (U, M) ≫
        (rationalDerivedTensor l L W).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        (pullbackTensorRationalLeftUnitor l L W (G.obj M)).hom =
        G.map (pullbackTensorRationalLeftUnitor l E W M).hom) ∧
      ((rationalTensorScalarComparison l E L ι W).hom.app (M, U) ≫
        (rationalDerivedTensor l L W).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        (pullbackTensorRationalRightUnitor l L W (G.obj M)).hom =
        G.map (pullbackTensorRationalRightUnitor l E W M).hom) := by
    intro M
    constructor
    · have hc := hα U M
      have ht := htmap (hG U) rfl (hG M) (hG M) ε.hom (𝟙 _) εI.hom (𝟙 _) hε (hid M)
      have hu := (pullbackTensorRationalLeftUnitor_existsUnique l L W
        (G.obj M)).exists.choose_spec
      have hcongr {A B : sfIntegralConstructibleCategory l L W} (h : A = B) :
          HEq (Q.map (pullbackTensorIntegralLeftUnitor l L W A).hom)
            (Q.map (pullbackTensorIntegralLeftUnitor l L W B).hom) := by subst B; rfl
      have hu' := hu.trans (hcongr (hbase M))
      have htail := heq_comp (by rw [hTL, hG, hG]; rfl)
        (by rw [hTL, hG]; rfl) (hG M) ht hu'
      have hleft := heq_comp (by dsimp only [Functor.comp_obj]; rw [hG, hTE]; rfl)
        (by dsimp only [Functor.comp_obj, Functor.prod_obj]; rw [hTL, hG, hG]; rfl) (hG M) hc htail
      have hright := hmap (hTE (U, M)) rfl _ _
        (pullbackTensorRationalLeftUnitor_existsUnique l E W M).exists.choose_spec
      apply eq_of_heq
      refine hleft.trans ((heq_of_eq ?_).trans hright.symm)
      have h := congrArg Q.map (hI M.obj).1
      simp only [Functor.map_comp] at h
      convert h using 1
      rfl
    · have hc := hα M U
      have ht := htmap (hG M) (hG M) (hG U) rfl (𝟙 _) ε.hom (𝟙 _) εI.hom (hid M) hε
      have hu := (pullbackTensorRationalRightUnitor_existsUnique l L W
        (G.obj M)).exists.choose_spec
      have hcongr {A B : sfIntegralConstructibleCategory l L W} (h : A = B) :
          HEq (Q.map (pullbackTensorIntegralRightUnitor l L W A).hom)
            (Q.map (pullbackTensorIntegralRightUnitor l L W B).hom) := by subst B; rfl
      have hu' := hu.trans (hcongr (hbase M))
      have htail := heq_comp (by rw [hTL, hG, hG]; rfl)
        (by rw [hTL, hG]; rfl) (hG M) ht hu'
      have hleft := heq_comp (by dsimp only [Functor.comp_obj]; rw [hG, hTE]; rfl)
        (by dsimp only [Functor.comp_obj, Functor.prod_obj]; rw [hTL, hG, hG]; rfl) (hG M) hc htail
      have hright := hmap (hTE (M, U)) rfl _ _
        (pullbackTensorRationalRightUnitor_existsUnique l E W M).exists.choose_spec
      apply eq_of_heq
      refine hleft.trans ((heq_of_eq ?_).trans hright.symm)
      have h := congrArg Q.map (hI M.obj).2
      simp only [Functor.map_comp] at h
      convert h using 1
      rfl
  refine ⟨ε, equations, ?_⟩
  intro ε' hε'
  -- The right equation at the unit fixes its tensor with the extended unit.
  have he := ((hε' U).2).trans (equations U).2.symm
  have ht : (rationalDerivedTensor l L W).map (Prod.mkHom (𝟙 (G.obj U)) ε'.hom) =
        (rationalDerivedTensor l L W).map (Prod.mkHom (𝟙 (G.obj U)) ε.hom) := by
    apply (cancel_mono (pullbackTensorRationalRightUnitor l L W (G.obj U)).hom).mp
    apply (cancel_epi ((rationalTensorScalarComparison l E L ι W).hom.app (U, U))).mp
    convert he using 1 <;> rfl
  exact scalarUnit_unitIso_unique (rationalDerivedTensor l L W) (pullbackTensorRationalUnit l L W)
    (G.obj U) (pullbackTensorRationalLeftUnitor l L W)
    (fun g ↦ scalarUnit_rationalLeftUnitor_natural l L W g) ε' ε ht

-- Naturality in the first variable descends through the specified tensor and unit reductions.
private theorem scalarUnit_reducedRightUnitor_natural
    {C D : Type*} [Category* C] [Category* D]
    (Q : C ⥤ D) [Q.Faithful] (T : C × C ⥤ C) (S : D × D ⥤ D)
    (b : T ⋙ Q ≅ (Q.prod Q) ⋙ S) (U : C) (V : D) (e : Q.obj U ≅ V)
    (ru : ∀ M, S.obj (M, V) ≅ M)
    (hn : ∀ {M N} (f : M ⟶ N),
      S.map (Prod.mkHom f (𝟙 V)) ≫ (ru N).hom = (ru M).hom ≫ f)
    (ri : ∀ M, T.obj (M, U) ≅ M)
    (hi : ∀ M, Q.map (ri M).hom = b.hom.app (M, U) ≫
      S.map (Prod.mkHom (𝟙 _) e.hom) ≫ (ru (Q.obj M)).hom)
    {M N : C} (f : M ⟶ N) :
    T.map (Prod.mkHom f (𝟙 U)) ≫ (ri N).hom = (ri M).hom ≫ f := by
  have hb := b.hom.naturality (Prod.mkHom f (𝟙 U))
  change Q.map (T.map (Prod.mkHom f (𝟙 U))) ≫ b.hom.app (N, U) =
    b.hom.app (M, U) ≫ S.map (Prod.mkHom (Q.map f) (Q.map (𝟙 U))) at hb
  apply Q.map_injective
  simp only [Functor.map_comp, hi, Category.assoc]
  rw [← Category.assoc, hb, Q.map_id]
  simp only [Category.assoc]
  have hs : S.map (Prod.mkHom (Q.map f) (𝟙 (Q.obj U))) ≫
      S.map (Prod.mkHom (𝟙 (Q.obj N)) e.hom) =
    S.map (Prod.mkHom (𝟙 (Q.obj M)) e.hom) ≫
      S.map (Prod.mkHom (Q.map f) (𝟙 V)) := by
    simp only [← S.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  rw [reassoc_of% hs, hn]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarUnit_integralRightUnitor_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N : sfIntegralConstructibleCategory l E W} (f : M ⟶ N) :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom f (𝟙 (pullbackTensorIntegralUnit l E W))) ≫
        (pullbackTensorIntegralRightUnitor l E W N).hom =
      (pullbackTensorIntegralRightUnitor l E W M).hom ≫ f := by
  have := (coherentReduction_fullyFaithful l E W).2
  apply scalarUnit_reducedRightUnitor_natural (coherentReduction l E W)
    (constructibleIntegralTensor l E W) (pullbackTensorCalculus l E W).systemClosed.tensor
    (reduction_tensor l E W) (pullbackTensorIntegralUnit l E W) _
    (pullbackTensorIntegralUnitReduction l E W)
    (pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor
  · intro M N f
    let := (pullbackTensorCalculus l E W).systemClosed.monoidal
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.tensorHom_id] using MonoidalCategory.rightUnitor_naturality f
  · intro M
    exact (pullbackTensorIntegralRightUnitor_existsUnique l E W M).exists.choose_spec

private theorem scalarUnit_rationalRightUnitor_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N : sfRationalConstructibleCategory l E W} (f : M ⟶ N) :
    (rationalDerivedTensor l E W).map
        (Prod.mkHom f (𝟙 (pullbackTensorRationalUnit l E W))) ≫
        (pullbackTensorRationalRightUnitor l E W N).hom =
      (pullbackTensorRationalRightUnitor l E W M).hom ≫ f := by
  let T := rationalDerivedTensor l E W
  let I := constructibleIntegralTensor l E W
  let R := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  let U := pullbackTensorRationalUnit l E W
  let U₀ := pullbackTensorIntegralUnit l E W
  have spec := scalarUnit_chosen_spec (rationalDerivedTensor_existsUnique l E W) T rfl
  have ho (MN : sfRationalConstructibleCategory l E W ×
      sfRationalConstructibleCategory l E W) :
      T.obj MN = ScalarLocalization.mk (I.obj (MN.1.obj, MN.2.obj)) := spec.1 MN
  obtain ⟨b, hb, hp⟩ := spec.2 M N U U
  change T.map (Prod.mkHom f (𝟙 U)) ≫ _ = _
  rw [hb]
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    change (b (f + g)) (𝟙 U) ≫ _ = _ ≫ (f + g)
    rw [map_add, LinearMap.add_apply, Preadditive.add_comp]
    rw [hf, hg]
    exact (Preadditive.comp_add _ _ _
      (pullbackTensorRationalRightUnitor l E W M).hom f g).symm
  | tmul a f =>
    have ht : HEq (b (a ⊗ₜ[R] f) (𝟙 U))
        ((a * 1) ⊗ₜ[R] I.map (Prod.mkHom f (𝟙 U₀))) := hp f (𝟙 U₀) a 1
    have hL := (pullbackTensorRationalRightUnitor_existsUnique l E W N).exists.choose_spec
    have hM := (pullbackTensorRationalRightUnitor_existsUnique l E W M).exists.choose_spec
    have hl := heq_comp (ho (M, U)) (ho (N, U)) rfl ht hL
    have hr := heq_comp (ho (M, U)) rfl rfl hM (HEq.rfl (a := a ⊗ₜ[R] f))
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ScalarLocalization.composition R _ p _ _ _
        (1 ⊗ₜ[R] (pullbackTensorIntegralRightUnitor l E W N.obj).hom)
        ((a * 1) ⊗ₜ[R] I.map (Prod.mkHom f (𝟙 U₀))) =
      ScalarLocalization.composition R _ p _ _ _ (a ⊗ₜ[R] f)
        (1 ⊗ₜ[R] (pullbackTensorIntegralRightUnitor l E W M.obj).hom)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    rw [scalarUnit_integralRightUnitor_natural l E W f]

attribute [local irreducible] pullbackTensorIntegralUnit pullbackTensorRationalUnit
  pullbackTensorIntegralLeftUnitor pullbackTensorIntegralRightUnitor
  pullbackTensorRationalLeftUnitor pullbackTensorRationalRightUnitor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Scalar extension preserves the canonical rational coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: For integral coefficients, scalar
extension
  sends the coefficient-ring unit to the new coefficient ring by multiplication. Its unit equations
  hold on pure tensors, remain true in both Roos coordinates, and localize. The tensor comparison is
  invertible; cancellation in the unit square at the unit object proves uniqueness. -/
theorem pullbackTensorRationalScalarUnit_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    ∃! e : (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((@pullbackTensorRationalUnit l _ E _ _ _ W hW)) ≅ (@pullbackTensorRationalUnit l _ L _ _
            _ W hW),
      ∀ M : sfRationalConstructibleCategory l E W,
        ((rationalTensorScalarComparison l E L ι W).hom.app ((@pullbackTensorRationalUnit l _ E _ _
          _ W hW),M) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom e.hom (𝟙 _)) ≫
          ((@pullbackTensorRationalLeftUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalLeftUnitor l
              _ E _ _ _ W hW) M).hom) ∧
        ((rationalTensorScalarComparison l E L ι W).hom.app (M,(@pullbackTensorRationalUnit l _ E _
          _ _ W hW)) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom (𝟙 _) e.hom) ≫
          ((@pullbackTensorRationalRightUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalRightUnitor l
              _ E _ _ _ W hW) M).hom) := by
  exact rationalScalarUnit_existsUnique_aux l E L ι W

/-- The coefficient-ring scalar comparison fixed by the two tensor unit squares.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalScalarUnit
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :=
  (@pullbackTensorRationalScalarUnit_existsUnique l _ E _ _ _ L _ _ _ ι W hW).exists.choose

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The common-stage unit represented over the least finite coefficient field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
      generalAlgebraicallyClosedConstructibleCategory l
      Ω W :=
  ⟨Padic.finiteCoefficientBase l Ω,
    (@pullbackTensorRationalUnit l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) _ _ _ W hW)⟩

/-- The common-stage ring unit is the rational ring unit at every larger stage.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonUnitStage (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage ≤ L) :
    ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).toStage h ≅
      (@pullbackTensorRationalUnit l _
        (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W hW)
        :=
  (operationStageTransitionIso l Ω W _ L h).app _ ≪≫
    @pullbackTensorRationalScalarUnit l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) _ _ _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _
        (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.coefficientInclusion l Ω _ L h) W hW

section CommonUnitorTransport

-- Transport a unit square along an equality of the scalar functor.
private theorem scalarUnit_leftSquare_of_eq {A B : Type*} [Category* A] [Category* B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) {G G' : A ⥤ B} (hG : G' = G)
    (cG : TA ⋙ G ≅ G.prod G ⋙ TB) (c : TA ⋙ G' ≅ G'.prod G' ⋙ TB)
    (hc : c = Functor.isoWhiskerLeft TA (eqToIso hG) ≪≫ cG ≪≫
      Functor.isoWhiskerRight (NatIso.prod (eqToIso hG).symm (eqToIso hG).symm) TB)
    (UA : A) (UB : B) (eG : G.obj UA ≅ UB)
    (luA : ∀ X, TA.obj (UA, X) ≅ X) (luB : ∀ X, TB.obj (UB, X) ≅ X)
    (h : ∀ X, cG.hom.app (UA, X) ≫ TB.map (Prod.mkHom eG.hom (𝟙 _)) ≫
      (luB (G.obj X)).hom = G.map (luA X).hom) (X : A) :
    c.hom.app (UA, X) ≫ TB.map (Prod.mkHom ((eqToIso hG).app UA ≪≫ eG).hom (𝟙 _)) ≫
      (luB (G'.obj X)).hom = G'.map (luA X).hom := by
  subst hG hc
  simpa [Functor.isoWhiskerLeft, Functor.isoWhiskerRight, NatTrans.prod] using h X

private theorem scalarUnit_rightSquare_of_eq {A B : Type*} [Category* A] [Category* B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) {G G' : A ⥤ B} (hG : G' = G)
    (cG : TA ⋙ G ≅ G.prod G ⋙ TB) (c : TA ⋙ G' ≅ G'.prod G' ⋙ TB)
    (hc : c = Functor.isoWhiskerLeft TA (eqToIso hG) ≪≫ cG ≪≫
      Functor.isoWhiskerRight (NatIso.prod (eqToIso hG).symm (eqToIso hG).symm) TB)
    (UA : A) (UB : B) (eG : G.obj UA ≅ UB)
    (ruA : ∀ X, TA.obj (X, UA) ≅ X) (ruB : ∀ X, TB.obj (X, UB) ≅ X)
    (h : ∀ X, cG.hom.app (X, UA) ≫ TB.map (Prod.mkHom (𝟙 _) eG.hom) ≫
      (ruB (G.obj X)).hom = G.map (ruA X).hom) (X : A) :
    c.hom.app (X, UA) ≫ TB.map (Prod.mkHom (𝟙 _) ((eqToIso hG).app UA ≪≫ eG).hom) ≫
      (ruB (G'.obj X)).hom = G'.map (ruA X).hom := by
  subst hG hc
  simpa [Functor.isoWhiskerLeft, Functor.isoWhiskerRight, NatTrans.prod] using h X

/-- The scalar unit comparison along a stage transition. -/
private def commonScalarUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    ((stageSystem l Ω W).T h).obj
        (pullbackTensorRationalUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W) ≅
      pullbackTensorRationalUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W :=
  (operationStageTransitionIso l Ω W i j h).app _ ≪≫
    pullbackTensorRationalScalarUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) W

attribute [local semireducible] operationStageTransitionIso in
private theorem commonScalarUnit_left (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j)
    (X : Stage l Ω W i) :
    (rationalTensorStageComparison l Ω W h).hom.app
        (pullbackTensorRationalUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W,
          X) ≫
      (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W).map
        (Prod.mkHom (commonScalarUnit l Ω W h).hom (𝟙 _)) ≫
      (pullbackTensorRationalLeftUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W
        (((stageSystem l Ω W).T h).obj X)).hom =
    ((stageSystem l Ω W).T h).map
      (pullbackTensorRationalLeftUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
        W X).hom := by
  have spec := (pullbackTensorRationalScalarUnit_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) W).exists.choose_spec
  exact scalarUnit_leftSquare_of_eq
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W)
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W)
    ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 i j h)
    (rationalTensorScalarComparison l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) W)
    (rationalTensorStageComparison l Ω W h) rfl _ _
    (pullbackTensorRationalScalarUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) W)
    (pullbackTensorRationalLeftUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W)
    (pullbackTensorRationalLeftUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W)
    (fun X ↦ (spec X).1) X

attribute [local semireducible] operationStageTransitionIso in
private theorem commonScalarUnit_right (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j)
    (X : Stage l Ω W i) :
    (rationalTensorStageComparison l Ω W h).hom.app
        (X,
          pullbackTensorRationalUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W) ≫
      (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W).map
        (Prod.mkHom (𝟙 _) (commonScalarUnit l Ω W h).hom) ≫
      (pullbackTensorRationalRightUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
        W (((stageSystem l Ω W).T h).obj X)).hom =
    ((stageSystem l Ω W).T h).map
      (pullbackTensorRationalRightUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
        W X).hom := by
  have spec := (pullbackTensorRationalScalarUnit_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) W).exists.choose_spec
  exact scalarUnit_rightSquare_of_eq
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W)
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W)
    ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 i j h)
    (rationalTensorScalarComparison l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) W)
    (rationalTensorStageComparison l Ω W h) rfl _ _
    (pullbackTensorRationalScalarUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) W)
    (pullbackTensorRationalRightUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      W)
    (pullbackTensorRationalRightUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      W)
    (fun X ↦ (spec X).2) X

/-- Reassociate the two input corrections through the bifunctor. -/
private theorem scalarUnit_tensorStageComparison_endpoint
    {C D : Type*} [Category* C] [Category* D]
    (F : C × C ⥤ C) (G : D × D ⥤ D) {T R : C ⥤ D} (e : T ≅ R)
    (c : F ⋙ R ≅ R.prod R ⋙ G) (X Y : C) {X' Y' : D}
    (a : T.obj X ≅ X') (b : T.obj Y ≅ Y') :
    ((Functor.isoWhiskerLeft F e ≪≫ c ≪≫
        Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) G).app (X, Y) ≪≫
      G.mapIso (Iso.prod a b)) =
    e.app (F.obj (X, Y)) ≪≫ c.app (X, Y) ≪≫
      G.mapIso (Iso.prod ((e.app X).symm ≪≫ a) ((e.app Y).symm ≪≫ b)) := by
  apply Iso.ext
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    NatIso.prod_hom, NatTrans.prod, Iso.prod_hom, Functor.mapIso_hom]
  simp only [Category.assoc, ← Functor.map_comp, prod_comp, Iso.prod_hom, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv]

attribute [local semireducible] operationStageTransitionIso commonStageTensorComparison in
/-- The common-stage tensor comparison is the descent endpoint of the stage comparisons. -/
private theorem commonStageTensorComparison_endpoint (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : (commonStageTensorObject l Ω W P Q).stage ≤ L) :
    (commonStageTensorComparison l Ω W P Q L h).hom =
      (rationalTensorStageComparison l Ω W h).hom.app
        (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1,
          Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2) ≫
      (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W).map
        (Prod.mkHom
          (((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1 h).hom.app P.obj)
          (((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2 h).hom.app
              Q.obj)) := by
  have hh := scalarUnit_tensorStageComparison_endpoint
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage)) W)
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W)
    (operationStageTransitionIso l Ω W _ L h)
    (rationalTensorScalarComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage))
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω _ L h) W)
    (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1)
    (Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2)
    (((stageSystem l Ω W).assoc
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1 h).app P.obj)
    (((stageSystem l Ω W).assoc
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2 h).app Q.obj)
  have hh' := congrArg Iso.hom hh
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom] at hh'
  rw [show commonStageTensorComparison l Ω W P Q L h =
      (operationStageTransitionIso l Ω W _ L h).app (commonStageTensorObject l Ω W P Q).obj ≪≫
        _ ≪≫ _ from rfl]
  exact hh'.symm

/-- Cached stagewise tensor functors. -/
private abbrev cuT (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    Stage l Ω W i × Stage l Ω W i ⥤ Stage l Ω W i :=
  rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W

/-- Cached stagewise tensor comparisons. -/
private abbrev cuc (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    cuT l Ω W i ⋙ (stageSystem l Ω W).T h ≅
      ((stageSystem l Ω W).T h).prod ((stageSystem l Ω W).T h) ⋙ cuT l Ω W j :=
  rationalTensorStageComparison l Ω W h

/-- Cached stagewise units. -/
private abbrev cuUn (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (i : AlgebraicallyClosedCoefficients.Index l Ω) : Stage l Ω W i :=
  pullbackTensorRationalUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W

/-- Cached stagewise left unitors. -/
private abbrev culu (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (i : AlgebraicallyClosedCoefficients.Index l Ω) (X : Stage l Ω W i) :
    (cuT l Ω W i).obj (cuUn l Ω W i, X) ≅ X :=
  pullbackTensorRationalLeftUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W X

/-- Cached stagewise right unitors. -/
private abbrev curu (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (i : AlgebraicallyClosedCoefficients.Index l Ω) (X : Stage l Ω W i) :
    (cuT l Ω W i).obj (X, cuUn l Ω W i) ≅ X :=
  pullbackTensorRationalRightUnitor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W X

private theorem cu_tower (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    StageTensorTower (stageSystem l Ω W) (cuT l Ω W) (fun h ↦ cuc l Ω W h) :=
  fun h h' X Y ↦ rationalTensorStageComparison_coherent l Ω W h h' X Y

private theorem cu_hlu (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ i {X Y : Stage l Ω W i} (f : X ⟶ Y),
      (cuT l Ω W i).map (Prod.mkHom (𝟙 (cuUn l Ω W i)) f) ≫ (culu l Ω W i Y).hom =
        (culu l Ω W i X).hom ≫ f :=
  fun i X Y f ↦ scalarUnit_rationalLeftUnitor_natural l _ W f

private theorem cu_hru (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ i {X Y : Stage l Ω W i} (f : X ⟶ Y),
      (cuT l Ω W i).map (Prod.mkHom f (𝟙 (cuUn l Ω W i))) ≫ (curu l Ω W i Y).hom =
        (curu l Ω W i X).hom ≫ f :=
  fun i X Y f ↦ scalarUnit_rationalRightUnitor_natural l _ W f

private theorem cu_hL (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) (X : Stage l Ω W i),
      (cuc l Ω W h).hom.app (cuUn l Ω W i, X) ≫
        (cuT l Ω W j).map (Prod.mkHom (commonScalarUnit l Ω W h).hom (𝟙 _)) ≫
        (culu l Ω W j (((stageSystem l Ω W).T h).obj X)).hom =
      ((stageSystem l Ω W).T h).map (culu l Ω W i X).hom :=
  fun h X ↦ commonScalarUnit_left l Ω W h X

private theorem cu_hR (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) (X : Stage l Ω W i),
      (cuc l Ω W h).hom.app (X, cuUn l Ω W i) ≫
        (cuT l Ω W j).map (Prod.mkHom (𝟙 _) (commonScalarUnit l Ω W h).hom) ≫
        (curu l Ω W j (((stageSystem l Ω W).T h).obj X)).hom =
      ((stageSystem l Ω W).T h).map (curu l Ω W i X).hom :=
  fun h X ↦ commonScalarUnit_right l Ω W h X

private theorem cu_cocycle (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ {i j k : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) (h' : j ≤ k),
      ((stageSystem l Ω W).T h').map (commonScalarUnit l Ω W h).hom ≫
          (commonScalarUnit l Ω W h').hom =
        ((stageSystem l Ω W).assoc h h').hom.app (cuUn l Ω W i) ≫
          (commonScalarUnit l Ω W (h.trans h')).hom :=
  fun h h' ↦ stageUnit_cocycle (stageSystem l Ω W) (cuT l Ω W) (fun h ↦ cuc l Ω W h)
    (cuUn l Ω W) (fun h ↦ commonScalarUnit l Ω W h) (cu_tower l Ω W) (culu l Ω W)
    (curu l Ω W) (cu_hlu l Ω W) (cu_hru l Ω W) (cu_hR l Ω W) h h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackTensorCommonLeftUnitor_existsUnique_aux (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)),M) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW)) M) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω _ _ _
            W hW)).stage
          M.stage).2.trans h)
          ((commonStageTensorComparison l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω
                  _ _ _ W hW)).stage M.stage).1.trans h)).hom (𝟙 _)) ≫
            ((@pullbackTensorRationalLeftUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage M.stage).2.trans
                  h))).hom)) := by
  classical
  let S := stageSystem l Ω W
  let U := pullbackTensorCommonUnit l Ω W
  let A := commonStageTensorObject l Ω W U M
  have hb := ((Padic.finiteCoefficientFields_properties l Ω).1 U.stage M.stage).1
  have hm := ((Padic.finiteCoefficientFields_properties l Ω).1 U.stage M.stage).2
  obtain ⟨d, hd⟩ := pairCategory_exists_iso_of_tr S (A := A) (M := M) hm
    (fun h ↦ stageLeftUnitorRep S (cuT l Ω W) (fun h ↦ cuc l Ω W h) (cuUn l Ω W)
      (fun h ↦ commonScalarUnit l Ω W h) (culu l Ω W) hb hm M.obj h)
    (fun h k ↦ stageLeftUnitorRep_tr S (cuT l Ω W) (fun h ↦ cuc l Ω W h) (cuUn l Ω W)
      (fun h ↦ commonScalarUnit l Ω W h) (cu_tower l Ω W) (culu l Ω W) (cu_hlu l Ω W)
      (cu_hL l Ω W) (cu_cocycle l Ω W) hb hm M.obj h k)
  have hTobj : (commonStageDerivedTensor l Ω W).obj (U, M) = A :=
    (scalarUnit_chosen_spec (commonStageDerivedTensor_existsUnique l Ω W)
      (commonStageDerivedTensor l Ω W) (by unfold commonStageDerivedTensor; rfl)).1 U M
  apply existsUnique_of_exists_of_unique
  · refine ⟨eqToIso hTobj ≪≫ d, fun L h ↦ ?_⟩
    rw [Iso.trans_hom, eqToIso.hom, hd L h]
    refine (eqToHom_comp_heq _ _).trans (heq_of_eq ?_)
    dsimp only [GeneralAlgebraicallyClosedCoefficients.ofHom]
    apply congrArg (StageSystem.PairCategory.mkHom (X := A) (Y := M) L h (hm.trans h))
    rw [commonStageTensorComparison_endpoint]
    exact stageLeftUnitorRep_hom_eq S (cuT l Ω W) (fun h ↦ cuc l Ω W h) (cuUn l Ω W)
      (fun h ↦ commonScalarUnit l Ω W h) (culu l Ω W) hb hm M.obj h
  · intro y₁ y₂ h₁ h₂
    exact Iso.ext (eq_of_heq ((h₁ _ le_rfl).trans (h₂ _ le_rfl).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackTensorCommonRightUnitor_existsUnique_aux (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (M,((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW))) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage ((@pullbackTensorCommonUnit l _
            Ω _ _ _ W hW)).stage).1.trans h)
          ((commonStageTensorComparison l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom (𝟙 _) ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                  ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).2.trans h)).hom) ≫
            ((@pullbackTensorRationalRightUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).1.trans h))).hom)) := by
  classical
  let S := stageSystem l Ω W
  let U := pullbackTensorCommonUnit l Ω W
  let A := commonStageTensorObject l Ω W M U
  have hm := ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage U.stage).1
  have hb := ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage U.stage).2
  obtain ⟨d, hd⟩ := pairCategory_exists_iso_of_tr S (A := A) (M := M) hm
    (fun h ↦ stageRightUnitorRep S (cuT l Ω W) (fun h ↦ cuc l Ω W h) (cuUn l Ω W)
      (fun h ↦ commonScalarUnit l Ω W h) (curu l Ω W) hb hm M.obj h)
    (fun h k ↦ stageRightUnitorRep_tr S (cuT l Ω W) (fun h ↦ cuc l Ω W h) (cuUn l Ω W)
      (fun h ↦ commonScalarUnit l Ω W h) (cu_tower l Ω W) (curu l Ω W) (cu_hru l Ω W)
      (cu_hR l Ω W) (cu_cocycle l Ω W) hb hm M.obj h k)
  have hTobj : (commonStageDerivedTensor l Ω W).obj (M, U) = A :=
    (scalarUnit_chosen_spec (commonStageDerivedTensor_existsUnique l Ω W)
      (commonStageDerivedTensor l Ω W) (by unfold commonStageDerivedTensor; rfl)).1 M U
  apply existsUnique_of_exists_of_unique
  · refine ⟨eqToIso hTobj ≪≫ d, fun L h ↦ ?_⟩
    rw [Iso.trans_hom, eqToIso.hom, hd L h]
    refine (eqToHom_comp_heq _ _).trans (heq_of_eq ?_)
    dsimp only [GeneralAlgebraicallyClosedCoefficients.ofHom]
    apply congrArg (StageSystem.PairCategory.mkHom (X := A) (Y := M) L h (hm.trans h))
    rw [commonStageTensorComparison_endpoint]
    exact stageRightUnitorRep_hom_eq S (cuT l Ω W) (fun h ↦ cuc l Ω W h) (cuUn l Ω W)
      (fun h ↦ commonScalarUnit l Ω W h) (curu l Ω W) hb hm M.obj h
  · intro y₁ y₂ h₁ h₂
    exact Iso.ext (eq_of_heq ((h₁ _ le_rfl).trans (h₂ _ le_rfl).symm))

end CommonUnitorTransport

attribute [local irreducible] pullbackTensorCommonUnitStage pullbackTensorCommonUnit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The common-stage left unitor has the canonical representative at every larger field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Represent at the finite
compositum. Apply
  the tensor-stage comparison, the coefficient-ring unit comparison, and the rational unitor. The
  scalar unit equations and scalar cocycles identify these arrows at all larger stages. Their
  inverses define an inverse class, and this representative condition determines the colimit hom
  uniquely. -/
theorem pullbackTensorCommonLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)),M) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW)) M) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω _ _ _
            W hW)).stage
          M.stage).2.trans h)
          ((commonStageTensorComparison l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω
                  _ _ _ W hW)).stage M.stage).1.trans h)).hom (𝟙 _)) ≫
            ((@pullbackTensorRationalLeftUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage M.stage).2.trans h))).hom)) :=
                  by
  exact pullbackTensorCommonLeftUnitor_existsUnique_aux l Ω W M

/-- The common-stage class of the canonical rational left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonLeftUnitor_existsUnique l _ Ω _ _ _ W hW) M).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The common-stage right unitor has the canonical representative at every larger field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Represent at the finite
compositum. Apply
  the tensor-stage comparison, the coefficient-ring unit comparison, and the rational unitor. The
  scalar unit equations and scalar cocycles identify these arrows at all larger stages. Their
  inverses define an inverse class, and this representative condition determines the colimit hom
  uniquely. -/
theorem pullbackTensorCommonRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (M,((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW))) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage ((@pullbackTensorCommonUnit l _
            Ω _ _ _ W hW)).stage).1.trans h)
          ((commonStageTensorComparison l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom (𝟙 _) ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                  ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).2.trans h)).hom) ≫
            ((@pullbackTensorRationalRightUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).1.trans h))).hom)) := by
  exact pullbackTensorCommonRightUnitor_existsUnique_aux l Ω W M

/-- The common-stage class of the canonical rational right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonRightUnitor_existsUnique l _ Ω _ _ _ W hW) M).exists.choose

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Both unit equations for the actual canonical integral comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalIntegralPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
    ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) ≅
      (@pullbackTensorIntegralUnit l _ E _ _ _ X hX),
    ∀ M : sfIntegralConstructibleCategory l E Y,
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) ((@pullbackTensorIntegralUnit l _
        E _ _ _ Y hY)) M).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ X hX) (((@constructibleIntegralPullback l _
          E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M ((@pullbackTensorIntegralUnit l
        _ E _ _ _ Y hY))).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ X hX) (((@constructibleIntegralPullback l _
          E _ _ _ X Y f hX hY)).obj M)).hom
          =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom)

/-- Both unit equations for the actual canonical rational comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalRationalPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj ((@pullbackTensorRationalUnit l _
    E _ _ _ Y hY)) ≅
      (@pullbackTensorRationalUnit l _ E _ _ _ X hX),
    ∀ M : sfRationalConstructibleCategory l E Y,
      (((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) ((@pullbackTensorRationalUnit l _
        E _ _ _ Y hY)) M).hom ≫
        ((@rationalDerivedTensor l _ E _ _ _ X hX)).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorRationalLeftUnitor l _ E _ _ _ X hX) (((@rationalDerivedPullback l _ E _ _
          _ X Y f hX hY)).obj M)).hom =
      ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalLeftUnitor l
        _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M ((@pullbackTensorRationalUnit l
        _ E _ _ _ Y hY))).hom ≫
        ((@rationalDerivedTensor l _ E _ _ _ X hX)).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorRationalRightUnitor l _ E _ _ _ X hX) (((@rationalDerivedPullback l _ E _ _
          _ X Y f hX hY)).obj M)).hom =
      ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalRightUnitor
        l _ E _ _ _ Y hY) M).hom)

/-- Both unit equations for the actual canonical commonstage comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalCommonStagePullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj ((@pullbackTensorCommonUnit l _
    Ω _ _ _ Y hY)) ≅
      (@pullbackTensorCommonUnit l _ Ω _ _ _ X hX),
    ∀ M : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      (((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) ((@pullbackTensorCommonUnit l
        _ Ω _ _ _ Y hY)) M).hom ≫
        ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorCommonLeftUnitor l _ Ω _ _ _ X hX) (((@commonStageDerivedPullback l _ Ω _ _
          _ X Y f hX hY)).obj M)).hom =
      ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonLeftUnitor
        l _ Ω _ _ _ Y hY) M).hom) ∧
      (((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M ((@pullbackTensorCommonUnit
        l _ Ω _ _ _ Y hY))).hom ≫
        ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorCommonRightUnitor l _ Ω _ _ _ X hX) (((@commonStageDerivedPullback l _ Ω _
          _ _ X Y f hX hY)).obj M)).hom =
      ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonRightUnitor
        l _ Ω _ _ _ Y hY) M).hom)

/-- Coherence for the canonical integral comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalIntegralPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : sfIntegralConstructibleCategory l E Y),
    ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
      ((@pullbackTensorIntegralAssociator l _ E _ _ _ Y hY) M N P).hom ≫
          ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M
            (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (N,P))).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom (𝟙 _) ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) N P).hom)
              =
        ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY)
          (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N)) P).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom (𝟙 _))
              ≫
          ((@pullbackTensorIntegralAssociator l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj P)).hom

/-- The normalized integral comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Apply coherent reduction to both
routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  associator. The system comparison associativity equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalIntegralPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_associative l _ E _ _ _ X Y f hX hY) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E X).2
    apply reduced_associativity
      (coherentReduction l E Y) (coherentReduction l E X)
      (constructibleIntegralPullback l E f) (pullbackTensorSequenceDerived l E f)
      (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
      (pullbackTensorCalculus l E Y).systemClosed.tensor
      (pullbackTensorCalculus l E X).systemClosed.tensor
      (reduction_tensor l E Y) (reduction_tensor l E X) (reduction_pullback l E f)
      (pullbackTensorSystemComparison l E f) (canonicalIntegralPullbackTensor l E f)
      (pullbackTensorIntegralAssociator l E Y) (pullbackTensorIntegralAssociator l E X)
      (pullbackTensorCalculus l E Y).systemClosed.monoidal.associator
      (pullbackTensorCalculus l E X).systemClosed.monoidal.associator
    · intro M N P M' N' P' a b c
      exact @MonoidalCategory.associator_naturality _ _
        (pullbackTensorCalculus l E X).systemClosed.monoidal _ _ _ _ _ _ a b c
    · intro M N P
      exact (pullbackTensorIntegralAssociator_existsUnique l E Y M N P).exists.choose_spec
    · intro M N P
      exact (pullbackTensorIntegralAssociator_existsUnique l E X M N P).exists.choose_spec
    · exact integralComparison_reduction l E f
    · exact pullbackTensorSystemComparison_associativity l E f

/-- Coherence for the canonical rational comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalRationalPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : sfRationalConstructibleCategory l E Y),
    ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalAssociator l _
      E _ _ _ Y hY) M N P).hom ≫
            ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M
              (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (N,P))).hom ≫
            ((@rationalDerivedTensor l _ E _ _ _ X hX)).map
              (Prod.mkHom (𝟙 _) ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) N
                P).hom) =
          ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY)
            (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (M,N)) P).hom ≫
            ((@rationalDerivedTensor l _ E _ _ _ X hX)).map
              (Prod.mkHom ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom (𝟙
                _)) ≫
            ((@pullbackTensorRationalAssociator l _ E _ _ _ X hX)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj N)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj P)).hom

attribute [local irreducible] pullbackTensorIntegralAssociator
  pullbackTensorRationalAssociator canonicalIntegralPullbackTensor

section RationalCoherenceElaboration
attribute [local irreducible] sfIntegralConstructible Linear.homModule Preadditive.homGroup

/-- The normalized rational comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Apply coherent reduction to both
routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  associator. The system comparison associativity equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalRationalPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_associative l _ E _ _ _ X Y f hX hY) := by
  intro M N P
  let F := rationalDerivedPullback l E f
  let I := constructibleIntegralPullback l E f
  let Q := sfRationalConstructibleLocalization l E X
  have hF (K) : F.obj K =
      (sfRationalConstructibleLocalization l E X).obj (I.obj K.obj) :=
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K
  have hTY (MN) : (rationalDerivedTensor l E Y).obj MN =
      (sfRationalConstructibleLocalization l E Y).obj
        ((constructibleIntegralTensor l E Y).obj (MN.1.obj,MN.2.obj)) :=
    (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec.1 MN
  have hTX (MN) : (rationalDerivedTensor l E X).obj MN =
      Q.obj ((constructibleIntegralTensor l E X).obj (MN.1.obj,MN.2.obj)) :=
    (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 MN
  have hmap {A B : sfRationalConstructibleCategory l E Y}
      {A' B' : sfIntegralConstructibleCategory l E Y}
      (hA : A = (sfRationalConstructibleLocalization l E Y).obj A')
      (hB : B = (sfRationalConstructibleLocalization l E Y).obj B')
      (a : A ⟶ B) (b : A' ⟶ B')
      (hab : HEq a ((sfRationalConstructibleLocalization l E Y).map b)) :
      HEq (F.map a) (Q.map (I.map b)) := by
    exact map_localized_heq I F (sfRationalConstructibleLocalization l E Y) Q
      (fun {K L} c ↦
        (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K L c 1)
      hA hB a b hab
  have hbase (K) : (F.obj K).obj = I.obj K.obj := by rw [hF]; rfl
  have hty (A B : sfRationalConstructibleCategory l E Y) :
      ((rationalDerivedTensor l E Y).obj (A,B)).obj =
        (constructibleIntegralTensor l E Y).obj (A.obj,B.obj) := by rw [hTY]; rfl
  have htx (A B : sfRationalConstructibleCategory l E X) :
      ((rationalDerivedTensor l E X).obj (A,B)).obj =
        (constructibleIntegralTensor l E X).obj (A.obj,B.obj) := by rw [hTX]; rfl
  have htmap {A B C D : sfRationalConstructibleCategory l E X}
      {A' B' C' D' : sfIntegralConstructibleCategory l E X}
      (hA : A = Q.obj A') (hB : B = Q.obj B')
      (hC : C = Q.obj C') (hD : D = Q.obj D')
      (a : A ⟶ B) (b : C ⟶ D) (a' : A' ⟶ B') (b' : C' ⟶ D')
      (ha : HEq a (Q.map a')) (hb : HEq b (Q.map b')) :
      HEq ((rationalDerivedTensor l E X).map (Prod.mkHom a b))
        (Q.map ((constructibleIntegralTensor l E X).map (Prod.mkHom a' b'))) := by
    subst A B C D
    have ha' := eq_of_heq ha
    have hb' := eq_of_heq hb
    subst a b
    obtain ⟨bil, hbil, hbil'⟩ :=
      (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.2
        (Q.obj A') (Q.obj B') (Q.obj C') (Q.obj D')
    change HEq ((rationalDerivedTensor_existsUnique l E X).exists.choose.map
      (Prod.mkHom (Q.map a') (Q.map b'))) _
    rw [hbil]
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [one_mul, Q, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] using hbil' a' b' 1 1
  have hc (A B B' : sfIntegralConstructibleCategory l E Y) (h : B = B') :
      HEq (Q.map (canonicalIntegralPullbackTensor l E f A B).hom)
        (Q.map (canonicalIntegralPullbackTensor l E f A B').hom) := by
    subst B'
    rfl
  have ha := (pullbackTensorRationalAssociator_existsUnique l E Y M N P).exists.choose_spec
  have ha' := hmap (by rw [hTY, hTY]; rfl) (by rw [hTY, hTY]; rfl) _ _ ha
  have hmid := (canonicalRationalPullbackTensor_existsUnique l E f M
    ((rationalDerivedTensor l E Y).obj (N,P))).exists.choose_spec
  have hmid' : HEq ((canonicalRationalPullbackTensor l E f M
      ((rationalDerivedTensor l E Y).obj (N,P))).hom)
      (Q.map (canonicalIntegralPullbackTensor l E f M.obj
        ((constructibleIntegralTensor l E Y).obj (N.obj,P.obj))).hom) :=
    hmid.trans (hc M.obj _ _ (hty N P))
  have hnp := (canonicalRationalPullbackTensor_existsUnique l E f N P).exists.choose_spec
  have hid : HEq (𝟙 (F.obj M)) (Q.map (𝟙 (I.obj M.obj))) := by
    have hh {A : sfRationalConstructibleCategory l E X}
        {B : sfIntegralConstructibleCategory l E X} (h : A = Q.obj B) :
        HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
    exact hh (hF M)
  have hnp' := htmap (hF M) (hF M) (by rw [hF, hTY]; rfl)
    (by rw [hTX, hF, hF]; rfl) (𝟙 (F.obj M)) _ _ _ hid hnp
  have hleft₁ := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hF, hTY, hTY]; rfl) (by rw [hTX, hF, hF, hTY]; rfl) ha' hmid'
  have hleft := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hTX, hF, hF, hTY]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl) hleft₁ hnp'
  have hmn := (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec
  have hrmid := (canonicalRationalPullbackTensor_existsUnique l E f
    ((rationalDerivedTensor l E Y).obj (M,N)) P).exists.choose_spec
  have hc' (A A' B : sfIntegralConstructibleCategory l E Y) (h : A = A') :
      HEq (Q.map (canonicalIntegralPullbackTensor l E f A B).hom)
        (Q.map (canonicalIntegralPullbackTensor l E f A' B).hom) := by
    subst A'
    rfl
  have hrmid' := hrmid.trans (hc' _ _ P.obj (hty M N))
  have hid' : HEq (𝟙 (F.obj P)) (Q.map (𝟙 (I.obj P.obj))) := by
    have hh {A : sfRationalConstructibleCategory l E X}
        {B : sfIntegralConstructibleCategory l E X} (h : A = Q.obj B) :
        HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
    exact hh (hF P)
  have hmn' := htmap (by rw [hF, hTY]; rfl)
    (by rw [hTX, hF, hF]; rfl) (hF P) (hF P) _ (𝟙 (F.obj P)) _ _ hmn hid'
  have hrassoc := (pullbackTensorRationalAssociator_existsUnique l E X
    (F.obj M) (F.obj N) (F.obj P)).exists.choose_spec
  have has {A B C A' B' C' : sfIntegralConstructibleCategory l E X}
      (hA : A = A') (hB : B = B') (hC : C = C') :
      HEq (Q.map (pullbackTensorIntegralAssociator l E X A B C).hom)
        (Q.map (pullbackTensorIntegralAssociator l E X A' B' C').hom) := by
    subst A' B' C'
    rfl
  have hrassoc' := hrassoc.trans (has (hbase M) (hbase N) (hbase P))
  have hright₁ := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hTX, hF, hTY, hF]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl) hrmid' hmn'
  have hright := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl) hright₁ hrassoc'
  simp only [← Category.assoc]
  apply eq_of_heq
  simp only [← Functor.map_comp] at hleft hright
  have hh := canonicalIntegralPullbackTensor_associative_spec l E f M.obj N.obj P.obj
  simp only [← Category.assoc] at hh
  simpa only [pullbackTensorRationalAssociator, canonicalRationalPullbackTensor, F] using
    hleft.trans ((heq_of_eq (congrArg Q.map hh)).trans hright.symm)

/-- Coherence for the canonical commonstage comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalCommonStagePullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
    ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonAssociator l
      _ Ω _ _ _ Y hY) M N P).hom ≫
            ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M
              (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (N,P))).hom ≫
            ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map
              (Prod.mkHom (𝟙 _) ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) N
                P).hom) =
          ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY)
            (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (M,N)) P).hom ≫
            ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map
              (Prod.mkHom ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom (𝟙
                _)) ≫
            ((@pullbackTensorCommonAssociator l _ Ω _ _ _ X hX)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj P)).hom

/-- Coherence for the canonical integral comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalIntegralPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : sfIntegralConstructibleCategory l E Y),
    ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorIntegralBraiding
      l _ E _ _ _ Y hY) M N).hom ≫
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) N M).hom =
          ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
            ((@pullbackTensorIntegralBraiding l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom

/-- The normalized integral comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Apply coherent reduction to both
routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  braiding. The system comparison signed symmetry equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalIntegralPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E X).2
    let p := reduction_pullback l E f
    exact reduced_braiding
      (coherentReduction l E Y) (coherentReduction l E X)
      (constructibleIntegralPullback l E f) (pullbackTensorSequenceDerived l E f)
      (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
      (pullbackTensorCalculus l E Y).systemClosed.tensor
      (pullbackTensorCalculus l E X).systemClosed.tensor
      (pullbackTensorIntegralReductionTensor l E Y)
      (pullbackTensorIntegralReductionTensor l E X) p
      (canonicalIntegralPullbackTensor l E f)
      (fun M N ↦ (pullbackTensorSystemComparison l E f).app (M, N))
      (pullbackTensorIntegralBraiding l E Y) (pullbackTensorIntegralBraiding l E X)
      (fun M N ↦ (pullbackTensorBraiding
        (coefficientSequenceTopology (ProEt.topology Y)) (coefficientSequenceCommRingSheaf l E Y)
        (pullbackTensorCalculus l E Y).systemClosed
        (pullbackTensorCalculus l E Y).systemTensorModel).app (M, N))
      (pullbackTensorBraiding
        (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
        (pullbackTensorCalculus l E X).systemClosed
        (pullbackTensorCalculus l E X).systemTensorModel)
      (fun M N ↦ (pullbackTensorIntegralBraiding_existsUnique l E Y M N).exists.choose_spec)
      (fun M N ↦ (pullbackTensorIntegralBraiding_existsUnique l E X M N).exists.choose_spec)
      (integralComparison_reduction l E f) (pullbackTensorSystemComparison_braiding l E f)

/-- Coherence for the canonical rational comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalRationalPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : sfRationalConstructibleCategory l E Y),
    ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalBraiding l _ E
      _ _ _ Y hY) M N).hom ≫
            ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) N M).hom =
          ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
            ((@pullbackTensorRationalBraiding l _ E _ _ _ X hX)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom

/-- The normalized rational comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Apply coherent reduction to both
routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  braiding. The system comparison signed symmetry equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalRationalPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    intro M N
    let F := rationalDerivedPullback l E f
    let I := constructibleIntegralPullback l E f
    let Q := sfRationalConstructibleLocalization l E X
    have hF (K) : F.obj K =
        (sfRationalConstructibleLocalization l E X).obj (I.obj K.obj) :=
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K
    have hTY (MN) : (rationalDerivedTensor l E Y).obj MN =
        (sfRationalConstructibleLocalization l E Y).obj
          ((constructibleIntegralTensor l E Y).obj (MN.1.obj,MN.2.obj)) :=
      (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec.1 MN
    have hTX (MN) : (rationalDerivedTensor l E X).obj MN =
        Q.obj ((constructibleIntegralTensor l E X).obj (MN.1.obj,MN.2.obj)) :=
      (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 MN
    have hm : (F.obj M).obj = I.obj M.obj := by
      rw [hF]
      rfl
    have hn : (F.obj N).obj = I.obj N.obj := by
      rw [hF]
      rfl
    have hmap {A B : sfRationalConstructibleCategory l E Y}
        {A' B' : sfIntegralConstructibleCategory l E Y}
        (hA : A = (sfRationalConstructibleLocalization l E Y).obj A')
        (hB : B = (sfRationalConstructibleLocalization l E Y).obj B')
        (a : A ⟶ B) (b : A' ⟶ B')
        (hab : HEq a ((sfRationalConstructibleLocalization l E Y).map b)) :
        HEq (F.map a) (Q.map (I.map b)) := by
      exact map_localized_heq I F (sfRationalConstructibleLocalization l E Y) Q
        (fun {K L} c ↦
          (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K L c 1)
        hA hB a b hab
    have hb := (pullbackTensorRationalBraiding_existsUnique l E Y M N).exists.choose_spec
    have hb' := hmap (hTY (M,N)) (hTY (N,M)) _ _ hb
    have hc := (canonicalRationalPullbackTensor_existsUnique l E f N M).exists.choose_spec
    have hleft := heq_comp
      (by rw [hF, hTY]; rfl)
      (by rw [hF, hTY]; rfl)
      (by rw [hTX, hF, hF]; rfl) hb' hc
    have hd := (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec
    have he := (pullbackTensorRationalBraiding_existsUnique l E X
      (F.obj M) (F.obj N)).exists.choose_spec
    have hsym {A B A' B' : sfIntegralConstructibleCategory l E X}
        (hA : A = A') (hB : B = B') :
        HEq (Q.map (pullbackTensorIntegralBraiding l E X A B).hom)
          (Q.map (pullbackTensorIntegralBraiding l E X A' B').hom) := by
      subst A' B'
      rfl
    have he' : HEq ((pullbackTensorRationalBraiding l E X (F.obj M) (F.obj N)).hom)
        (Q.map ((pullbackTensorIntegralBraiding l E X (I.obj M.obj) (I.obj N.obj)).hom)) :=
      he.trans (hsym hm hn)
    have hright := heq_comp
      (by rw [hF, hTY]; rfl)
      (by rw [hTX, hF, hF]; rfl)
      (by rw [hTX, hF, hF]; rfl) hd he'
    apply eq_of_heq
    refine hleft.trans ?_
    refine (heq_of_eq (Q.map_comp _ _).symm).trans ?_
    rw [canonicalIntegralPullbackTensor_braiding_spec l E f M.obj N.obj]
    exact (heq_of_eq (Q.map_comp _ _)).trans hright.symm

/-- Coherence for the canonical commonstage comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalCommonStagePullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
    ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonBraiding l _
      Ω _ _ _ Y hY) M N).hom ≫
            ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) N M).hom =
          ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
            ((@pullbackTensorCommonBraiding l _ Ω _ _ _ X hX)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom

end RationalCoherenceElaboration

attribute [local irreducible] pullbackTensorIntegralBraiding pullbackTensorRationalBraiding
  rationalDerivedTensor rationalDerivedPullback canonicalRationalPullbackTensor

end HigherCoherence
end WeilConjectures
