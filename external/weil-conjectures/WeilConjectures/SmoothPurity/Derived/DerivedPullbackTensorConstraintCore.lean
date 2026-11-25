/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorAssociatorConstraints
import all WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints

import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import all WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.StageTensorBraiding
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import WeilConjectures.SmoothPurity.Integral.IntegralBraidingScalarExtensionSquare
import all Mathlib.Logic.Small.Defs

/-! # Common-stage normalized tensor constraints

The common-stage associator and braiding constraints, using the finite
normalized constraints and the directed-stage representative calculation.
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
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

section HigherCoherence
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

attribute [local irreducible] pullbackTensorIntegralComposition
  pullbackTensorIntegralReductionTensor pullbackTensorIntegralReductionPullback

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

private theorem integralBraiding_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M M' N N' : sfIntegralConstructibleCategory l E W)
    (f : M ⟶ M') (g : N ⟶ N') :
    (constructibleIntegralTensor l E W).map (Prod.mkHom f g) ≫
        (pullbackTensorIntegralBraiding l E W M' N').hom =
      (pullbackTensorIntegralBraiding l E W M N).hom ≫
        (constructibleIntegralTensor l E W).map (Prod.mkHom g f) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).2
    exact reducedBraiding_natural (coherentReduction l E W)
      (constructibleIntegralTensor l E W) (pullbackTensorCalculus l E W).systemClosed.tensor
      (reduction_tensor l E W)
      (fun A B ↦ (pullbackTensorBraiding
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
        (pullbackTensorCalculus l E W).systemClosed
        (pullbackTensorCalculus l E W).systemTensorModel).hom.app (A, B))
      (fun A A' B B' a b ↦ (pullbackTensorBraiding
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
        (pullbackTensorCalculus l E W).systemClosed
        (pullbackTensorCalculus l E W).systemTensorModel).hom.naturality (Prod.mkHom a b))
      (fun A B ↦ (pullbackTensorIntegralBraiding l E W A B).hom)
      (fun A B ↦ (pullbackTensorIntegralBraiding_existsUnique l E W A B).exists.choose_spec)
      M M' N N' f g

private theorem rationalBraiding_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M M' N N' : sfRationalConstructibleCategory l E W)
    (f : M ⟶ M') (g : N ⟶ N') :
    (rationalDerivedTensor l E W).map (Prod.mkHom f g) ≫
        (pullbackTensorRationalBraiding l E W M' N').hom =
      (pullbackTensorRationalBraiding l E W M N).hom ≫
        (rationalDerivedTensor l E W).map (Prod.mkHom g f) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact localizedBraiding_natural
      (R := Padic.coefficientExtensionIntegers l E)
      (A := sfIntegralConstructibleCategory l E W) _ (constructibleIntegralTensor l E W)
      (pullbackTensorIntegralBraiding l E W) (integralBraiding_natural l E W)
      (rationalDerivedTensor l E W) (pullbackTensorRationalBraiding l E W)
      (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
      (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2
      (fun A B ↦ (pullbackTensorRationalBraiding_existsUnique l E W A B).exists.choose_spec)
      M M' N N' f g

private theorem braiding_square_of_iso
    {C D : Type*} [Category* C] [Category* D]
    (U : C × C ⥤ C) (V : D × D ⥤ D) (F G : C ⥤ D) (e : F ≅ G)
    (c : U ⋙ G ≅ G.prod G ⋙ V)
    (β : ∀ A B, U.obj (A, B) ≅ U.obj (B, A))
    (γ : ∀ A B, V.obj (A, B) ≅ V.obj (B, A))
    (hn : ∀ {A A' B B'} (f : A ⟶ A') (g : B ⟶ B'),
      V.map (Prod.mkHom f g) ≫ (γ A' B').hom =
        (γ A B).hom ≫ V.map (Prod.mkHom g f))
    (hc : ∀ A B, G.map (β A B).hom ≫ c.hom.app (B, A) =
      c.hom.app (A, B) ≫ (γ (G.obj A) (G.obj B)).hom)
    (A B : C) :
    F.map (β A B).hom ≫
        ((Functor.isoWhiskerLeft U e ≪≫ c ≪≫
          Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) V).hom.app (B, A)) =
      ((Functor.isoWhiskerLeft U e ≪≫ c ≪≫
          Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) V).hom.app (A, B)) ≫
        (γ (F.obj A) (F.obj B)).hom := by
  dsimp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatIso.prod_hom, NatTrans.prod, Iso.symm_hom]
  simp only [Category.assoc]
  rw [reassoc_of% (e.hom.naturality (β A B).hom), reassoc_of% (hc A B)]
  rw [← hn (e.inv.app A) (e.inv.app B)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarMap_integral_local
    (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (X : Scheme.{u})
    (A B : sfRationalConstructibleCategory l E X)
    (A₀ B₀ : sfIntegralConstructibleCategory l E X)
    (hA : A = (sfRationalConstructibleLocalization l E X).obj A₀)
    (hB : B = (sfRationalConstructibleLocalization l E X).obj B₀)
    (f : A ⟶ B) (f₀ : A₀ ⟶ B₀)
    (hf : HEq f ((sfRationalConstructibleLocalization l E X).map f₀)) :
    HEq ((sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map f)
      ((sfRationalConstructibleLocalization l F X).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι X).map f₀)) := by
  cases hA
  cases hB
  cases hf
  simpa only [map_one, sfRationalConstructibleLocalization, ScalarLocalization.localization,
    sfRationalScalarExtension, sfConstructibleIntegralScalarExtension] using
    sfRationalScalarExtension_map_tmul l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι A₀ B₀ f₀ 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarBraiding_hom_local
    (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K L : sfRationalConstructibleCategory l E X) :
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map
        (pullbackTensorRationalBraiding l E X K L).hom ≫
        (rationalTensorScalarComparison l E F ι X).hom.app (L, K) =
      (rationalTensorScalarComparison l E F ι X).hom.app (K, L) ≫
        (pullbackTensorRationalBraiding l F X
          ((sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj K)
          ((sfRationalScalarExtension l E X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj L)).hom := by
  let S := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι X
  let G := sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let Q := sfRationalConstructibleLocalization l F X
  let TE := rationalDerivedTensor l E X
  let TF := rationalDerivedTensor l F X
  let TI := constructibleIntegralTensor l E X
  let TJ := constructibleIntegralTensor l F X
  have hs (M : sfRationalConstructibleCategory l E X) :
      G.obj M = Q.obj (S.obj M.obj) :=
    sfRationalScalarExtension_obj l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι M
  have ht (M N : sfRationalConstructibleCategory l E X) :
      TE.obj (M, N) = (sfRationalConstructibleLocalization l E X).obj
        (TI.obj (M.obj, N.obj)) :=
    by simpa only [TE, TI, rationalDerivedTensor, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 (M, N)
  have hu (M N : sfRationalConstructibleCategory l E X) :
      G.obj (TE.obj (M, N)) = Q.obj (S.obj (TI.obj (M.obj, N.obj))) := by
    rw [hs, ht]
    rfl
  have hv (M N : sfRationalConstructibleCategory l E X) :
      TF.obj (G.obj M, G.obj N) = Q.obj (TJ.obj (S.obj M.obj, S.obj N.obj)) := by
    rw [hs M, hs N]
    simpa only [TF, TJ, rationalDerivedTensor, Q, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedTensor_existsUnique l F X).exists.choose_spec.1
        (Q.obj (S.obj M.obj), Q.obj (S.obj N.obj))
  have hb := scalarMap_integral_local l E F ι X _ _ _ _ (ht K L) (ht L K) _ _
    ((pullbackTensorRationalBraiding_existsUnique l E X K L).exists.choose_spec)
  have hc (M N : sfRationalConstructibleCategory l E X) :=
    (rationalTensorScalarComparison_existsUnique l E F ι X).exists.choose_spec M N
  have hd : HEq (pullbackTensorRationalBraiding l F X (G.obj K) (G.obj L)).hom
      (Q.map (pullbackTensorIntegralBraiding l F X (S.obj K.obj) (S.obj L.obj)).hom) := by
    have h := (pullbackTensorRationalBraiding_existsUnique l F X
      (G.obj K) (G.obj L)).exists.choose_spec
    have hK := congrArg ScalarLocalization.obj (hs K)
    have hL := congrArg ScalarLocalization.obj (hs L)
    exact h.trans (by
      rw [hK, hL]
      rfl)
  apply eq_of_heq
  refine (heq_comp (hu K L) (hu L K) (hv L K) hb (hc L K)).trans ?_
  refine (heq_of_eq ?_).trans
    (heq_comp (hu K L) (hv K L) (hv L K) (hc K L) hd).symm
  rw [← Q.map_comp, ← Q.map_comp]
  exact congrArg Q.map (integralBraidingScalarExtensionSquare l E F ι X K.obj L.obj)

/-- The rationalized Koszul braiding commutes with the prescribed scalar comparison.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ; the integral
compatibility is `integralBraidingScalarExtensionSquare`, and localization of the
specified maps preserves the square. This includes identity and ramified extensions.
Proof: Every rational object is the localization of its integral object, so the
source and target tensor objects are localized integral tensor objects. The
defining equations of the prescribed rational comparison and braiding identify
them with localizations of the integral comparison and braiding. Scalar extension
sends the localized arrow `1 ⊗ f` to the localization of the integral scalar
extension of `f`. Both composites are then the localization functor applied to
the two composites of the integral scalar square, which agree.
(blueprint: lem-pur-rational-braiding-scalar-extension-square).
-/
theorem rationalBraidingScalarExtensionSquare
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ (E L : AlgebraicallyClosedCoefficients.Index l Ω) (hEL : E ≤ L),
      ∀ (A B : sfRationalConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W),
        (sfRationalScalarExtension l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL)).map
            (pullbackTensorRationalBraiding l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W A B).hom ≫
          (rationalTensorScalarComparison l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) W).hom.app
            (B, A) =
        (rationalTensorScalarComparison l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) W).hom.app
            (A, B) ≫
          (pullbackTensorRationalBraiding l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W
            ((sfRationalScalarExtension l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL)).obj A)
            ((sfRationalScalarExtension l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL)).obj B)).hom := by
  intro E L hEL A B
  exact scalarBraiding_hom_local l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) W A B

section CommonBraidingDescent
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.pairCategory CategoryTheory.uniformProd
attribute [local semireducible] operationStageTransitionIso
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5
attribute [local irreducible] rationalDerivedTensor sfRationalScalarExtension
  rationalTensorScalarComparison ObjectProperty.FullSubcategory.category ScalarLocalization.category
  pullbackTensorRationalBraiding pullbackTensorIntegralBraiding

/-- Existence half of the normalized constraint; uniqueness is proved by the parent theorem.
Source: Stacks 06YS, 07A4, 0941.
(blueprint: lem-pur-derived-pullback-tensor-constraints-common-braiding-existence). -/
theorem pullbackTensorCommonBraiding_exists (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃ e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,N) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (N,M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W M N).stage ≤ L) (hT : (commonStageTensorObject l Ω W N
          M).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M N)
          (commonStageTensorObject l Ω W N M) L hS hT
          ((commonStageTensorComparison l Ω W M N L hS).hom ≫
            ((@pullbackTensorRationalBraiding l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                hS)) (N.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                N.stage).2.trans hS))).hom ≫
            (commonStageTensorComparison l Ω W N M L hT).inv)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let S := stageSystem l Ω W
    let U : BilinearCoefficientDescent.Family S S S :=
      ⟨fun F ↦ rationalDerivedTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) W,
        fun {_ _} h ↦ rationalTensorStageComparison l Ω W h,
        rationalTensorStageComparison_coherent l Ω W⟩
    let join := Padic.finiteCoefficientCompositum l Ω
    let left := fun F L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 F L).1
    let right := fun F L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 F L).2
    have hendpoint (A B : generalAlgebraicallyClosedConstructibleCategory l Ω W)
        (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : join A.stage B.stage ≤ L) :
        BilinearCoefficientDescent.endpoint U join left right (A, B) h =
          commonStageTensorComparison l Ω W A B L h := by
      unfold BilinearCoefficientDescent.endpoint
      change ((rationalTensorStageComparison l Ω W h).app
        (A.toStage (left A.stage B.stage), B.toStage (right A.stage B.stage)) ≪≫
        (rationalDerivedTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W).mapIso
          (Iso.prod ((S.assoc (left A.stage B.stage) h).app A.obj)
            ((S.assoc (right A.stage B.stage) h).app B.obj))) = _
      delta rationalTensorStageComparison commonStageTensorComparison operationStageTransitionIso
      exact tensorStageComparison_endpoint _ _ _ _ _ _ _ _
    let β := fun F ↦ pullbackTensorRationalBraiding l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) W
    have hn : ∀ F {A A' B B'} (a : A ⟶ A') (b : B ⟶ B'),
        (U.U F).map (Prod.mkHom a b) ≫ (β F A' B').hom =
          (β F A B).hom ≫ (U.U F).map (Prod.mkHom b a) := by
      intro F A A' B B' a b
      exact rationalBraiding_natural l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) W A A' B B' a b
    have hc : ∀ {F L} (h : F ≤ L) A B,
        (S.T h).map (β F A B).hom ≫ (U.comparison h).hom.app (B, A) =
          (U.comparison h).hom.app (A, B) ≫
            (β L ((S.T h).obj A) ((S.T h).obj B)).hom := by
      intro F L h A B
      dsimp only [U, S, BilinearCoefficientDescent.Family.U,
        BilinearCoefficientDescent.Family.comparison, rationalTensorStageComparison]
      exact braiding_square_of_iso
        (C := Stage l Ω W F) (D := Stage l Ω W L)
        (U.U F) (U.U L) (S.T h) _
        (eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 F L h))
        (rationalTensorScalarComparison l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F L h) W)
        (β F) (β L)
        (fun {A A' B B'} a b ↦ rationalBraiding_natural l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W A A' B B' a b)
        (rationalBraidingScalarExtensionSquare l Ω W F L h) A B
    obtain ⟨e, he⟩ := BilinearCoefficientDescent.braiding_exists S U join left right β hn hc M N
    change commonStageTensorObject l Ω W M N ≅ commonStageTensorObject l Ω W N M at e
    have hM : (commonStageDerivedTensor l Ω W).obj (M, N) =
        commonStageTensorObject l Ω W M N := by
      simpa only [commonStageDerivedTensor] using
        (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1 M N
    have hN : (commonStageDerivedTensor l Ω W).obj (N, M) =
        commonStageTensorObject l Ω W N M := by
      simpa only [commonStageDerivedTensor] using
        (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1 N M
    obtain ⟨d, hd, -⟩ := existsUnique_iso_of_eq hM hN e
    refine ⟨d, ?_⟩
    intro L hS hT
    refine hd.trans (heq_of_eq ?_)
    have he' := he L hS hT
    change e.hom = ofHom (commonStageTensorObject l Ω W M N)
      (commonStageTensorObject l Ω W N M) L hS hT
      ((BilinearCoefficientDescent.endpoint U join left right (M, N) hS).hom ≫
        (β L (M.toStage ((left _ _).trans hS))
          (N.toStage ((right _ _).trans hS))).hom ≫
        (BilinearCoefficientDescent.endpoint U join left right (N, M) hT).inv) at he'
    apply he'.trans
    apply congrArg
    exact congrArg₂
      (fun a b ↦ a ≫ (β L (M.toStage ((left _ _).trans hS))
        (N.toStage ((right _ _).trans hS))).hom ≫ b)
      (congrArg Iso.hom (hendpoint M N L hS))
      (congrArg Iso.inv (hendpoint N M L hT))

end CommonBraidingDescent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The common-stage braiding has its prescribed representative at every larger field.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Conjugate the rational braiding
by the
  displayed transition/tensor comparisons. Their scalar-extension cocycles show independence of
  enlargement. The inverse formula gives an inverse class. Directedness supplies common stages, and
  a representative determines its colimit hom class uniquely. -/
theorem pullbackTensorCommonBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,N) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (N,M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W M N).stage ≤ L) (hT : (commonStageTensorObject l Ω W N
          M).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M N)
          (commonStageTensorObject l Ω W N M) L hS hT
          ((commonStageTensorComparison l Ω W M N L hS).hom ≫
            ((@pullbackTensorRationalBraiding l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                hS)) (N.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                N.stage).2.trans hS))).hom ≫
            (commonStageTensorComparison l Ω W N M L hT).inv)) := by
  obtain ⟨e, he⟩ := pullbackTensorCommonBraiding_exists l Ω W M N
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  let S := commonStageTensorObject l Ω W M N
  let T := commonStageTensorObject l Ω W N M
  let L := Padic.finiteCoefficientCompositum l Ω S.stage T.stage
  let hS := ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage T.stage).1
  let hT := ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage T.stage).2
  exact eq_of_heq ((hd L hS hT).trans (he L hS hT).symm)

/-- The stage-independent rational braiding class.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonBraiding_existsUnique l _ Ω _ _ _ W hW) M N).exists.choose

end HigherCoherence

end WeilConjectures
