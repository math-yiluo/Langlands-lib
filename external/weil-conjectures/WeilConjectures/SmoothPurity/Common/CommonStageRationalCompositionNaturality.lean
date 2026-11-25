/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints

import all Mathlib.Logic.Small.Defs

/-! # Rational pullback compositor naturality

Source: purity/trace equivariance proof Step 1, canonical pullback compositors.
(blueprint: lem-pur-common-stage-rational-composition-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

-- Use the same cached category structures as the coefficient comparison APIs.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
  GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.category StageSystem.instCategoryPairCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  StageSystem.ι sfRationalConstructibleLocalization ScalarLocalization.localization
  commonStagePullbackObject

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback
  constructibleIntegralPullback Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  sfRationalScalarExtension rationalPullbackScalarComparison sfRationalScalarComp

private theorem normalization_map_heq
    {C B : Type*} [Category* C] [Category* B] (F : C ⥤ B)
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

/-- The rational pullback composition comparison is natural in the input morphism.
Source: blueprint purity/trace equivariance Step 1, rationalized pullback composition.
(blueprint: lem-pur-common-stage-rational-composition-naturality).
Proof: decompose a morphism in the localized tensor category into zero, pure tensor,
and sums. For a pure tensor, the defining localization formula reduces the claim to
naturality of the integral pullback compositor. The zero and additive cases follow
from the additive functor structures. Object equalities are transported explicitly. -/
theorem commonStageRationalComposition_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (h : Z ⟶ X)
    {K L : sfRationalConstructibleCategory l E Y} (a : K ⟶ L) :
    (rationalDerivedPullback l E (h ≫ f)).map a ≫
        (pullbackTensorRationalComposition l E f h L).hom =
      (pullbackTensorRationalComposition l E f h K).hom ≫
        (rationalDerivedPullback l E h).map ((rationalDerivedPullback l E f).map a) := by
  have obj {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M : sfRationalConstructibleCategory l E W) :
      (rationalDerivedPullback l E g).obj M =
        ⟨(constructibleIntegralPullback l E g).obj M.obj⟩ :=
    by simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 M
  have hom {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M N : sfIntegralConstructibleCategory l E W) (b : M ⟶ N)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((rationalDerivedPullback l E g).map
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] b))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E g).map b) := by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2 M N b c
  have : (rationalDerivedPullback l E (h ≫ f)).Additive :=
    by simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.1
  have : (rationalDerivedPullback l E f).Additive :=
    by simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
  have : (rationalDerivedPullback l E h).Additive :=
    by simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.1
  have compobj (M) : (rationalDerivedPullback l E h).obj
      ((rationalDerivedPullback l E f).obj M) =
      ⟨(constructibleIntegralPullback l E h).obj
        ((constructibleIntegralPullback l E f).obj M.obj)⟩ := by
    rw [obj, obj]
  have hc (M) := (pullbackTensorRationalComposition_existsUnique l E f h M).exists.choose_spec
  induction a using TensorProduct.inductionOn with
  | tmul c a =>
    have hm := (normalization_map_heq (rationalDerivedPullback l E h) (obj f K) (obj f L)
      (hom f K.obj L.obj a c)).trans
        (hom h _ _ ((constructibleIntegralPullback l E f).map a) c)
    have hleft := heq_comp (obj (h ≫ f) K) (obj (h ≫ f) L) (compobj L)
      (hom (h ≫ f) K.obj L.obj a c) (hc L)
    have hright := heq_comp (obj (h ≫ f) K) (compobj K) (compobj L) (hc K) hm
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app L.obj)
        (c ⊗ₜ (constructibleIntegralPullback l E (h ≫ f)).map a) =
      ScalarLocalization.composition _ _ _ _ _ _
        (c ⊗ₜ (constructibleIntegralPullback l E h).map
          ((constructibleIntegralPullback l E f).map a))
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app K.obj)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    exact congrArg (fun b ↦ c ⊗ₜ b)
      ((pullbackTensorIntegralComposition l E f h).hom.naturality a)
  | add a b ha hb =>
    change (rationalDerivedPullback l E (h ≫ f)).map (a + b : K ⟶ L) ≫ _ =
      _ ≫ (rationalDerivedPullback l E h).map
        ((rationalDerivedPullback l E f).map (a + b : K ⟶ L))
    rw [Functor.map_add, Functor.map_add, Functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add, ha, hb]

end WeilConjectures
