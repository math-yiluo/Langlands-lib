/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition

import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.DeligneLaumon.CommonStagePullbackCompComponent
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackCompositionLocalization
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels

/-! # Finite normalized pullback tensor constraints

The finite composition, associator and braiding constructions, extracted from
the higher constraints module to keep single-file checking within its time limit.
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

/-- The canonical completed composition family, normalized by every finite reduction.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    (@constructibleIntegralPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY) ≅
      (@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY) ⋙ (@constructibleIntegralPullback l _
        E _ _ _ Z X h hZ hX) :=
  (integralPullbackComposition l E).choose h f

/-- The canonical rational composition comparison on unchanged integral objects.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: localize the specified integral
composition
  map and conjugate by the object equalities in rationalDerivedPullback_existsUnique. This fixes
  every component and its inverse, so the required isomorphism exists uniquely. -/
theorem pullbackTensorRationalComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y) :
    ∃! e : ((@rationalDerivedPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@rationalDerivedPullback l _ E _ _ _ Z X h hZ hX)).obj (((@rationalDerivedPullback l _ E _ _
        _ X Y f hX hY)).obj M),
      HEq e.hom ((sfRationalConstructibleLocalization l E Z).map
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M.obj)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.2.1 M)
      ?_
      ((sfRationalConstructibleLocalization l E Z).mapIso
        ((pullbackTensorIntegralComposition l E f h).app M.obj))
    have hf (K) : (rationalDerivedPullback l E f).obj K =
        ⟨(constructibleIntegralPullback l E f).obj K.obj⟩ :=
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K
    have hh (K) : (rationalDerivedPullback l E h).obj K =
        ⟨(constructibleIntegralPullback l E h).obj K.obj⟩ :=
      (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.2.1 K
    rw [hh, hf]
    rfl

/-- Rationalization of the finite-reduction-normalized integral composition.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y) :=
  ((@pullbackTensorRationalComposition_existsUnique l _ E _ _ _ X Y Z f h hX hY hZ) M).exists.choose

section CommonCompositionProof
attribute [local irreducible] commonStagePullbackCompComponent
  commonStagePullbackRationalComposition ScalarLocalization.category

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Existence half of the normalized constraint; uniqueness is proved by the parent theorem.
Source: Stacks 06YS, 07A4, 0941.
(blueprint: lem-pur-derived-pullback-tensor-constraints-common-composition-existence). -/
theorem pullbackTensorCommonComposition_exists {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    ∃ e : ((@commonStageDerivedPullback l _ Ω _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).obj (((@commonStageDerivedPullback l _
        Ω _ _ _ X Y f hX hY)).obj M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L),
        HEq e.hom (ofHom (commonStagePullbackObject l Ω (h ≫ f) M)
          (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f M)) L hM hM
          ((commonStagePullbackComparison l Ω (h ≫ f) M L hM).hom ≫
            ((@pullbackTensorRationalComposition l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X
              Y Z f h hX hY
              hZ)
              (M.toStage hM)).hom ≫
            ((@rationalDerivedPullback l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ Z
              X h hZ hX)).map
              (commonStagePullbackComparison l Ω f M L hM).inv ≫
            (commonStagePullbackComparison l Ω h
              (commonStagePullbackObject l Ω f M) L hM).inv)) := by
  refine ⟨commonStagePullbackCompComponent l Ω h f M, ?_⟩
  intro L hM
  let K := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L
  have hu := pullbackTensorRationalComposition_existsUnique l K f h (M.toStage hM)
  have hi : commonStagePullbackRationalComposition l Ω h f L M hM =
      pullbackTensorRationalComposition l K f h (M.toStage hM) :=
    hu.unique (commonStagePullbackRationalComposition_localization l Ω f h M L hM)
      hu.exists.choose_spec
  have hs := commonStagePullbackCompComponent_stage_representation l Ω h f M L hM
  rw [hi] at hs
  exact hs
end CommonCompositionProof

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Common-stage composition, specified at every larger finite coefficient field.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: represent the rational
composition at the
  stage of M. Conjugate by the three prescribed transition/pullback comparisons. Their scalar
  cocycles identify these representatives at every enlargement. The rational inverse gives an
  inverse class; the representative at the original stage determines the class uniquely. -/
theorem pullbackTensorCommonComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    ∃! e : ((@commonStageDerivedPullback l _ Ω _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).obj (((@commonStageDerivedPullback l _
        Ω _ _ _ X Y f hX hY)).obj M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L),
        HEq e.hom (ofHom (commonStagePullbackObject l Ω (h ≫ f) M)
          (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f M)) L hM hM
          ((commonStagePullbackComparison l Ω (h ≫ f) M L hM).hom ≫
            ((@pullbackTensorRationalComposition l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X
              Y Z f h hX hY
              hZ)
              (M.toStage hM)).hom ≫
            ((@rationalDerivedPullback l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ Z
              X h hZ hX)).map
              (commonStagePullbackComparison l Ω f M L hM).inv ≫
            (commonStagePullbackComparison l Ω h
              (commonStagePullbackObject l Ω f M) L hM).inv)) := by
  obtain ⟨e, he⟩ := pullbackTensorCommonComposition_exists l Ω f h M
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  exact eq_of_heq ((hd M.stage le_rfl).trans (he M.stage le_rfl).symm)

/-- The composition isomorphism represented by the prescribed rational comparison.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  ((@pullbackTensorCommonComposition_existsUnique l _ Ω _ _ _ X Y Z f h hX hY hZ) M).exists.choose

attribute [local irreducible] pullbackTensorIntegralComposition
  pullbackTensorRationalComposition pullbackTensorCommonComposition

/-- Composition equation on the actual canonical integral comparison, with both transports.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalIntegralPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop :=
  ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@constructibleIntegralTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M)
          (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app N)) =
    ((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app
      (((@constructibleIntegralTensor l _ E _ _ _
      Y hY)).obj
      (M,N)) ≫
      ((@constructibleIntegralPullback l _ E _ _ _ Z X h hZ hX)).map
        ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z X h hZ hX)
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
          N)).hom

/-- Composition equation on the actual canonical rational comparison, with both transports.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalRationalPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfRationalConstructibleCategory l E Y) : Prop :=
  ((@canonicalRationalPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@rationalDerivedTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorRationalComposition l _ E _ _ _ X Y Z f h hX hY hZ)
        M).hom) (((@pullbackTensorRationalComposition l _ E _ _ _ X Y Z f h hX hY hZ) N).hom)) =
    ((@pullbackTensorRationalComposition l _ E _ _ _ X Y Z f h hX hY hZ) (((@rationalDerivedTensor l
      _ E _ _ _ Y hY)).obj
      (M,N))).hom ≫
      ((@rationalDerivedPullback l _ E _ _ _ Z X h hZ hX)).map ((@canonicalRationalPullbackTensor l
        _ E _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalRationalPullbackTensor l _ E _ _ _ Z X h hZ hX)
        (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M) (((@rationalDerivedPullback l _
          E _ _ _ X Y f hX hY)).obj N)).hom

/-- Composition equation on the actual canonical commonstage comparison, with both transports.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalCommonStagePullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y) : Prop :=
  ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@commonStageDerivedTensor l _ Ω _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ)
        M).hom) (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) N).hom)) =
    ((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) (((@commonStageDerivedTensor
      l _ Ω _ _ _ Y hY)).obj
      (M,N))).hom ≫
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).map
        ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z X h hZ hX)
        (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
          (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom

/-- Reduction of the actual completed tensor via its fixed Roos realization and counit.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralReductionTensor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (pullbackTensorCalculus l E W).reduction.obj
      (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)).obj ≅
    (pullbackTensorCalculus l E W).systemClosed.tensor.obj
      ((pullbackTensorCalculus l E W).reduction.obj M.obj,
       (pullbackTensorCalculus l E W).reduction.obj N.obj) :=
  (pullbackTensorCalculus l E W).reduction.mapIso
    ((pullbackTensorIntegralTensorModel l E W).app (M.obj,N.obj)) ≪≫
    @asIso _ _ _ _ ((pullbackTensorCalculus l E W).adjunction.counit.app
      ((pullbackTensorCalculus l E W).systemClosed.tensor.obj
        ((pullbackTensorCalculus l E W).reduction.obj M.obj,
         (pullbackTensorCalculus l E W).reduction.obj N.obj)))
      (((@pullbackTensorComparisonCounits l _ E _ _ _ W W (𝟙 W) hW hW) M N).1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reduction of completed pullback via its actual normalized Roos model and counit.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralReductionPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M : sfIntegralConstructibleCategory l E Y) :
    (pullbackTensorCalculus l E X).reduction.obj
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M).obj ≅
    (pullbackTensorSequenceDerived l E f).obj
      ((pullbackTensorCalculus l E Y).reduction.obj M.obj) :=
  letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M M).2.1
  (pullbackTensorCalculus l E X).reduction.mapIso
    ((pullbackTensorIntegralPullbackModel l E f).app M.obj) ≪≫
    asIso ((pullbackTensorCalculus l E X).adjunction.counit.app _)

/-- The actual integral comparison reduces to the same coherent comparison at all levels.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def canonicalIntegralPullbackTensor_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop :=
  (pullbackTensorCalculus l E X).reduction.map
      ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom.hom ≫
    ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ X hX)
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom ≫
    (pullbackTensorCalculus l E X).systemClosed.tensor.map
      (Prod.mkHom ((@pullbackTensorIntegralReductionPullback l _ E _ _ _ X Y f hX hY) M).hom
        ((@pullbackTensorIntegralReductionPullback l _ E _ _ _ X Y f hX hY) N).hom) =
  ((@pullbackTensorIntegralReductionPullback l _ E _ _ _ X Y f hX hY)
      (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N))).hom ≫
    (pullbackTensorSequenceDerived l E f).map
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ Y hY) M N).hom ≫
    (pullbackTensorSystemComparison l E f).hom.app
      ((pullbackTensorCalculus l E Y).reduction.obj M.obj,
       (pullbackTensorCalculus l E Y).reduction.obj N.obj)

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

attribute [local irreducible] pullbackTensorIntegralReductionTensor
  pullbackTensorIntegralReductionPullback

/-- The integral associator is uniquely fixed in the coherent reduction category.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Reduction is fully faithful on
  derived-complete constructible objects: its unit is invertible by normalized DVR effectivity.
  Conjugate the specified coherent tensor associator by the actual reduction/tensor comparisons and
  lift along that fully faithful functor. Lift the inverse too; faithfulness gives the inverse
  identities and uniqueness. -/
theorem pullbackTensorIntegralAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (((@constructibleIntegralTensor l _
      E _ _ _ W hW)).obj (M,N),P)
      ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,((@constructibleIntegralTensor l _ E
        _ _ _ W hW)).obj (N,P)),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M
          (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,P))).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N P).hom) =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW)
        (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)) P).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom (𝟙 _)) ≫
        ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator
          ((pullbackTensorCalculus l E W).reduction.obj M.obj)
          ((pullbackTensorCalculus l E W).reduction.obj N.obj)
          ((pullbackTensorCalculus l E W).reduction.obj P.obj)).hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    simpa only [coherentReduction, Functor.comp_map, ObjectProperty.ι_map,
      Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
      Category.assoc] using
      existsUnique_iso_of_map_constraints (coherentReduction l E W)
      (A := (constructibleIntegralTensor l E W).obj
        ((constructibleIntegralTensor l E W).obj (M,N),P))
      (B := (constructibleIntegralTensor l E W).obj
        (M,(constructibleIntegralTensor l E W).obj (N,P)))
      (pullbackTensorIntegralReductionTensor l E W
        ((constructibleIntegralTensor l E W).obj (M,N)) P)
      ((pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
        (Iso.prod (pullbackTensorIntegralReductionTensor l E W M N) (Iso.refl _)))
      ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator _ _ _)
      (pullbackTensorIntegralReductionTensor l E W M
        ((constructibleIntegralTensor l E W).obj (N,P)))
      ((pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
        (Iso.prod (Iso.refl _) (pullbackTensorIntegralReductionTensor l E W N P)))

/-- The canonical completed associator, fixed by its coherent reduction.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralAssociator_existsUnique l _ E _ _ _ W hW) M N P).exists.choose

/-- The rational associator is the actual localization of the integral map.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Use the object equalities in
  rationalDerivedTensor_existsUnique to identify the endpoints. Localize the preceding integral
  isomorphism and its inverse. The displayed equality fixes its hom, so the isomorphism is unique.
-/
theorem pullbackTensorRationalAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (((@rationalDerivedTensor l _ E _ _ _ W
      hW)).obj (M,N),P) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,((@rationalDerivedTensor l _ E _ _ _ W
        hW)).obj (N,P)),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralAssociator l _ E _ _ _ W hW) M.obj N.obj P.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hT (MN) : (rationalDerivedTensor l E W).obj MN =
        ⟨(constructibleIntegralTensor l E W).obj (MN.1.obj,MN.2.obj)⟩ :=
      (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 MN
    apply existsUnique_iso_of_eq ?_ ?_
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralAssociator l E W M.obj N.obj P.obj))
    · rw [hT, hT]
      rfl
    · rw [hT, hT]
      rfl

/-- The localized integral associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalAssociator_existsUnique l _ E _ _ _ W hW) M N P).exists.choose

/-- The integral braiding is uniquely fixed in the coherent reduction category.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Reduction is fully faithful on
  derived-complete constructible objects: its unit is invertible by normalized DVR effectivity.
  Conjugate the specified coherent tensor Koszul symmetry by the actual reduction/tensor comparisons
  and lift along that fully faithful functor. Lift the inverse too; faithfulness gives the inverse
  identities and uniqueness. -/
theorem pullbackTensorIntegralBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,M),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N M).hom =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom ≫
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel).hom.app
            ((pullbackTensorCalculus l E W).reduction.obj M.obj,
             (pullbackTensorCalculus l E W).reduction.obj N.obj) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    simpa only [coherentReduction, Functor.comp_map, ObjectProperty.ι_map,
      Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
      Category.assoc] using
      existsUnique_iso_of_map_constraint (coherentReduction l E W)
      (A := (constructibleIntegralTensor l E W).obj (M,N))
      (B := (constructibleIntegralTensor l E W).obj (N,M))
      (pullbackTensorIntegralReductionTensor l E W M N)
      ((pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (pullbackTensorCalculus l E W).systemClosed
        (pullbackTensorCalculus l E W).systemTensorModel).app
          ((pullbackTensorCalculus l E W).reduction.obj M.obj,
            (pullbackTensorCalculus l E W).reduction.obj N.obj))
      (pullbackTensorIntegralReductionTensor l E W N M)

/-- The canonical completed braiding, fixed by its coherent reduction.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralBraiding_existsUnique l _ E _ _ _ W hW) M N).exists.choose

/-- The rational braiding is the actual localization of the integral map.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Use the object equalities in
  rationalDerivedTensor_existsUnique to identify the endpoints. Localize the preceding integral
  isomorphism and its inverse. The displayed equality fixes its hom, so the isomorphism is unique.
-/
theorem pullbackTensorRationalBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (N,M),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralBraiding l _ E _ _ _ W hW) M.obj N.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (M,N))
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (N,M))
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralBraiding l E W M.obj N.obj))

/-- The localized integral braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalBraiding_existsUnique l _ E _ _ _ W hW) M N).exists.choose

end HigherCoherence

end WeilConjectures
