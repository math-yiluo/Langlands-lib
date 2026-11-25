/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorIntegralConstruction
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemTensorComparisonComposition
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackTensorCompositionTransport

/-! # Coherent reduction of the canonical integral pullback/tensor comparison

Source: Stacks 07A4 and 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

The coherent reduction of the canonical integral comparison is the transported system
comparison, conjugated by the whole-system pullback comparison of
`integralPullbackSystemComparison` and by the reduction/tensor comparison built from the
Roos-normalized tensor realization and the coherent counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The counit of the coherent reduction/limit adjunction is invertible at system tensors
of reductions of constructible objects.
Source: Stacks 0941 (blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem integralSystemTensor_counit_isIso (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (MN : sfIntegralConstructibleCategory l E W × sfIntegralConstructibleCategory l E W) :
    IsIso ((pullbackTensorCalculus l E W).adjunction.counit.app
      ((pullbackTensorCalculus l E W).systemClosed.tensor.obj
        ((pullbackTensorCalculus l E W).reduction.obj MN.1.obj,
          (pullbackTensorCalculus l E W).reduction.obj MN.2.obj))) :=
  (pullbackTensorComparisonCounits l E (𝟙 W) MN.1 MN.2).1

/-- Coherent reduction carries the constructible integral tensor to the system tensor,
through the Roos-normalized tensor realization and the coherent counit.
Source: Stacks 07A4, 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
def integralSystemTensorReduction (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    constructibleIntegralTensor l E W ⋙
        ((sfIntegralConstructible l E W).ι ⋙ (pullbackTensorCalculus l E W).reduction) ≅
      ((sfIntegralConstructible l E W).ι ⋙ (pullbackTensorCalculus l E W).reduction).prod
        ((sfIntegralConstructible l E W).ι ⋙ (pullbackTensorCalculus l E W).reduction) ⋙
        (pullbackTensorCalculus l E W).systemClosed.tensor :=
  NatIso.ofComponents
    (fun MN ↦ (pullbackTensorCalculus l E W).reduction.mapIso
        ((pullbackTensorIntegralTensorModel l E W).app (MN.1.obj, MN.2.obj)) ≪≫
      @asIso _ _ _ _ ((pullbackTensorCalculus l E W).adjunction.counit.app
        ((pullbackTensorCalculus l E W).systemClosed.tensor.obj
          ((pullbackTensorCalculus l E W).reduction.obj MN.1.obj,
            (pullbackTensorCalculus l E W).reduction.obj MN.2.obj)))
        (integralSystemTensor_counit_isIso l E W MN))
    (by
      intro MN MN' g
      have h₁ := (pullbackTensorIntegralTensorModel l E W).hom.naturality
        (Prod.mkHom g.1.hom g.2.hom)
      have h₂ := (pullbackTensorCalculus l E W).adjunction.counit.naturality
        ((pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom ((pullbackTensorCalculus l E W).reduction.map g.1.hom)
            ((pullbackTensorCalculus l E W).reduction.map g.2.hom)))
      have key : (pullbackTensorCalculus l E W).reduction.map
          ((integralCompletedTensor l E W).map (Prod.mkHom g.1.hom g.2.hom)) ≫
          (pullbackTensorCalculus l E W).reduction.map
            ((pullbackTensorIntegralTensorModel l E W).hom.app (MN'.1.obj, MN'.2.obj)) ≫
          (pullbackTensorCalculus l E W).adjunction.counit.app
            ((pullbackTensorCalculus l E W).systemClosed.tensor.obj
              ((pullbackTensorCalculus l E W).reduction.obj MN'.1.obj,
                (pullbackTensorCalculus l E W).reduction.obj MN'.2.obj)) =
          ((pullbackTensorCalculus l E W).reduction.map
            ((pullbackTensorIntegralTensorModel l E W).hom.app (MN.1.obj, MN.2.obj)) ≫
          (pullbackTensorCalculus l E W).adjunction.counit.app
            ((pullbackTensorCalculus l E W).systemClosed.tensor.obj
              ((pullbackTensorCalculus l E W).reduction.obj MN.1.obj,
                (pullbackTensorCalculus l E W).reduction.obj MN.2.obj))) ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom ((pullbackTensorCalculus l E W).reduction.map g.1.hom)
              ((pullbackTensorCalculus l E W).reduction.map g.2.hom)) := by
        erw [← Functor.map_comp_assoc, h₁, Functor.map_comp, Category.assoc, Category.assoc]
        exact congrArg (_ ≫ ·) h₂
      exact key)

/-- Components of the transported Roos-normalized pullback realization.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem completedQuotientPullbackRealization_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E Y)) :
    (CompletedQuotient.completedQuotientPullbackRealization l E f).hom.app K =
      (pullbackTensorIntegralPullbackModel l E f).hom.app K ≫
        (coefficientSequenceLimit l E X).map ((sequenceDerivedPullbackBridge l E f).hom.app
          ((pullbackTensorCalculus l E Y).reduction.obj K)) :=
  rfl

/-- The whole-system pullback comparison at a constructible object, read in the coherent
sequence-site derived category.
Source: Stacks 099N(5), 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
def integralPullbackSystemComparisonApp {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (pullbackTensorCalculus l E X).reduction.obj ((integralDerivedPullback l E f).obj K.obj) ≅
      (integralComparisonDerivedSequencePullback l E f).obj
        ((pullbackTensorCalculus l E Y).reduction.obj K.obj) :=
  ((integralPullbackSystemComparison l E).choose f).app K

/-- The whole-system pullback comparison is the reduction of the Roos-normalized
realization followed by the coherent counit.
Source: Stacks 099N(5), 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem integralPullbackSystemComparisonApp_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralPullbackSystemComparisonApp l E f K).hom =
      (pullbackTensorCalculus l E X).reduction.map
          ((pullbackTensorIntegralPullbackModel l E f).hom.app K.obj ≫
            (coefficientSequenceLimit l E X).map ((sequenceDerivedPullbackBridge l E f).hom.app
              ((pullbackTensorCalculus l E Y).reduction.obj K.obj))) ≫
        (pullbackTensorCalculus l E X).adjunction.counit.app
          ((integralComparisonDerivedSequencePullback l E f).obj
            ((pullbackTensorCalculus l E Y).reduction.obj K.obj)) := by
  have hβ := @(integralPullbackSystemComparison l E).choose_spec.2
  exact (@hβ X Y hX hY f K).trans
    (congrArg (fun z ↦ (pullbackTensorCalculus l E X).reduction.map z ≫
      (pullbackTensorCalculus l E X).adjunction.counit.app
        ((integralComparisonDerivedSequencePullback l E f).obj
          ((pullbackTensorCalculus l E Y).reduction.obj K.obj)))
      (completedQuotientPullbackRealization_hom_app l E f K.obj))

/-- The coherent reduction of the canonical integral pullback/tensor comparison is the
transported system comparison, conjugated by the whole-system pullback comparisons and the
reduction/tensor comparisons.
Source: Stacks 07A4, 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).
Proof: the whole-system pullback comparison is the reduction of the Roos-normalized
realization followed by the coherent counit (`integralPullbackSystemComparison`). Apply
`reduction_limitConjugate_eq` to the defining composite of
`canonicalIntegralPullbackTensor`. -/
theorem canonicalIntegralPullbackTensor_systemReduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (integralSystemReduction l E X).map (canonicalIntegralPullbackTensor l E f M N).hom =
      ((integralPullbackSystemComparison l E).choose f).hom.app
          ((constructibleIntegralTensor l E Y).obj (M, N)) ≫
        (finiteSystemDerivedPullback (integralSystemRings l E)
          (integralSystemTransition l E) f).map
          ((integralSystemTensorReduction l E Y).hom.app (M, N)) ≫
        (integralSystemTensorComparison l E f).hom.app
          ((integralSystemReduction l E Y).obj M, (integralSystemReduction l E Y).obj N) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom (((integralPullbackSystemComparison l E).choose f).inv.app M)
            (((integralPullbackSystemComparison l E).choose f).inv.app N)) ≫
        (integralSystemTensorReduction l E X).inv.app
          ((constructibleIntegralPullback l E f).obj M,
            (constructibleIntegralPullback l E f).obj N) := by
  have := (pullbackTensorComparisonCounits l E f M N).1
  have := (pullbackTensorComparisonCounits l E f M N).2.1
  have := (pullbackTensorComparisonCounits l E f M N).2.2
  have : IsIso ((pullbackTensorCalculus l E X).adjunction.counit.app
      ((pullbackTensorCalculus l E X).systemClosed.tensor.obj
        ((pullbackTensorCalculus l E X).reduction.obj ((integralDerivedPullback l E f).obj M.obj),
          (pullbackTensorCalculus l E X).reduction.obj
            ((integralDerivedPullback l E f).obj N.obj)))) :=
    integralSystemTensor_counit_isIso l E X
      ((constructibleIntegralPullback l E f).obj M, (constructibleIntegralPullback l E f).obj N)
  have key := reduction_limitConjugate_eq (pullbackTensorCalculus l E Y).reduction
    (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E Y)
    (coefficientSequenceLimit l E X) (pullbackTensorCalculus l E Y).adjunction.counit
    (pullbackTensorCalculus l E X).adjunction.counit (integralDerivedPullback l E f)
    (sequenceDerivedPullbackBridge l E f) (integralCompletedTensor l E Y)
    (integralCompletedTensor l E X) (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (pullbackTensorIntegralPullbackModel l E f) (pullbackTensorIntegralTensorModel l E Y)
    (pullbackTensorIntegralTensorModel l E X) (pullbackTensorSystemComparison l E f)
    M.obj N.obj
    (integralPullbackSystemComparisonApp l E f ((constructibleIntegralTensor l E Y).obj (M, N)))
    (integralPullbackSystemComparisonApp_hom l E f ((constructibleIntegralTensor l E Y).obj (M, N)))
    (integralPullbackSystemComparisonApp l E f M) (integralPullbackSystemComparisonApp_hom l E f M)
    (integralPullbackSystemComparisonApp l E f N) (integralPullbackSystemComparisonApp_hom l E f N)
    ((integralSystemTensorReduction l E Y).app (M, N)) rfl
    ((integralSystemTensorReduction l E X).app
      ((constructibleIntegralPullback l E f).obj M, (constructibleIntegralPullback l E f).obj N))
    rfl
  exact key

end WeilConjectures
