/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorTensorCounit
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorPullbackCounit

import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # The canonical integral pullback/tensor comparison

Source: Stacks 07A4 and 0941. The existing coherent-counit construction is
separated from its scalar compatibility proof to allow that proof to use the
strict quotient realization lemmas without an import cycle.
(blueprint: def-pur-completed-pullback-tensor-integral-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

section CoherentSystems

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem pullbackTensorSequenceRing_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f = integralComparisonSequenceRingMap l E f := by
  unfold pullbackTensorSequenceRing pullbackTensorSequenceRingMap
  rfl

attribute [local irreducible] pullbackTensorIntegralTensorNormalization

/-- The systems used in the integral comparison are normalized, so the actual
reduction/limit counits on them are invertible.
Source: Stacks 0941; Bhatt--Scholze 3.4.12 (blueprint:
def-pur-completed-pullback-tensor-construction).
Proof: the reduction systems of constructible inputs are normalized. Tensor and
constant-coefficient inverse image preserve the Cartesian quotient comparisons
by their flat K-flat models, including ramified transitions. The normalized DVR
effectivity theorem identifies the displayed counits as equivalences. -/
theorem pullbackTensorComparisonCounits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    [_hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    IsIso ((pullbackTensorCalculus l E Y).adjunction.counit.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj
        ((pullbackTensorCalculus l E Y).reduction.obj M.obj,
          (pullbackTensorCalculus l E Y).reduction.obj N.obj))) ∧
    IsIso ((pullbackTensorCalculus l E X).adjunction.counit.app
      ((pullbackTensorSequenceDerived l E f).obj
        ((pullbackTensorCalculus l E Y).reduction.obj M.obj))) ∧
    IsIso ((pullbackTensorCalculus l E X).adjunction.counit.app
      ((pullbackTensorSequenceDerived l E f).obj
        ((pullbackTensorCalculus l E Y).reduction.obj N.obj))) := by
  have hY' : ∀ y : Y, IsUnit (l : Y.residueField y) :=
    fun y ↦ isUnit_of_invertible (l : Y.residueField y)
  have hX' : ∀ x : X, IsUnit (l : X.residueField x) :=
    fun x ↦ isUnit_of_invertible (l : X.residueField x)
  have h₁ := completedPullbackTensor_tensor_counit l E Y hY'
    (pullbackTensorCalculus l E Y) M.obj N.obj
  have heq : pullbackTensorSequenceInverse l E f =
      integralComparisonSequencePullback l E f := by
    unfold pullbackTensorSequenceInverse integralComparisonSequencePullback
    congr 1
    unfold pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
    rw [pullbackTensorSequenceRing_eq]
    rfl
  have h₂ := completedPullbackTensor_pullback_counit l E f hX' hY'
    (pullbackTensorCalculus l E X) (pullbackTensorCalculus l E Y)
    (pullbackTensorSequenceInverse l E f) heq M.obj
  have h₃ := completedPullbackTensor_pullback_counit l E f hX' hY'
    (pullbackTensorCalculus l E X) (pullbackTensorCalculus l E Y)
    (pullbackTensorSequenceInverse l E f) heq N.obj
  refine ⟨?_, ?_, ?_⟩
  · exact h₁
  · exact h₂
  · exact h₃

/-- The integral comparison in coherent coordinates is exactly Rlim of the
canonical system comparison, conjugated only by the specified coherent counits.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorReferenceComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (pullbackTensorReferencePullback l E f).obj
      ((pullbackTensorReferenceTensor l E Y).obj (M.obj,N.obj)) ≅
    (pullbackTensorReferenceTensor l E X).obj
      ((pullbackTensorReferencePullback l E f).obj M.obj,
        (pullbackTensorReferencePullback l E f).obj N.obj) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M N).1
      letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M N).2.1
      letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M N).2.2
      (coefficientSequenceLimit l E X).mapIso
        ((pullbackTensorSequenceDerived l E f).mapIso
          (asIso ((pullbackTensorCalculus l E Y).adjunction.counit.app
            ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj
              ((pullbackTensorCalculus l E Y).reduction.obj M.obj,
                (pullbackTensorCalculus l E Y).reduction.obj N.obj))))) ≪≫
      (coefficientSequenceLimit l E X).mapIso
        ((pullbackTensorSystemComparison l E f).app
          ((pullbackTensorCalculus l E Y).reduction.obj M.obj,
            (pullbackTensorCalculus l E Y).reduction.obj N.obj)) ≪≫
      (coefficientSequenceLimit l E X).mapIso
        ((pullbackTensorCalculus l E X).systemClosed.tensor.mapIso
          (Iso.prod
            (asIso ((pullbackTensorCalculus l E X).adjunction.counit.app
              ((pullbackTensorSequenceDerived l E f).obj
                ((pullbackTensorCalculus l E Y).reduction.obj M.obj)))).symm
            (asIso ((pullbackTensorCalculus l E X).adjunction.counit.app
              ((pullbackTensorSequenceDerived l E f).obj
                ((pullbackTensorCalculus l E Y).reduction.obj N.obj)))).symm))

attribute [local irreducible] pullbackTensorReferenceComparison

/-- The canonical completed integral comparison, transported from the actual
coherent-system Rlim map to the recorded completed operations and their full
constructible subcategories.
Source: Stacks 07A4 and 0941 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def canonicalIntegralPullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@IntegralPullbackTensorComparison l _ E _ _ _ X Y f hX hY) := fun M N ↦
  ObjectProperty.isoMk _
    ((pullbackTensorIntegralPullbackModel l E f).app
        ((integralCompletedTensor l E Y).obj (M.obj,N.obj)) ≪≫
      (pullbackTensorReferencePullback l E f).mapIso
        ((pullbackTensorIntegralTensorModel l E Y).app (M.obj,N.obj)) ≪≫
      (@pullbackTensorReferenceComparison l _ E _ _ _ X Y f hX hY) M N ≪≫
      (pullbackTensorReferenceTensor l E X).mapIso
        (Iso.prod ((pullbackTensorIntegralPullbackModel l E f).app M.obj).symm
          ((pullbackTensorIntegralPullbackModel l E f).app N.obj).symm) ≪≫
      ((pullbackTensorIntegralTensorModel l E X).app
        ((integralDerivedPullback l E f).obj M.obj,
          (integralDerivedPullback l E f).obj N.obj)).symm)

end CoherentSystems

end WeilConjectures
