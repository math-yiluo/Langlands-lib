/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexSubstitution
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSubstitutionCore

/-! # Substitution with fixed normalized reindexing primitives

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-substitution). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Substitute normalized systems using these particular reindexing primitives.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4, 0941 (blueprint: lem-pod-reindexing-tensor-substitution).

Proof: present the completed-operation models on the two Bool locations using
the fixed calculi podReindexCalculus, the completion comparisons and Roos models
of D. The canonical closed total-tensor presentations identify their system and
integral closed structures with those of these calculi. At g use D.pullback;
its PullbackNormalization is precisely the required representative normalization.
At other morphisms use the same normalized pullback construction. Thus no
independently chosen limit or completion maps replace those in D.
Choose qY and qX by composing the given integral tensor realization with the
inverse tensor realization of these models. This gives their two HEq equations.
The primitive pullback formula is realization followed by the full-system
counit. Substitute D.Counit into this formula and use the right triangle
identity: F(unit) followed by this primitive comparison is exactly D.limit.
The completion and Roos coordinate laws supply all other displayed pins.
Normalized reconstruction makes the counit invertible on normalized systems.
Tensor and pullback preserve normalization on quotient representatives.
The expression induction of completed-operation substitution now applies to
these same primitives: naturality gives ComparisonLaws, induction on the outer
expression gives SubstitutionLaw, and conjugation by the invertible expression
comparisons gives StructuralLaw. Keep T.Model and T.Canonical unchanged.
All steps concern whole systems, work without boundedness, and include an empty
scheme or empty expression family. -/
theorem podReindexingTensorSubstitution
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T) :
    PodReindexSubstitution l E g D T := by
  obtain ⟨core, _⟩ := podReindexingTensorSubstitutionCore l E g D hD T hT
  rcases hT with ⟨_, _, _, _, hModel, hCanonical⟩
  refine ⟨core.C, core.qY, core.qX, core.calculus_false, core.calculus_true,
    core.completion_false, core.completion_true, core.roos_false, core.roos_true,
    core.pullback, core.tensor_Y, core.tensor_X, core.limit, hModel, hCanonical,
    core.comparisonLaws, core.substitutionLaw, core.structuralLaw⟩

end WeilConjectures
