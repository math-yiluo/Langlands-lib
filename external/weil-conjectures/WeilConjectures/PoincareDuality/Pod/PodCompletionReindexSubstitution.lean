/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution

/-! # Coherence of the specified ordinary reindexing comparisons

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-substitution).
All equations below refer to the displayed family's own reduction, limit and tensor maps.
-/

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

universe t u a b s
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The two locations occupied by the item's own source and target systems.
Source: blueprint Steps 1 and 5 (blueprint: def-pod-completion-reindex-substitution). -/
def podReindexLocations (X Y : Scheme.{u}) : Bool → Scheme.{u} :=
  fun b ↦ if b then X else Y

/-- Compare a model's tensor codomain with the fixed quotient/Roos tensor codomain.
The closed-tensor comparison preserves the common internal-Hom adjunction; the
left-adjoint comparison preserves the common total-limit adjunction. These are
isomorphisms of presentations, rather than equalities of chosen tensor functors.
Source: Stacks 07A4, 08J9, 0941; uniqueness of adjoints
(blueprint: def-pod-completion-reindex-substitution). -/
def podReindexTensorCodomainComparison {S : Type s} {W : S → Scheme.{u}}
    (C : CompletedOperations.Models l E W) (a : S) :
    ((C.calculus a).reduction.prod (C.calculus a).reduction) ⋙
        CompletedOperations.tensor l E C a ⋙ coefficientSequenceLimit l E (W a) ≅
      pullbackTensorReferenceTensor l E (W a) :=
  isoWhiskerRight
    (isoWhiskerLeft ((C.calculus a).reduction.prod (C.calculus a).reduction)
        (CoefficientClosedStructure.comparison (C.system a).closed
          (pullbackTensorCalculus l E (W a)).systemClosed) ≪≫
      isoWhiskerRight
        (NatIso.prod
          (Adjunction.leftAdjointUniq (C.calculus a).adjunction
            (pullbackTensorCalculus l E (W a)).adjunction)
          (Adjunction.leftAdjointUniq (C.calculus a).adjunction
            (pullbackTensorCalculus l E (W a)).adjunction))
        (pullbackTensorCalculus l E (W a)).systemClosed.tensor)
    (coefficientSequenceLimit l E (W a))

/-- Substitution for these particular normalized primitives. In addition to the
expression laws, both calculi, completion augmentations, Roos models and the
pullback realization are the ones in D. The primitive limit equation involves
D.limit itself. The tensor transport to the slice presentation is fixed by the same
strict tower used in T.Model, whose canonical comparison is T.Canonical.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: def-pod-completion-reindex-substitution). -/
def PodReindexSubstitution {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D) : Prop :=
  ∃ C : CompletedOperations.Models l E (podReindexLocations X Y),
    ∃ qY : integralCompletedTensor l E Y ≅ IntegralOnSlice.completedTensor l E Y none,
    ∃ qX : integralCompletedTensor l E X ≅ IntegralOnSlice.completedTensor l E X none,
    C.calculus false = podReindexCalculus l E Y ∧
    C.calculus true = podReindexCalculus l E X ∧
    HEq (C.completion false) D.completionSource ∧
    HEq (C.completion true) D.completionTarget ∧
    C.roos false = D.sourceRoos ∧ C.roos true = D.targetRoos ∧
    HEq (C.pullback (a := true) (b := false) g).realization D.pullback ∧
    (qY ≪≫ CompletedOperations.tensorRealization l E C false ≪≫
      podReindexTensorCodomainComparison l E C false) =
        pullbackTensorIntegralTensorModel l E Y ∧
    (qX ≪≫ CompletedOperations.tensorRealization l E C true ≪≫
      podReindexTensorCodomainComparison l E C true) =
        pullbackTensorIntegralTensorModel l E X ∧
    (∀ N : coefficientSequenceDerived l E Y,
      IsNormalizedCoefficientSequence l E Y N →
      (podOrdinaryToCompleted l E g D).app ((coefficientSequenceLimit l E Y).obj N) ≫
        CompletedOperations.pullbackComparison l E C (a := true) (b := false) g N =
          D.limit.hom.app N) ∧
    PodCompletedTensorReindex.Model l E g D T ∧
    PodCompletedTensorReindex.Canonical l E g D T ∧
    CompletedOperations.ComparisonLaws.{u,u,0,0} l E C ∧
    CompletedOperations.SubstitutionLaw.{u,u,0,0,0} l E C ∧
    CompletedOperations.StructuralLaw.{u,u,0,0} l E C

end WeilConjectures
