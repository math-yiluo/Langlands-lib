/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorRoosStrict

/-! # Strict steps in normalized completed tensor reindexing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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

/-- The canonical derived comparison realizes the normalized strict Roos map.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-tensor-roos-normalization).

Proof: take simultaneous flat-term K-flat P,Q. Their finite tensor reductions
are the total tensors of the quotient complexes. The forward generator law
identifies T.tower with the ordinary finite pullback/tensor comparison conjugated
by the two quotient comparisons of D. The quotient-transition squares identify
these comparisons on the entire coherent system, not just its evaluations.
Apply the specified Roos realization: its two cone coordinates are fixed by
D.RoosFst and D.RoosSnd, so the realized map is D.roos followed by Roos(T.tower).
Use D.FiniteModel and D.LimitModel to identify its source and target with the
existing completed operations. D.Unit, D.Counit, and D.PullbackNormalization
identify the resulting derived comparison with the canonical completed
pullback/tensor map after podOrdinaryToCompleted on all three objects.
The assumed Canonical equation and invertibility of the ordinary-to-completed
maps on the complete constructible inputs therefore give the displayed Model
equation by cancellation. Naturality of the strict tower maps ensures this
calculation respects morphisms of representatives. No assertion of equality is
inferred from faithfulness of finite evaluation; the whole-system unit/counit
and the two Roos coordinates are used before localization. Zero representatives
and empty schemes satisfy the same identities. -/
theorem podReindexingTensorRoosNormalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hgen : PodCompletedTensorReindex.Generators l E g D T)
    (hnat : PodCompletedTensorReindex.TowerNaturality l E g D T)
    (hcanonical : PodCompletedTensorReindex.Canonical l E g D T) :
    PodCompletedTensorReindex.Model l E g D T := by
  have hpair := podReindexingTensorRoosNormalization_model_iff_canonical
    l E g D hD T hgen
  have _ := hnat
  exact hpair.mpr (fun P Q hP hQ ↦ hcanonical ⟨_,hP⟩ ⟨_,hQ⟩)

end WeilConjectures
