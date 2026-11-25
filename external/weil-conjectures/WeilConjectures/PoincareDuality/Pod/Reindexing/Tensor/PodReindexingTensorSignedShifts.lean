/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSignedShiftsCore
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSignedSquares

/-! # Signed shifts of fixed normalized tensor reindexing

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-signed-shifts). -/

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

/-- Signed shifts of the same quotient-normalized completion and tensor maps.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 011G, 07A4, 0941 (blueprint: lem-pod-reindexing-tensor-signed-shifts).

Proof: construct left and right tensor-shift comparisons by relabeling the total
tensor summands on flat-term K-flat representatives. The right comparison has
the Koszul factor (-1)^(pr); the left comparison has its prescribed sign.
The signed total differentials verify these are chain isomorphisms for every
integer shift, and the quotient transitions commute with them. Localize these
maps to get SY and SX with their Generators laws. Apply the same two-coordinate
Roos realization used in T.Model to obtain their Model laws. On a shifted Roos
complex the second coordinate is multiplied by (-1)^r, while the first is the
projection-defined shift/product comparison. D.shiftSource.Laws and
D.shiftTarget.Laws fix exactly these maps. D.LimitModel therefore supplies the
two PodLimitSignedShift identities. On the coherent reduction system, shifting
commutes with the quotient tensor generator map, proving CommShift of
D.reduction.hom; the diagonal Roos equation proves CommShift of D.limit.hom.
Finally reindexing preserves degrees and integer signs, so both tensor-shift
squares agree on all homogeneous summands and descend through T.Model.
This verifies negative shifts, shift zero, empty schemes and zero inputs too. -/
theorem podReindexingTensorSignedShifts
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T) :
    ∃ SY : PodTensorSignedShift l E Y, ∃ SX : PodTensorSignedShift l E X,
      PodReindexSignedShifts l E g D T SY SX := by
  obtain ⟨SY, SX, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ :=
    podReindexingTensorSignedShifts_core l E g D hD T hT
  have hs := podReindexingTensorSignedShifts_tensorSquares l E g D hD T hT SY SX h₅ h₆ h₇ h₈
  refine ⟨SY, SX, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, ?_⟩
  intro M N M' N' r a b
  exact ⟨hs.1 M N M' N' r a b, hs.2 M N M' N' r a b⟩

end WeilConjectures
