/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorSignedShiftDescent

/-! # Signed tensor shift models

The construction of the two signed tensor shift structures is isolated from the
compatibility calculation for a fixed reindexing comparison.
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Existence of the signed tensor shift models and their two intrinsic laws.

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-signed-shifts-core-models-r3).

Proof: on flat-term K-flat representatives, relabel the direct-sum tensor
summands for each integer shift.  The first relabelling has no Koszul factor;
the second has the factor `(-1)^(pr)`.  The signed total differential and all
finite quotient transitions are preserved by these maps.  Localize the maps
to obtain the two derived shift fields.  The same representative calculation,
followed by the normalized Roos comparison, proves `Generators` and `Model`.
The construction is independent for the source and target schemes and applies
to negative shifts and zero complexes.
-/
theorem podReindexingTensorSignedShiftModels
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T) :
    ∃ SY : PodTensorSignedShift l E Y, ∃ SX : PodTensorSignedShift l E X,
      SY.Generators l E ∧ SX.Generators l E ∧
      SY.Model l E D.shiftSource ∧ SX.Model l E D.shiftTarget := by
  have _tensorLaws := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hY, hX, _⟩ := hD
  obtain ⟨LY, RY, mY⟩ := podTensorSignedShiftDescent l E Y D.shiftSource hY
  obtain ⟨LX, RX, mX⟩ := podTensorSignedShiftDescent l E X D.shiftTarget hX
  exact ⟨podTensorSignedShiftOfDerived l E Y LY RY,
    podTensorSignedShiftOfDerived l E X LX RX,
    podTensorSignedShiftOfDerived_generators l E Y LY RY,
    podTensorSignedShiftOfDerived_generators l E X LX RX, mY, mX⟩

end WeilConjectures
