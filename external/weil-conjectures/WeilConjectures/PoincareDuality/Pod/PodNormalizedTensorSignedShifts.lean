/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCompletionUnitTensor
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSignedShifts

/-! # Signed tensor shifts for arbitrary normalized reindexing data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The signed completed tensor shift square for every representative-normalized datum.
Source: blueprint theorem-poincare-duality-frobenius--2, Step 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-normalized-tensor-signed-shifts).

Proof: take the signed total-tensor shift on flat-term K-flat complexes. Its first
factor map reindexes homogeneous summands; its second factor map multiplies degree p
by (-1)^(p*r). Flatness and K-flatness are preserved by every integer shift.
The quotient tower retains these generator formulas at every level and transition.
Apply the two-coordinate signed Roos shift fixed by A.shiftSource and A.shiftTarget.
A's RoosShift law identifies reindexing before and after this signed shift. On each
finite homogeneous generator the tensor comparison T sends x tensor y to Fx tensor Fy,
so the first-factor square is literal relabelling and the second has the same sign
(-1)^(p*r) on both routes. Generator extensionality gives the strict tower equations.
The normalized Roos and T.Model equations descend them to all derived presentations.
Define SY.left/right and SX.left/right using the localized shift maps, transported
through each supplied presentation isomorphism. Naturality gives their Model laws
for every representative. The reduction/limit comparisons commute with canonical
shifts by their unit/counit and representative normalizations; the limit signed-model
identities follow from the same two Roos coordinates. These yield all conjuncts of
PodReindexSignedShifts. No finite Tor bound is used, and arbitrary signed shifts,
zero complexes and empty schemes obey the same formulas. -/
theorem podNormalized_tensor_signed_shifts
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T) :
    ∃ (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X),
      PodReindexSignedShifts l E g A T SY SX := by
  exact podReindexingTensorSignedShifts l E g A hA T hT

end WeilConjectures
