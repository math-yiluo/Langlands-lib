/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.CharP.Basic
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.Algebra.CharP.Lemmas

/-!
# Étaleness of the Frobenius polynomial solution algebra

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-frobenius-polynomial-etale).
-/

@[expose] public section

set_option autoImplicit false

universe u

open MvPolynomial

namespace Algebra

/-- The solution algebra for a Frobenius-semilinear inhomogeneous system is étale.

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-frobenius-polynomial-etale).

Proof: use the displayed finite presentation, with each relation paired to its
corresponding variable. In characteristic `p`, the derivative of each `p`th power
vanishes. The Jacobian is therefore the identity matrix and its determinant is one.
This is a square Jacobian presentation, hence an étale algebra. The empty system
uses the determinant of the empty identity matrix, again one.
-/
theorem frobenius_polynomial_etale
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (n : ℕ) (a : Fin n → Fin n → R) (b : Fin n → R) :
    Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range
      (fun i : Fin n ↦ C (b i) + X i - ∑ j, C (a i j) * X j ^ p))) := by
  classical
  let r : Fin n → MvPolynomial (Fin n) R :=
    fun i ↦ C (b i) + X i - ∑ j, C (a i j) * X j ^ p
  let P : PreSubmersivePresentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range r)) (Fin n) (Fin n) :=
    { Presentation.naive (v := r) with map := _root_.id, map_inj := Function.injective_id }
  have hderiv (i j : Fin n) : pderiv i (r j) = if i = j then 1 else 0 := by
    simp [r, map_sub, map_add, map_sum, Pi.single_apply, eq_comm]
  have hmatrix : P.jacobiMatrix = 1 := by
    ext i j : 1
    simpa [P, PreSubmersivePresentation.jacobiMatrix_apply, Matrix.one_apply,
      Pi.single_apply] using hderiv i j
  have hjac : P.jacobian = 1 := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hmatrix, Matrix.det_one,
      map_one]
  exact (show SquareJacobianPresentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range r)) (Fin n) from
    { P with jacobian_isUnit := by rw [hjac]; exact isUnit_one, map_eq_id := rfl }).etale

end Algebra
