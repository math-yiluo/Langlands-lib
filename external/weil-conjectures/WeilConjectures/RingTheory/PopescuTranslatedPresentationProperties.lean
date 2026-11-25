/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-! # Applying a quotient section to a Jacobian identity

Source: Stacks Project, Tag 07CR, constant coefficients and the identity for `uπ`.
(blueprint: lem-weil-pbc-popescu-translated-presentation-properties).
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial

/-- A section killing the generators converts a witnessed Jacobian identity to constant minors.

Source: Stacks Project, Tag 07CR, the equations preceding the use of Tag 07DQ.
(blueprint: lem-weil-pbc-popescu-translated-presentation-properties).

Proof: compose evaluation with the quotient map and `ρ`. Since the generators map to
zero, this composite equals constant evaluation followed by the quotient map of `R`:
the two algebra homomorphisms agree on constants and variables. Applying it to each
relation shows its constant coefficient belongs to `(π⁴)`, giving the scalars `a`.
Apply it to the supplied minor identity. Homomorphisms commute with finite sums,
products and determinants. Lift each of the finitely many images of `b I` to a scalar
`d I` in `R`. If `S` is the sum of these scalars times the constant minors, this gives
`π - S ∈ (π⁴)`, so `π - S = π⁴ t`. Rearrangement gives `(1 - π³ t)π = S`.
Each minor is one of the stated generators after transposition, which preserves the
determinant, and an ideal is closed under scalar multiplication and finite sums.
No cancellation of `π` is involved, including when `π = 0` or is a zero divisor. -/
theorem exists_popescu_translated_presentation_properties
    (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] (π : R)
    (ρ : (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
      (R ⧸ Ideal.span {π ^ 4}))
    (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m)) (hc : c ≤ min n m)
    (b : {I : Finset (Fin n) // I.card = c} → A)
    (hzero : ∀ i, ρ (Ideal.Quotient.mk _ (P.val i)) = 0)
    (hminor : algebraMap R A π = ∑ I : {I : Finset (Fin n) // I.card = c}, b I *
      Matrix.det (fun j i : Fin c =>
        aeval P.val (pderiv (I.val.orderEmbOfFin I.property i)
          (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j))))) :
    ∃ (a : Fin m → R) (t : R),
      (∀ j, constantCoeff (P.relation j) = π ^ 4 * a j) ∧
      (1 - π ^ 3 * t) * π ∈ Ideal.span (Set.range
        (fun I : {I : Finset (Fin n) // I.card = c} ↦
          (Matrix.submatrix
            (fun i j ↦ constantCoeff
              (pderiv i (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j))))
            (I.val.orderEmbOfFin I.property) (fun j ↦ j)).det)) := by
  classical
  let q : A →ₐ[R] R ⧸ Ideal.span {π ^ 4} :=
    ρ.comp (Ideal.Quotient.mkₐ R _)
  have heval : q.comp (aeval P.val) = aeval (fun _ : Fin n => 0) := by
    ext i
    simpa [q] using hzero i
  have hconst (f : MvPolynomial (Fin n) R) :
      q (aeval P.val f) = Ideal.Quotient.mk _ (constantCoeff f) := by
    have h := DFunLike.congr_fun heval f
    simpa only [AlgHom.comp_apply, aeval_zero', Ideal.Quotient.algebraMap_eq] using h
  have ha (j : Fin m) : ∃ a : R, constantCoeff (P.relation j) = π ^ 4 * a := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hconst, P.aeval_val_relation, map_zero]
  choose a ha using ha
  let D : {I : Finset (Fin n) // I.card = c} → R := fun I =>
    Matrix.det (fun j i : Fin c => constantCoeff
      (pderiv (I.val.orderEmbOfFin I.property i)
        (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j))))
  have hD (I : {I : Finset (Fin n) // I.card = c}) :
      q (Matrix.det (fun j i : Fin c =>
        aeval P.val (pderiv (I.val.orderEmbOfFin I.property i)
          (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j))))) =
        Ideal.Quotient.mk (Ideal.span {π ^ 4}) (D I) := by
    rw [AlgHom.map_det, RingHom.map_det]
    congr 1
    ext j i
    exact hconst _
  have hd (I : {I : Finset (Fin n) // I.card = c}) :
      ∃ d : R, Ideal.Quotient.mk (Ideal.span {π ^ 4}) d = q (b I) :=
    Ideal.Quotient.mk_surjective (q (b I))
  choose d hd using hd
  have hmod : Ideal.Quotient.mk (Ideal.span {π ^ 4}) π =
      Ideal.Quotient.mk (Ideal.span {π ^ 4}) (∑ I, d I * D I) := by
    have h := congrArg q hminor
    simpa only [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, map_sum, map_mul,
      hD, hd] using h
  have ht : ∃ t : R, π - ∑ I, d I * D I = π ^ 4 * t := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hmod, sub_self]
  obtain ⟨t, ht⟩ := ht
  refine ⟨a, t, ha, ?_⟩
  have heq : (1 - π ^ 3 * t) * π = ∑ I, d I * D I := by
    calc
      (1 - π ^ 3 * t) * π = π - π ^ 4 * t := by ring
      _ = ∑ I, d I * D I := by rw [← ht]; ring
  rw [heq]
  apply Ideal.sum_mem
  intro I _
  apply Ideal.mul_mem_left
  apply Ideal.subset_span
  refine ⟨I, ?_⟩
  exact Matrix.det_transpose _

end Algebra
