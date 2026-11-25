/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Automorphisms of matrix algebras are inner

The **Skolem–Noether theorem** for matrix algebras over a field: every `F`-algebra automorphism
of `Matrix n n F` is conjugation by an invertible matrix. In particular it preserves the
determinant.

## Main statements

- `Matrix.exists_unit_conj_of_algEquiv`: an automorphism of `Matrix n n F` is inner.
- `Matrix.det_algEquiv_apply`: an automorphism of `Matrix n n F` preserves the determinant.
-/

@[expose] public section

namespace Matrix

variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

/-- For an automorphism `σ` of `Matrix n n F` and any matrix `Y`, the matrix
`∑ j, σ (single j i₀ 1) * Y * single i₀ j 1` intertwines the identity and `σ`. -/
theorem algEquiv_mul_sum_eq (σ : Matrix n n F ≃ₐ[F] Matrix n n F) (Y : Matrix n n F) (i₀ : n)
    (X : Matrix n n F) :
    σ X * ∑ j, σ (single j i₀ 1) * Y * single i₀ j 1 =
      (∑ j, σ (single j i₀ 1) * Y * single i₀ j 1) * X := by
  induction X using Matrix.induction_on' with
  | h_zero => simp
  | h_add p q hp hq => rw [map_add, add_mul, mul_add, hp, hq]
  | h_std_basis a b x =>
    have hx : single a b x = x • single a b 1 := by rw [smul_single, smul_eq_mul, mul_one]
    rw [hx, map_smul, smul_mul_assoc, mul_smul_comm,
      Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single b, Finset.sum_eq_single a]
    · rw [mul_assoc _ (single i₀ a 1), single_mul_single_same, ← mul_assoc, ← mul_assoc,
        ← map_mul, single_mul_single_same, mul_one]
    · intro j _ hj
      rw [mul_assoc _ (single i₀ j 1), single_mul_single_of_ne (h := hj), mul_zero]
    · simp
    · intro j _ hj
      rw [← mul_assoc, ← mul_assoc, ← map_mul, single_mul_single_of_ne (h := Ne.symm hj),
        map_zero, zero_mul, zero_mul]
    · simp

omit [DecidableEq n] in
/-- If `g * X *ᵥ v = 0` for all matrices `X` and some nonzero vector `v`, then `g = 0`. -/
theorem eq_zero_of_mul_mulVec_eq_zero {g : Matrix n n F} {v : n → F} (hv : v ≠ 0)
    (h : ∀ X : Matrix n n F, g *ᵥ (X *ᵥ v) = 0) : g = 0 := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  ext t s
  have := congrFun (h (single s k 1)) t
  simp only [mulVec, dotProduct, single_apply, Pi.zero_apply] at this
  simp only [Pi.zero_apply] at hk
  simp [ite_and] at this
  exact this.resolve_right hk

/-- **Skolem–Noether for matrix algebras.** Every `F`-algebra automorphism of `Matrix n n F`
is conjugation by a unit: with `v` a nonzero vector in the image of `σ (single i₀ i₀ 1)`, the
matrix with columns `σ (single j i₀ 1) v` intertwines the identity and `σ`. -/
@[stacks 074P]
theorem exists_unit_conj_of_algEquiv (σ : Matrix n n F ≃ₐ[F] Matrix n n F) :
    ∃ g : (Matrix n n F)ˣ, ∀ X, σ X = g * X * g⁻¹ := by
  cases isEmpty_or_nonempty n with
  | inl _ => exact ⟨1, fun X => Subsingleton.elim _ _⟩
  | inr h =>
  obtain ⟨i₀⟩ := h
  obtain ⟨r', r, hr⟩ : ∃ r' r, σ (single i₀ i₀ 1) r' r ≠ 0 := by
    by_contra! h
    have h1 : single i₀ i₀ (1 : F) = 0 := σ.injective (by rw [map_zero]; exact Matrix.ext h)
    simpa using congrFun (congrFun h1 i₀) i₀
  have key := algEquiv_mul_sum_eq σ (single r i₀ 1) i₀
  set g := ∑ j, σ (single j i₀ 1) * single r i₀ 1 * single i₀ j 1
  have hg : g ≠ 0 := by
    intro hg
    have h1 : g r' i₀ = σ (single i₀ i₀ 1) r' r := by
      simp only [g]
      rw [Matrix.sum_apply, Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        exact mul_single_apply_of_ne (hbj := Ne.symm hj) ..
      · simp
    rw [hg] at h1
    exact hr (by simpa using h1.symm)
  have hdet : IsUnit g := by
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hgv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    refine hg (eq_zero_of_mul_mulVec_eq_zero hv fun X => ?_)
    rw [mulVec_mulVec, ← key, ← mulVec_mulVec, hgv, mulVec_zero]
  obtain ⟨u, hu⟩ := hdet
  refine ⟨u, fun X => ?_⟩
  rw [← hu] at key
  rw [← key, Units.mul_inv_cancel_right]


/-- An `F`-algebra automorphism of `Matrix n n F` preserves the determinant. -/
theorem det_algEquiv_apply (σ : Matrix n n F ≃ₐ[F] Matrix n n F) (X : Matrix n n F) :
    (σ X).det = X.det := by
  obtain ⟨g, hg⟩ := exists_unit_conj_of_algEquiv σ
  rw [hg, det_mul, det_mul, mul_right_comm, ← det_mul, Units.mul_inv, det_one, one_mul]


end Matrix
