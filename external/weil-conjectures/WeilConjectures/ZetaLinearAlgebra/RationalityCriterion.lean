/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.List.TFAE
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
public import WeilConjectures.ZetaLinearAlgebra.ShiftSpan

/-!
# The rationality criterion for power series

Let `K` be a field and `f = ∑ cₙ Tⁿ ∈ K⟦X⟧`. This file proves that the following are equivalent:

1. `f = A / B` for polynomials `A B : K[X]` with `B(0) = 1`;
2. the Hankel matrix `(c_{r+s})_{r,s ≥ 0}` of `f` has finite rank, i.e. the ranks of its finite
   square submatrices are bounded;
3. the coefficients of `f` eventually satisfy a linear recurrence
   `c_{n+d} + a_{d-1} c_{n+d-1} + ⋯ + a₀ cₙ = 0`.

The rows of the Hankel matrix are the iterated shifts of the coefficient sequence, so their span
is `shiftSpan`, and `PowerSeries.exists_normalized_fraction_iff_finiteDimensional_shiftSpan`
already identifies (1) with finite-dimensionality of that span.

## Main definitions

- `PowerSeries.hankel`: the Hankel matrix of a power series.

## Main statements

- `PowerSeries.span_range_row_hankel`: the rows of the Hankel matrix span the shift span.
- `finiteDimensional_shiftSpan_of_forall_add_eq_zero`: a sequence eventually satisfying a monic
  linear recurrence has finite-dimensional shift span.
- `PowerSeries.tfae_exists_normalized_fraction`: the rationality criterion.
-/

@[expose] public section

open Finset

open scoped Polynomial PowerSeries

variable {K : Type*} [Field K]

/-- A sequence satisfying the linear recurrence
`a (n + d) + c (d - 1) * a (n + d - 1) + ⋯ + c 0 * a n = 0` for all `n ≥ m` has
finite-dimensional shift span: every shift lies in the span of the first `m + d` shifts. -/
theorem finiteDimensional_shiftSpan_of_forall_add_eq_zero {a : ℕ → K} {m d : ℕ}
    (c : Fin d → K) (h : ∀ n, m ≤ n → a (n + d) + ∑ i, c i * a (n + i) = 0) :
    FiniteDimensional K (shiftSpan K a) := by
  set g : ℕ → (ℕ → K) := fun k => (⇑(seqShift K))^[k] a with hg
  set W : Submodule K (ℕ → K) := Submodule.span K (g '' Set.Iio (m + d)) with hW
  have hWfd : FiniteDimensional K W :=
    FiniteDimensional.span_of_finite K ((Set.finite_Iio _).image g)
  have key : ∀ k, g k ∈ W := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases lt_or_ge k (m + d) with hk | hk
      · exact Submodule.subset_span ⟨k, hk, rfl⟩
      · have hgk : g k = -∑ i, c i • g (k - d + i) := by
          funext s
          have hs := h (s + (k - d)) (by omega)
          have hsk : s + (k - d) + d = s + k := by omega
          rw [hsk] at hs
          simp only [hg, iterate_seqShift_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, ← add_assoc]
          exact eq_neg_of_add_eq_zero_left hs
        rw [hgk]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (ih _ (by omega)))
  have hle : shiftSpan K a ≤ W := shiftSpan_le key
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

namespace PowerSeries

/-- The **Hankel matrix** `(c_{r+s})_{r,s ≥ 0}` of a power series `∑ cₙ Tⁿ`
(blueprints `lemma-hankel-rank-rationality--1`, `definition-reciprocal-root`). -/
noncomputable def hankel {R : Type*} [Semiring R] (f : R⟦X⟧) : Matrix ℕ ℕ R :=
  Matrix.of fun r s => coeff (r + s) f

@[simp]
lemma hankel_apply {R : Type*} [Semiring R] (f : R⟦X⟧) (r s : ℕ) :
    hankel f r s = coeff (r + s) f := rfl

/-- The rows of the Hankel matrix of `f` are the iterated shifts of the coefficient sequence
of `f`, so they span its shift span. -/
lemma span_range_row_hankel (f : K⟦X⟧) :
    Submodule.span K (Set.range (hankel f).row) = shiftSpan K fun n => coeff n f := by
  rw [shiftSpan]
  congr 2
  funext r s
  simp [Matrix.row, iterate_seqShift_apply, add_comm]

/-- A sequence with finite-dimensional shift span satisfies a monic linear recurrence
`a (n + d) + c (d - 1) * a (n + d - 1) + ⋯ + c 0 * a n = 0` of order `d ≥ 1` in all degrees. -/
theorem exists_forall_add_eq_zero_of_finiteDimensional_shiftSpan (a : ℕ → K)
    [FiniteDimensional K (shiftSpan K a)] :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ c : Fin d → K, ∀ n, a (n + d) + ∑ i, c i * a (n + i) = 0 := by
  obtain ⟨p, hpm, key⟩ := exists_monic_sum_coeff_mul_eq_zero_of_finiteDimensional_shiftSpan a
  rcases Nat.eq_zero_or_pos p.natDegree with hd | hd
  · refine ⟨1, le_rfl, 0, fun n => ?_⟩
    have hp1 : p.coeff 0 = 1 := hd ▸ hpm.coeff_natDegree
    have := key (n + 1)
    simp only [hd, zero_add, Finset.sum_range_one, hp1, one_mul, add_zero] at this
    simp [this]
  · refine ⟨p.natDegree, hd, fun i => p.coeff i, fun n => ?_⟩
    have := key n
    rw [Finset.sum_range_succ, hpm.coeff_natDegree, one_mul] at this
    rw [Fin.sum_univ_eq_sum_range (fun i => p.coeff i * a (n + i)), add_comm]
    exact this

/-- **Rationality criterion** (blueprint `lemma-hankel-rank-rationality`,
`lemma-hankel-rank-rationality--1`): for a power series `f = ∑ cₙ Tⁿ` over a field `K` the following
are equivalent:
1. `f = A / B` for polynomials `A`, `B` with `B(0) = 1`;
2. the Hankel matrix of `f` has finite rank: the ranks of its finite square submatrices are
   bounded;
3. there are `m ≥ 0`, `d ≥ 1` and `a₀, …, a_{d-1} ∈ K` with
   `c_{n+d} + a_{d-1} c_{n+d-1} + ⋯ + a₀ cₙ = 0` for all `n ≥ m`. -/
theorem tfae_exists_normalized_fraction (f : K⟦X⟧) :
    List.TFAE
      [∃ A B : K[X], B.coeff 0 = 1 ∧ f * (B : K⟦X⟧) = (A : K⟦X⟧),
        BddAbove (Set.range fun x : Σ r : ℕ, (Fin r → ℕ) × (Fin r → ℕ) =>
          ((hankel f).submatrix x.2.1 x.2.2).rank),
        ∃ m d : ℕ, 1 ≤ d ∧ ∃ a : Fin d → K,
          ∀ n, m ≤ n → coeff (n + d) f + ∑ i, a i * coeff (n + i) f = 0] := by
  tfae_have 1 ↔ 2 := by
    rw [exists_normalized_fraction_iff_finiteDimensional_shiftSpan,
      Matrix.bddAbove_range_rank_submatrix_iff, span_range_row_hankel]
  tfae_have 1 → 3 := by
    rw [exists_normalized_fraction_iff_finiteDimensional_shiftSpan]
    intro _
    obtain ⟨d, hd, a, ha⟩ :=
      exists_forall_add_eq_zero_of_finiteDimensional_shiftSpan fun n => coeff n f
    exact ⟨0, d, hd, a, fun n _ => ha n⟩
  tfae_have 3 → 1 := by
    rintro ⟨m, d, -, a, ha⟩
    rw [exists_normalized_fraction_iff_finiteDimensional_shiftSpan]
    exact finiteDimensional_shiftSpan_of_forall_add_eq_zero a ha
  tfae_finish

end PowerSeries
