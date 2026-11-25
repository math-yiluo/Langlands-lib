/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.Logarithm

/-!
# The logarithm and the exponential on deep principal units

Let `E / ℚ_ℓ` be a finite extension inside `ℚ̄_ℓ = PadicAlgCl l`, with the norm restricted from
`ℚ̄_ℓ`, and let `K = ℓ ^ (1 / (ℓ - 1))` (`PadicAlgCl.logExpConst`). On the ball
`K ‖x‖ < 1`, i.e. `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`, the logarithm series
`log (1 + x) = ∑ (-1)^(n+1) x ^ n / n` (`PadicAlgCl.smallLog`) and the exponential series
`exp x = ∑ x ^ n / n!` (`PadicAlgCl.smallExp`) converge, are isometries, and are mutually
inverse group isomorphisms between the principal units `1 + x` and the additive group of the
ball (blueprint `theorem-rank-one-sheaves-have-finite--1`). For a uniformizer `ϖ` and
`r > e / (ℓ - 1)` the ideal `𝔪_E ^ r` is a closed sub-ball of this ball.

The inverse identities are proved without composing power series: `f x = log (exp x)` is
additive with `‖f x - x‖ ≤ K ‖x‖ ^ 2`, and evaluating at `ℓⁿ x` forces `f x = x`.

## Main statements

- `PadicAlgCl.smallLog_add_add_mul`, `PadicAlgCl.smallExp_add`: the homomorphism properties.
- `PadicAlgCl.smallLog_smallExp_sub_one`, `PadicAlgCl.smallExp_smallLog`: the inverse identities.
- `PadicAlgCl.norm_smallLog_sub_smallLog`, `PadicAlgCl.norm_smallExp_sub_smallExp`: isometry.
- `PadicAlgCl.smallLog_smallExp_deep`: summary on a closed ball of radius `ρ < ℓ ^ (-1 / (ℓ - 1))`.
- `PadicAlgCl.exists_pow_norm_sub_one_le`: some power `u ^ N` of every unit of `𝒪_E` is a deep
  principal unit.
-/

@[expose] public section

universe w

open Filter Topology
open scoped Nat NNReal

namespace PadicAlgCl

section Constant

variable (l : ℕ) [Fact l.Prime]

/-- The constant `ℓ ^ (1 / (ℓ - 1))`. The logarithm and the exponential series converge on the
open ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`, of radius the inverse of this constant, since
`v_ℓ(n!) ≤ (n - 1) / (ℓ - 1)`. -/
noncomputable def logExpConst : ℝ := (l : ℝ) ^ (((l - 1 : ℕ) : ℝ)⁻¹)

variable {l}

theorem logExpConst_pos : 0 < logExpConst l :=
  Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _

theorem logExpConst_pow : logExpConst l ^ (l - 1) = l :=
  Real.rpow_inv_natCast_pow (Nat.cast_nonneg l)
    (by have := (Fact.out : l.Prime).two_le; omega)

theorem one_le_logExpConst : 1 ≤ logExpConst l :=
  Real.one_le_rpow (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) (by positivity)

/-- Legendre's bound `(ℓ - 1) v_ℓ((n + 1)!) ≤ n`, in the form `ℓ ^ v_ℓ((n + 1)!) ≤ K ^ n` for
`K = ℓ ^ (1 / (ℓ - 1))`. -/
theorem pow_padicValNat_factorial_le (n : ℕ) :
    (l : ℝ) ^ padicValNat l (n + 1)! ≤ logExpConst l ^ n := by
  have hl1 : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  have hK : (logExpConst l ^ n) ^ (l - 1) = (l : ℝ) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul, logExpConst_pow]
  rw [← pow_le_pow_iff_left₀ (by positivity) (pow_nonneg logExpConst_pos.le n) hl1, hK,
    ← pow_mul]
  refine pow_le_pow_right₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) ?_
  have := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l (n := n + 1) (by omega)
  rw [mul_comm] at this
  omega

/-- `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` if and only if `‖x‖ ^ (ℓ - 1) < ‖ℓ‖ = ℓ⁻¹`. -/
theorem mul_logExpConst_lt_one_iff {a : ℝ} (ha : 0 ≤ a) :
    a * logExpConst l < 1 ↔ a ^ (l - 1) < (l : ℝ)⁻¹ := by
  have hl1 : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [← pow_lt_one_iff_of_nonneg (mul_nonneg ha logExpConst_pos.le) hl1, mul_pow,
    logExpConst_pow, ← lt_div_iff₀ hl, one_div]

end Constant

section Estimates

variable {l : ℕ} [Fact l.Prime] {E : Type w} [Field E] [Algebra E (PadicAlgCl l)]

/-- The `(n + 1)`-st term of the exponential series has norm at most `‖x‖ (K ‖x‖) ^ n`, for
`K = ℓ ^ (1 / (ℓ - 1))`. -/
theorem norm_expSeries_term_le (x : E) (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    ‖x ^ (n + 1) / ((n + 1)! : E)‖ ≤ ‖x‖ * (logExpConst l * ‖x‖) ^ n := by
  let := normedFieldOfAlgebra l E
  rw [norm_div, norm_pow, norm_natCast_eq_pow_padicValNat (Nat.factorial_ne_zero _), inv_pow,
    div_inv_eq_mul, pow_succ', mul_pow, mul_assoc, mul_comm (logExpConst l ^ n)]
  gcongr
  exact pow_padicValNat_factorial_le n

/-- The `(n + 1)`-st term `(-1)^n x ^ (n + 1) / (n + 1)` of the logarithm series has norm at
most `‖x‖ (K ‖x‖) ^ n`, for `K = ℓ ^ (1 / (ℓ - 1))`, since `‖(n + 1)!‖ ≤ ‖n + 1‖`. -/
theorem norm_logSeries_term_le' (x : E) (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    ‖(-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ)‖ ≤ ‖x‖ * (logExpConst l * ‖x‖) ^ n := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have : NormOneClass E := ⟨by change ‖algebraMap E (PadicAlgCl l) 1‖ = 1; simp⟩
  have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
  refine le_trans ?_ (norm_expSeries_term_le x n)
  rw [norm_div, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hpos : 0 < ‖((n + 1)! : E)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  refine div_le_div_of_nonneg_left (by positivity) hpos ?_
  rw [Nat.factorial_succ, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one E _)

/-- For `K ‖x‖ ≤ 1` the difference quotient `((1 + x) ^ q - 1) / q` agrees with the `q`-th
partial sum of the logarithm series up to an error of norm at most `‖q‖ ‖x‖`: the coefficient of
`x ^ (j + 1)` in their difference is `(C(q - 1, j) - (-1)^j) / (j + 1)`, and
`j! (C(q - 1, j) - (-1)^j)` is divisible by `q`. -/
theorem norm_pow_sub_one_div_sub_sum_le' {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ ≤ 1) (q : ℕ) :
    letI := normedFieldOfAlgebra l E
    ‖((1 + x) ^ q - 1) / q - ∑ j ∈ Finset.range q, (-1) ^ j * x ^ (j + 1) / (j + 1 : ℕ)‖ ≤
      ‖(q : E)‖ * ‖x‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
  obtain _ | p := q
  · simp
  have hq : ((p + 1 : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr p.succ_ne_zero
  have hsum : ((1 + x) ^ (p + 1) - 1) / (p + 1 : ℕ) =
      ∑ j ∈ Finset.range (p + 1), (p.choose j : E) * x ^ (j + 1) / (j + 1 : ℕ) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one,
      add_sub_cancel_right]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h := congrArg (fun m : ℕ ↦ (m : E)) (Nat.add_one_mul_choose_eq p j)
    have hj : ((j + 1 : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr j.succ_ne_zero
    push_cast at h hq hj ⊢
    rw [div_eq_div_iff hq hj]
    linear_combination -x ^ (j + 1) * h
  rw [hsum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j hj ↦ ?_
  obtain ⟨w, hw⟩ := Nat.add_one_dvd_factorial_mul_choose_sub_neg_one_pow
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hw' : (j ! : E) * ((p.choose j : E) - (-1) ^ j) = ((p + 1 : ℕ) : E) * (w : E) := by
    exact_mod_cast hw
  have hfac : ((j + 1)! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hterm : ((p.choose j : E) * x ^ (j + 1) / (j + 1 : ℕ) -
      (-1) ^ j * x ^ (j + 1) / (j + 1 : ℕ)) =
      ((p + 1 : ℕ) : E) * (w : E) * (x ^ (j + 1) / ((j + 1)! : E)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, ← hw']
    have hj : (j ! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  rw [hterm, norm_mul, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖(w : E)‖ * ‖x ^ (j + 1) / ((j + 1)! : E)‖
      ≤ 1 * (‖x‖ * (logExpConst l * ‖x‖) ^ j) := by
        gcongr
        · exact IsUltrametricDist.norm_intCast_le_one E w
        · exact norm_expSeries_term_le x j
    _ ≤ ‖x‖ := by
        rw [one_mul]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (mul_nonneg logExpConst_pos.le (norm_nonneg _)) hx)

end Estimates

section Series

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

`smallExp l E x` is the sum of the exponential series `exp x = ∑_{n ≥ 0} x ^ n / n!`, formed in
the topology restricted from `ℚ̄_ℓ`. It converges for `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`
(`PadicAlgCl.summable_expSeries`). -/
noncomputable def smallExp (x : E) : E :=
  letI := normedFieldOfAlgebra l E
  ∑' n : ℕ, x ^ n / (n ! : E)

variable {l E}

theorem smallLog_zero : smallLog l E 0 = 0 := by
  simp [smallLog]

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- The logarithm series converges on the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`. -/
theorem summable_logSeries' {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    Summable fun n : ℕ ↦ (-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ) := by
  let := normedFieldOfAlgebra l E
  have := completeSpace_ofAlgebra l E
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one
    (mul_nonneg logExpConst_pos.le (norm_nonneg _)) hx).mul_left ‖x‖)
    (norm_logSeries_term_le' x)

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- The norms of the terms of the exponential series are summable on the ball
`‖x‖ < ℓ ^ (-1 / (ℓ - 1))`. -/
theorem summable_norm_expSeries {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    Summable fun n : ℕ ↦ ‖x ^ n / (n ! : E)‖ := by
  let := normedFieldOfAlgebra l E
  refine (summable_nat_add_iff 1).mp ?_
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_expSeries_term_le x)
    ((summable_geometric_of_lt_one (mul_nonneg logExpConst_pos.le (norm_nonneg _)) hx).mul_left
      ‖x‖)

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

The exponential series converges on the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`: its `n`-th term has
norm `‖x‖ ^ n ℓ ^ v_ℓ(n!)` and `v_ℓ(n!) ≤ (n - 1) / (ℓ - 1)`. -/
theorem summable_expSeries {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    Summable fun n : ℕ ↦ x ^ n / (n ! : E) := by
  let := normedFieldOfAlgebra l E
  have := completeSpace_ofAlgebra l E
  exact (summable_norm_expSeries hx).of_norm

/-- On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` one has `‖log (1 + x) - x‖ ≤ K ‖x‖ ^ 2`, for
`K = ℓ ^ (1 / (ℓ - 1))`. -/
theorem norm_smallLog_sub_le {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallLog l E x - x‖ ≤ logExpConst l * ‖x‖ ^ 2 := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have hsplit := (summable_logSeries' hx).tsum_eq_zero_add
  change smallLog l E x = _ at hsplit
  simp only [pow_zero, zero_add, pow_one, one_mul, Nat.cast_one, div_one] at hsplit
  rw [hsplit, add_sub_cancel_left]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg logExpConst_pos.le (sq_nonneg _)) fun n ↦
    (norm_logSeries_term_le' x (n + 1)).trans ?_
  calc ‖x‖ * (logExpConst l * ‖x‖) ^ (n + 1) ≤ ‖x‖ * (logExpConst l * ‖x‖) :=
        mul_le_mul_of_nonneg_left (pow_le_of_le_one (mul_nonneg logExpConst_pos.le
          (norm_nonneg _)) hx.le n.succ_ne_zero) (norm_nonneg x)
    _ = logExpConst l * ‖x‖ ^ 2 := by ring

/-- On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` one has `‖exp x - 1 - x‖ ≤ K ‖x‖ ^ 2`, for
`K = ℓ ^ (1 / (ℓ - 1))`. -/
theorem norm_smallExp_sub_le {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallExp l E x - 1 - x‖ ≤ logExpConst l * ‖x‖ ^ 2 := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have := completeSpace_ofAlgebra l E
  have hs := summable_expSeries hx
  have hsplit := hs.tsum_eq_zero_add
  rw [((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add] at hsplit
  change smallExp l E x = _ at hsplit
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one] at hsplit
  rw [hsplit, add_sub_cancel_left, add_sub_cancel_left]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg logExpConst_pos.le (sq_nonneg _)) fun n ↦
    (norm_expSeries_term_le x (n + 1)).trans ?_
  calc ‖x‖ * (logExpConst l * ‖x‖) ^ (n + 1) ≤ ‖x‖ * (logExpConst l * ‖x‖) :=
        mul_le_mul_of_nonneg_left (pow_le_of_le_one (mul_nonneg logExpConst_pos.le
          (norm_nonneg _)) hx.le n.succ_ne_zero) (norm_nonneg x)
    _ = logExpConst l * ‖x‖ ^ 2 := by ring

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- An element `x + t` with `‖t‖ ≤ K ‖x‖ ^ 2` and `K ‖x‖ < 1` has the norm of `x`. -/
theorem norm_eq_of_norm_sub_le {x y : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1)
    (hy : letI := normedFieldOfAlgebra l E; ‖y - x‖ ≤ logExpConst l * ‖x‖ ^ 2) :
    letI := normedFieldOfAlgebra l E
    ‖y‖ = ‖x‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using hy
  have hlt : ‖y - x‖ < ‖x‖ := by
    refine hy.trans_lt ?_
    rw [sq, ← mul_assoc]
    exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hx0) hx
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne'
  rwa [add_sub_cancel, max_eq_left hlt.le] at h

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` the logarithm preserves the norm:
`‖log (1 + x)‖ = ‖x‖`. -/
theorem norm_smallLog_eq {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallLog l E x‖ = ‖x‖ :=
  norm_eq_of_norm_sub_le hx (norm_smallLog_sub_le hx)

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` the exponential satisfies `‖exp x - 1‖ = ‖x‖`. -/
theorem norm_smallExp_sub_one_eq {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallExp l E x - 1‖ = ‖x‖ :=
  norm_eq_of_norm_sub_le hx (norm_smallExp_sub_le hx)

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

The exponential turns addition into multiplication on the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`:
`exp (x + y) = exp x exp y`, by the Cauchy product formula, the norms of the terms of both
series being summable. -/
theorem smallExp_add {x y : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1)
    (hy : letI := normedFieldOfAlgebra l E; logExpConst l * ‖y‖ < 1) :
    smallExp l E (x + y) = smallExp l E x * smallExp l E y := by
  let := normedFieldOfAlgebra l E
  have := completeSpace_ofAlgebra l E
  have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
  change ∑' n : ℕ, (x + y) ^ n / (n ! : E) =
    (∑' n : ℕ, x ^ n / (n ! : E)) * ∑' n : ℕ, y ^ n / (n ! : E)
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (R := E) (summable_norm_expSeries hx)
    (summable_norm_expSeries hy)]
  refine tsum_congr fun n ↦ ?_
  rw [(Commute.all x y).add_pow', Finset.sum_div]
  refine Finset.sum_congr rfl fun kl hkl ↦ ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [nsmul_eq_mul, ← hkl, Nat.cast_add_choose E]
  have h1 : (kl.1 ! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (kl.2 ! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((kl.1 + kl.2)! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

end Series
section Inverse

variable {l : ℕ} [Fact l.Prime] {E : Type w} [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
theorem smallExp_zero : smallExp l E 0 = 1 := by
  let := normedFieldOfAlgebra l E
  rw [smallExp, tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn]]
  simp

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- An element of the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` has norm `< 1`. -/
theorem norm_lt_one_of_mul_logExpConst_lt_one {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖x‖ < 1 := by
  let := normedFieldOfAlgebra l E
  exact lt_of_le_of_lt (le_mul_of_one_le_left (norm_nonneg _) one_le_logExpConst) hx

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- The ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` is closed under the operation `(x, y) ↦ x + y + x y`
corresponding to the multiplication of principal units, and under any operation not increasing
`max ‖x‖ ‖y‖`. -/
theorem mul_logExpConst_lt_one_of_le_max {x y z : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1)
    (hy : letI := normedFieldOfAlgebra l E; logExpConst l * ‖y‖ < 1)
    (hz : letI := normedFieldOfAlgebra l E; ‖z‖ ≤ max ‖x‖ ‖y‖) :
    letI := normedFieldOfAlgebra l E
    logExpConst l * ‖z‖ < 1 := by
  let := normedFieldOfAlgebra l E
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz logExpConst_pos.le) ?_
  rcases max_choice ‖x‖ ‖y‖ with h | h <;> rw [h] <;> assumption

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
theorem norm_add_add_mul_le_max {x y : E}
    (hy : letI := normedFieldOfAlgebra l E; ‖y‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖x + y + x * y‖ ≤ max ‖x‖ ‖y‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have h1 : ‖x * y‖ ≤ ‖x‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy.le
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (IsUltrametricDist.norm_add_le_max _ _) (h1.trans (le_max_left _ _)))

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- A principal unit `1 + x` with `‖x‖ < 1` has norm one. -/
theorem norm_one_add_eq_one {x : E} (hx : letI := normedFieldOfAlgebra l E; ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖1 + x‖ = 1 := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have : NormOneClass E := ⟨by change ‖algebraMap E (PadicAlgCl l) 1‖ = 1; simp⟩
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hx.ne'),
    norm_one, max_eq_left hx.le]

/-- On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` the logarithm is the limit of the difference quotients
`((1 + x) ^ ℓⁿ - 1) / ℓⁿ`. -/
theorem tendsto_pow_sub_one_div_smallLog' {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    Tendsto (fun n : ℕ ↦ ((1 + x) ^ (l ^ n) - 1) / (l ^ n : ℕ)) atTop (𝓝 (smallLog l E x)) := by
  let := normedFieldOfAlgebra l E
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := inv_nonneg.mpr (zero_le_one.trans hl.le)
  have hr1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hS := ((summable_logSeries' hx).hasSum.tendsto_sum_nat).comp
    (tendsto_pow_atTop_atTop_of_one_lt (Fact.out : l.Prime).one_lt)
  have hdiff : Tendsto (fun n : ℕ ↦ ((1 + x) ^ (l ^ n) - 1) / (l ^ n : ℕ) -
      ∑ j ∈ Finset.range (l ^ n), (-1) ^ j * x ^ (j + 1) / (j + 1 : ℕ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ ↦ (l : ℝ)⁻¹ ^ n * ‖x‖) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const ‖x‖
    refine squeeze_zero_norm (fun n ↦ (norm_pow_sub_one_div_sub_sum_le' hx.le _).trans_eq ?_) h0
    rw [norm_natCast_eq_pow_padicValNat (pow_ne_zero _ (Fact.out : l.Prime).ne_zero),
      padicValNat.prime_pow]
  have h := hdiff.add hS
  simp only [Function.comp_apply, sub_add_cancel, zero_add] at h
  exact h

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

The logarithm is a homomorphism on the principal units `1 + x` with `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`:
`log ((1 + x) (1 + y)) = log (1 + x) + log (1 + y)`, where `(1 + x) (1 + y) = 1 + (x + y + x y)`. -/
theorem smallLog_add_add_mul {x y : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1)
    (hy : letI := normedFieldOfAlgebra l E; logExpConst l * ‖y‖ < 1) :
    smallLog l E (x + y + x * y) = smallLog l E x + smallLog l E y := by
  let := normedFieldOfAlgebra l E
  have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
  have hxy : logExpConst l * ‖x + y + x * y‖ < 1 :=
    mul_logExpConst_lt_one_of_le_max hx hy
      (norm_add_add_mul_le_max (norm_lt_one_of_mul_logExpConst_lt_one hy))
  have hu := tendsto_pow_sub_one_div_smallLog' hx
  have hv := tendsto_pow_sub_one_div_smallLog' hy
  have huv := tendsto_pow_sub_one_div_smallLog' hxy
  have hq : Tendsto (fun n : ℕ ↦ ((l ^ n : ℕ) : E)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (zero_le_one.trans hl.le))
      (inv_lt_one_of_one_lt₀ hl)).congr fun n ↦ ?_
    rw [norm_natCast_eq_pow_padicValNat (pow_ne_zero _ (Fact.out : l.Prime).ne_zero),
      padicValNat.prime_pow]
  have key (n : ℕ) : ((l ^ n : ℕ) : E) * (((1 + x) ^ (l ^ n) - 1) / (l ^ n : ℕ)) *
      (((1 + y) ^ (l ^ n) - 1) / (l ^ n : ℕ)) + ((1 + x) ^ (l ^ n) - 1) / (l ^ n : ℕ) +
      ((1 + y) ^ (l ^ n) - 1) / (l ^ n : ℕ) =
        ((1 + (x + y + x * y)) ^ (l ^ n) - 1) / (l ^ n : ℕ) := by
    have hq0 : ((l ^ n : ℕ) : E) ≠ 0 :=
      Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    have h1 : 1 + (x + y + x * y) = (1 + x) * (1 + y) := by ring
    rw [h1, mul_pow]
    field_simp
    ring
  have hlim := (((hq.mul hu).mul hv).add hu).add hv
  rw [zero_mul, zero_mul, zero_add] at hlim
  exact tendsto_nhds_unique huv (hlim.congr key)

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

The logarithm is an isometry on the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`:
`‖log (1 + x) - log (1 + y)‖ = ‖x - y‖`; in particular it is continuous and injective there. -/
theorem norm_smallLog_sub_smallLog {x y : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1)
    (hy : letI := normedFieldOfAlgebra l E; logExpConst l * ‖y‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallLog l E x - smallLog l E y‖ = ‖x - y‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have hy1 : ‖1 + y‖ = 1 := norm_one_add_eq_one (norm_lt_one_of_mul_logExpConst_lt_one hy)
  have hy0 : 1 + y ≠ 0 := norm_ne_zero_iff.mp (by rw [hy1]; exact one_ne_zero)
  set c := (x - y) / (1 + y) with hc
  have hcn : ‖c‖ = ‖x - y‖ := by rw [hc, norm_div, hy1, div_one]
  have hcb : logExpConst l * ‖c‖ < 1 := by
    rw [hcn]
    refine mul_logExpConst_lt_one_of_le_max hx hy ?_
    rw [sub_eq_add_neg, ← norm_neg y]
    exact IsUltrametricDist.norm_add_le_max _ _
  have hxc : x = y + c + y * c := by
    rw [hc]
    field_simp
    ring
  rw [hxc, smallLog_add_add_mul hy hcb, add_sub_cancel_left, norm_smallLog_eq hcb,
    ← hxc, hcn]

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

The exponential is an isometry on the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`:
`‖exp x - exp y‖ = ‖x - y‖`; in particular it is continuous and injective there. -/
theorem norm_smallExp_sub_smallExp {x y : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1)
    (hy : letI := normedFieldOfAlgebra l E; logExpConst l * ‖y‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallExp l E x - smallExp l E y‖ = ‖x - y‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have hxy : logExpConst l * ‖x - y‖ < 1 := by
    refine mul_logExpConst_lt_one_of_le_max hx hy ?_
    rw [sub_eq_add_neg, ← norm_neg y]
    exact IsUltrametricDist.norm_add_le_max _ _
  have hy1 : ‖smallExp l E y‖ = 1 := by
    have h := norm_one_add_eq_one (l := l) (E := E) (x := smallExp l E y - 1) (by
      rw [norm_smallExp_sub_one_eq hy]
      exact norm_lt_one_of_mul_logExpConst_lt_one hy)
    rwa [add_sub_cancel] at h
  have hsplit : smallExp l E x = smallExp l E y * smallExp l E (x - y) := by
    rw [← smallExp_add hy hxy, add_sub_cancel]
  rw [hsplit, ← mul_sub_one, norm_mul, hy1, one_mul, norm_smallExp_sub_one_eq hxy]

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` the logarithm inverts the exponential:
`log (exp x) = x`. The map `f x = log (exp x)` is additive, and `‖f x - x‖ ≤ K ‖x‖ ^ 2`; applying
this to `ℓⁿ x` gives `‖f x - x‖ ≤ K ℓ⁻ⁿ ‖x‖ ^ 2` for every `n`. -/
theorem smallLog_smallExp_sub_one {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    smallLog l E (smallExp l E x - 1) = x := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  set K := logExpConst l with hK
  let f : E → E := fun x ↦ smallLog l E (smallExp l E x - 1)
  have hball (x : E) (hx : K * ‖x‖ < 1) : K * ‖smallExp l E x - 1‖ < 1 := by
    rwa [norm_smallExp_sub_one_eq hx]
  have hadd (x y : E) (hx : K * ‖x‖ < 1) (hy : K * ‖y‖ < 1) : f (x + y) = f x + f y := by
    have hxy : K * ‖x + y‖ < 1 :=
      mul_logExpConst_lt_one_of_le_max hx hy (IsUltrametricDist.norm_add_le_max _ _)
    have h : smallExp l E (x + y) - 1 = (smallExp l E x - 1) + (smallExp l E y - 1) +
        (smallExp l E x - 1) * (smallExp l E y - 1) := by
      rw [smallExp_add hx hy]
      ring
    change smallLog l E _ = smallLog l E _ + smallLog l E _
    rw [h, smallLog_add_add_mul (hball x hx) (hball y hy)]
  have hnat (n : ℕ) : K * ‖(n : E) * x‖ < 1 := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ logExpConst_pos.le) hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one E n)
  have hsmul (n : ℕ) : f ((n : E) * x) = n * f x := by
    induction n with
    | zero => simp [f, smallExp_zero, smallLog_zero]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hadd _ _ (hnat n) hx, ih, add_mul, one_mul]
  have hbound (y : E) (hy : K * ‖y‖ < 1) : ‖f y - y‖ ≤ K * ‖y‖ ^ 2 := by
    have h1 := norm_smallLog_sub_le (hball y hy)
    rw [norm_smallExp_sub_one_eq hy] at h1
    have h2 := norm_smallExp_sub_le hy
    have h : f y - y = (smallLog l E (smallExp l E y - 1) - (smallExp l E y - 1)) +
        (smallExp l E y - 1 - y) := by
      change smallLog l E _ - y = _
      ring
    rw [h]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := inv_nonneg.mpr (zero_le_one.trans hl.le)
  have hr1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hlim (n : ℕ) : ‖f x - x‖ ≤ K * ‖x‖ ^ 2 * (l : ℝ)⁻¹ ^ n := by
    have hq : ‖((l ^ n : ℕ) : E)‖ = (l : ℝ)⁻¹ ^ n := by
      rw [norm_natCast_eq_pow_padicValNat (pow_ne_zero _ (Fact.out : l.Prime).ne_zero),
        padicValNat.prime_pow]
    have h := hbound _ (hnat (l ^ n))
    rw [hsmul, ← mul_sub, norm_mul, norm_mul, hq, mul_pow] at h
    have hpos : 0 < (l : ℝ)⁻¹ ^ n := pow_pos (inv_pos.mpr (zero_lt_one.trans hl)) n
    refine le_of_mul_le_mul_left ?_ hpos
    calc (l : ℝ)⁻¹ ^ n * ‖f x - x‖ ≤ K * ((l : ℝ)⁻¹ ^ n) ^ 2 * ‖x‖ ^ 2 := by
          rw [mul_assoc]; exact h
      _ = (l : ℝ)⁻¹ ^ n * (K * ‖x‖ ^ 2 * (l : ℝ)⁻¹ ^ n) := by ring
  have ht : Tendsto (fun n : ℕ ↦ K * ‖x‖ ^ 2 * (l : ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (K * ‖x‖ ^ 2)
  have h0 : ‖f x - x‖ ≤ 0 := ge_of_tendsto' ht hlim
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` the exponential inverts the logarithm:
`exp (log (1 + x)) = 1 + x`, since the logarithm is injective there and inverts the
exponential. -/
theorem smallExp_smallLog {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    smallExp l E (smallLog l E x) = 1 + x := by
  let := normedFieldOfAlgebra l E
  have hL : logExpConst l * ‖smallLog l E x‖ < 1 := by rwa [norm_smallLog_eq hx]
  have hb : logExpConst l * ‖smallExp l E (smallLog l E x) - 1‖ < 1 := by
    rwa [norm_smallExp_sub_one_eq hL]
  have h := norm_smallLog_sub_smallLog hb hx
  rw [smallLog_smallExp_sub_one hL, sub_self, norm_zero, eq_comm, norm_eq_zero,
    sub_eq_zero] at h
  linear_combination h

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

Let `E / ℚ_ℓ` be finite and `0 ≤ ρ < ℓ ^ (-1 / (ℓ - 1))`; for instance `ρ = |ϖ| ^ r` for a
uniformizer `ϖ` of `E` and `r > e / (ℓ - 1)`, `e = v_E(ℓ)`, the ball `‖x‖ ≤ ρ` then being
`𝔪_E ^ r`. On the ball `D = {‖x‖ ≤ ρ}` the series `log (1 + x) = ∑ (-1)^(n+1) x ^ n / n` and
`exp x = ∑ x ^ n / n!` converge, `x ↦ log (1 + x)` and `x ↦ exp x - 1` map `D` to itself, are
mutually inverse, and are isometries (hence continuous); `log` turns the multiplication of the
principal units `1 + D` into addition and `exp` turns addition into multiplication. -/
theorem smallLog_smallExp_deep {ρ : ℝ} (hρ : logExpConst l * ρ < 1) :
    letI := normedFieldOfAlgebra l E
    (∀ x : E, ‖x‖ ≤ ρ → (Summable fun n : ℕ ↦ (-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ)) ∧
        Summable fun n : ℕ ↦ x ^ n / (n ! : E)) ∧
      (∀ x : E, ‖x‖ ≤ ρ → ‖smallLog l E x‖ ≤ ρ ∧ ‖smallExp l E x - 1‖ ≤ ρ) ∧
      (∀ x : E, ‖x‖ ≤ ρ → smallLog l E (smallExp l E x - 1) = x ∧
        smallExp l E (smallLog l E x) = 1 + x) ∧
      (∀ x y : E, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
        smallLog l E (x + y + x * y) = smallLog l E x + smallLog l E y ∧
          smallExp l E (x + y) = smallExp l E x * smallExp l E y) ∧
      (∀ x y : E, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
        ‖smallLog l E x - smallLog l E y‖ = ‖x - y‖ ∧
          ‖smallExp l E x - smallExp l E y‖ = ‖x - y‖) := by
  let := normedFieldOfAlgebra l E
  have hD (x : E) (hx : ‖x‖ ≤ ρ) : logExpConst l * ‖x‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hx logExpConst_pos.le) hρ
  refine ⟨fun x hx ↦ ⟨summable_logSeries' (hD x hx), summable_expSeries (hD x hx)⟩,
    fun x hx ↦ ⟨?_, ?_⟩, fun x hx ↦ ⟨smallLog_smallExp_sub_one (hD x hx),
      smallExp_smallLog (hD x hx)⟩, fun x y hx hy ↦ ⟨smallLog_add_add_mul (hD x hx) (hD y hy),
      smallExp_add (hD x hx) (hD y hy)⟩, fun x y hx hy ↦
      ⟨norm_smallLog_sub_smallLog (hD x hx) (hD y hy),
        norm_smallExp_sub_smallExp (hD x hx) (hD y hy)⟩⟩
  · rwa [norm_smallLog_eq (hD x hx)]
  · rwa [norm_smallExp_sub_one_eq (hD x hx)]

end Inverse

section Units

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- An element of the maximal ideal of `𝒪_E` has norm `< 1`. -/
theorem norm_lt_one_of_mem_maximalIdeal {x : integers l E}
    (hx : x ∈ IsLocalRing.maximalIdeal (integers l E)) :
    ‖algebraMap E (PadicAlgCl l) (x : E)‖ < 1 := by
  have hle : ‖algebraMap E (PadicAlgCl l) (x : E)‖ ≤ 1 := by
    exact_mod_cast (mem_integers_iff l E _).1 x.2
  refine lt_of_le_of_ne hle fun h ↦ ?_
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    rw [h0, map_zero, norm_zero] at h
    exact zero_ne_one h
  have hinv : (x : E)⁻¹ ∈ integers l E := by
    rw [mem_integers_iff, map_inv₀, nnnorm_inv, ← NNReal.coe_le_coe, NNReal.coe_inv, coe_nnnorm,
      h, inv_one, NNReal.coe_one]
  refine (IsLocalRing.mem_maximalIdeal x).1 hx ⟨⟨x, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

For every `ρ > 0` there is `N ≥ 1` with `‖u ^ N - 1‖ ≤ ρ` for every unit `u` of `𝒪_E`: the
quotient `𝒪_Eˣ / (1 + 𝔪_E ^ k)` is finite, and `𝔪_E ^ k` lies in the ball of radius `|ϖ| ^ k`
for a uniformizer `ϖ`. -/
theorem exists_pow_norm_sub_one_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N : ℕ, 0 < N ∧ ∀ u : (integers l E)ˣ,
      ‖algebraMap E (PadicAlgCl l) (((u : integers l E) : E) ^ N - 1)‖ ≤ ρ := by
  obtain ⟨ϖ, hϖ⟩ := isPrincipal_maximalIdeal_integers l E
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (integers l E) := by
    rw [hϖ]
    exact Submodule.mem_span_singleton_self ϖ
  have hϖ1 := norm_lt_one_of_mem_maximalIdeal l E hϖm
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρ hϖ1
  let I := IsLocalRing.maximalIdeal (integers l E) ^ k
  have hI : I = Ideal.span {ϖ ^ k} := by
    change IsLocalRing.maximalIdeal (integers l E) ^ k = _
    rw [hϖ, Ideal.submodule_span_eq, Ideal.span_singleton_pow]
  set N := Nat.card (integers l E ⧸ I)ˣ with hN
  refine ⟨N, Nat.card_pos, fun u ↦ ?_⟩
  have hmem : (u : integers l E) ^ N - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_pow, sub_eq_zero]
    have h := pow_card_eq_one' (G := (integers l E ⧸ I)ˣ)
      (x := Units.map (Ideal.Quotient.mk I).toMonoidHom u)
    exact congrArg Units.val h
  rw [hI, Ideal.mem_span_singleton'] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hyE : ((u : integers l E) : E) ^ N - 1 = (y : E) * (ϖ : E) ^ k := by
    have := congrArg (fun z : integers l E ↦ (z : E)) hy
    push_cast at this
    exact this.symm
  rw [hyE, map_mul, map_pow, norm_mul, norm_pow]
  have hy1 : ‖algebraMap E (PadicAlgCl l) (y : E)‖ ≤ 1 := by
    exact_mod_cast (mem_integers_iff l E _).1 y.2
  calc ‖algebraMap E (PadicAlgCl l) (y : E)‖ * ‖algebraMap E (PadicAlgCl l) (ϖ : E)‖ ^ k
      ≤ 1 * ‖algebraMap E (PadicAlgCl l) (ϖ : E)‖ ^ k := by gcongr
    _ ≤ ρ := by rw [one_mul]; exact hk.le

omit [FiniteDimensional ℚ_[l] E] in
variable {l E} in
/-- For a generator `ϖ` of the maximal ideal of `𝒪_E`, the ideal `𝔪_E ^ r` is the closed ball of
radius `|ϖ| ^ r`. -/
theorem mem_maximalIdeal_pow_iff {ϖ : integers l E}
    (hϖ : IsLocalRing.maximalIdeal (integers l E) = Ideal.span {ϖ}) (r : ℕ) (x : integers l E) :
    x ∈ IsLocalRing.maximalIdeal (integers l E) ^ r ↔
      ‖algebraMap E (PadicAlgCl l) (x : E)‖ ≤ ‖algebraMap E (PadicAlgCl l) (ϖ : E)‖ ^ r := by
  rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    have hy1 : ‖algebraMap E (PadicAlgCl l) (y : E)‖ ≤ 1 := by
      exact_mod_cast (mem_integers_iff l E _).1 y.2
    change ‖algebraMap E (PadicAlgCl l) ((y : E) * (ϖ : E) ^ r)‖ ≤ _
    rw [map_mul, map_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) hy1
  · intro hx
    have hϖ0 : (ϖ : E) ≠ 0 := by
      intro h0
      apply maximalIdeal_integers_ne_bot l E
      rw [hϖ, Ideal.span_singleton_eq_bot]
      exact Subtype.ext h0
    have hn : 0 < ‖algebraMap E (PadicAlgCl l) (ϖ : E)‖ ^ r := by
      have : algebraMap E (PadicAlgCl l) (ϖ : E) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap E (PadicAlgCl l)).injective).2 hϖ0
      positivity
    have hy : (x : E) / (ϖ : E) ^ r ∈ integers l E := by
      rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, map_div₀, norm_div, map_pow,
        norm_pow, NNReal.coe_one, div_le_one hn]
      exact hx
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    push_cast
    field_simp

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: The logarithm on sufficiently deep
principal units.

Let `E / ℚ_ℓ` be finite, `ϖ` a uniformizer (a generator of the maximal ideal `𝔪_E` of `𝒪_E`),
`e = v_E(ℓ)`, i.e. `|ℓ| = |ϖ| ^ e`, and `r` an integer with `r > e / (ℓ - 1)`. Then
`𝔪_E ^ r` is the closed ball `D` of radius `|ϖ| ^ r < ℓ ^ (-1 / (ℓ - 1))`, so that on `D` the
series `log (1 + x)` and `exp x` converge and give mutually inverse isometric (hence continuous)
group isomorphisms `log : 1 + 𝔪_E ^ r ≅ 𝔪_E ^ r` and `exp : 𝔪_E ^ r ≅ 1 + 𝔪_E ^ r`
(`PadicAlgCl.smallLog_smallExp_deep`); moreover there is `N ≥ 1` with `u ^ N ∈ 1 + 𝔪_E ^ r` for
every unit `u` of `𝒪_E`. -/
theorem deep_principal_unit_log {ϖ : integers l E}
    (hϖ : IsLocalRing.maximalIdeal (integers l E) = Ideal.span {ϖ}) {e r : ℕ}
    (he : ‖(l : PadicAlgCl l)‖ = ‖algebraMap E (PadicAlgCl l) (ϖ : E)‖ ^ e)
    (hr : e < r * (l - 1)) :
    (∀ x : integers l E, x ∈ IsLocalRing.maximalIdeal (integers l E) ^ r ↔
      ‖algebraMap E (PadicAlgCl l) (x : E)‖ ≤ ‖algebraMap E (PadicAlgCl l) (ϖ : E)‖ ^ r) ∧
    logExpConst l * ‖algebraMap E (PadicAlgCl l) (ϖ : E)‖ ^ r < 1 ∧
    (∃ N : ℕ, 0 < N ∧ ∀ u : (integers l E)ˣ,
      (u : integers l E) ^ N - 1 ∈ IsLocalRing.maximalIdeal (integers l E) ^ r) := by
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (integers l E) := by
    rw [hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have hϖ1 := norm_lt_one_of_mem_maximalIdeal l E hϖm
  set a := ‖algebraMap E (PadicAlgCl l) (ϖ : E)‖ with ha
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h0
    apply maximalIdeal_integers_ne_bot l E
    rw [hϖ, Ideal.span_singleton_eq_bot]
    exact Subtype.ext h0
  have ha0 : 0 < a :=
    norm_pos_iff.2 ((map_ne_zero_iff _ (algebraMap E (PadicAlgCl l)).injective).2 hϖ0)
  refine ⟨mem_maximalIdeal_pow_iff hϖ r, ?_, ?_⟩
  · rw [mul_comm, mul_logExpConst_lt_one_iff (by positivity), ← pow_mul]
    have hl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
      have h : ‖(l : PadicAlgCl l)‖₊ = 1 / (l : ℝ≥0) := by
        rw [← PadicAlgCl.valuation_def]
        exact PadicAlgCl.valuation_p l
      rw [← coe_nnnorm, h]
      simp
    rw [← hl, he]
    exact pow_lt_pow_right_of_lt_one₀ ha0 hϖ1 hr
  · obtain ⟨N, hN, hu⟩ := exists_pow_norm_sub_one_le l E (pow_pos ha0 r)
    refine ⟨N, hN, fun u ↦ (mem_maximalIdeal_pow_iff hϖ r _).2 ?_⟩
    change ‖algebraMap E (PadicAlgCl l) (((u : integers l E) : E) ^ N - 1)‖ ≤ _
    exact hu u

end Units
section Characters

variable {l : ℕ} [Fact l.Prime] {E : Type w} [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- The principal units `1 + ℓ² 𝒪_E` lie in the domain `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` of the
logarithm, since `ℓ ^ (1 / (ℓ - 1)) ℓ⁻² ≤ ℓ⁻¹ < 1`. -/
theorem mul_logExpConst_lt_one_of_div_mem_integers {x : E}
    (hx : x / ((l : E) ^ 2) ∈ integers l E) :
    letI := normedFieldOfAlgebra l E
    logExpConst l * ‖x‖ < 1 := by
  let := normedFieldOfAlgebra l E
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := zero_lt_one.trans hl
  have hK : logExpConst l ≤ l := by
    have h1 : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
    calc logExpConst l ≤ logExpConst l ^ (l - 1) := le_self_pow₀ one_le_logExpConst h1
      _ = l := logExpConst_pow
  calc logExpConst l * ‖x‖ ≤ l * ((l : ℝ)⁻¹ ^ 2) :=
        mul_le_mul hK (norm_le_of_div_mem_integers hx) (norm_nonneg _) hl0.le
    _ = (l : ℝ)⁻¹ := by field_simp
    _ < 1 := inv_lt_one_of_one_lt₀ hl

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: A multiplicative curve character produces an
invariant additive character.

The core of the lemma, for a continuous character `χ : G → Eˣ` of a compact group: its values are
units of `𝒪_E` (the norms `|χ g| ^ n = |χ (g ^ n)|` are bounded for all `n ∈ ℤ`), so for some
`N ≥ 1` (`PadicAlgCl.exists_pow_norm_sub_one_le`) the character `χ ^ N` takes values in the
principal units `1 + ℓ² 𝒪_E = 1 + 𝔪_E ^ (2 e)`, where the logarithm is a homomorphism; then
`λ g = log (χ g ^ N)` is a continuous additive character `G → E`. -/
theorem exists_smallLog_pow_hom {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (χ : G →* Eˣ) (hχ : Continuous fun g ↦ algebraMap E (PadicAlgCl l) (χ g)) :
    ∃ N : ℕ, 0 < N ∧ (∀ g, χ g ^ N ∈ smallUnits l E) ∧
      (∀ g h, smallLog l E ((χ (g * h) : E) ^ N - 1) =
        smallLog l E ((χ g : E) ^ N - 1) + smallLog l E ((χ h : E) ^ N - 1)) ∧
      Continuous fun g ↦ algebraMap E (PadicAlgCl l) (smallLog l E ((χ g : E) ^ N - 1)) := by
  let ι := algebraMap E (PadicAlgCl l)
  -- the values of `χ` have norm one
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_norm.comp hχ)).bddAbove
  have hle (g : G) : ‖ι (χ g)‖ ≤ 1 := by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge h)
    have := hC ⟨g ^ n, rfl⟩
    simp only [Function.comp_apply, map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    exact absurd hn (not_lt.2 this)
  have hnorm (g : G) : ‖ι (χ g)‖ = 1 := by
    refine le_antisymm (hle g) ?_
    have h := hle g⁻¹
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, norm_inv] at h
    have hpos : 0 < ‖ι (χ g)‖ := norm_pos_iff.2 ((map_ne_zero_iff _ ι.injective).2 (χ g).ne_zero)
    exact (inv_le_one₀ hpos).1 h
  have hint (g : G) : (χ g : E) ∈ integers l E := by
    rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    exact (hnorm g).le
  let u (g : G) : (integers l E)ˣ :=
    ⟨⟨χ g, hint g⟩, ⟨χ g⁻¹, hint g⁻¹⟩,
      Subtype.ext (by
        change (χ g : E) * (χ g⁻¹ : E) = 1
        rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
      Subtype.ext (by
        change (χ g⁻¹ : E) * (χ g : E) = 1
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
  -- a power of `χ` lands in `1 + ℓ² 𝒪_E`
  have hl0 : 0 < ‖(l : PadicAlgCl l)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  obtain ⟨N, hN, hu⟩ := exists_pow_norm_sub_one_le l E (pow_pos hl0 2)
  have hsmall' (g : G) : ((χ g : E) ^ N - 1) / ((l : E) ^ 2) ∈ integers l E := by
    rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, map_div₀, norm_div, map_pow,
      map_natCast, norm_pow, NNReal.coe_one, div_le_one (pow_pos hl0 2)]
    exact hu (u g)
  have hsmall (g : G) : χ g ^ N ∈ smallUnits l E := by
    have h := hsmall' g
    rw [← Units.val_pow_eq_pow_val] at h
    exact h
  refine ⟨N, hN, hsmall, fun g h ↦ ?_, ?_⟩
  · have := smallLog_mul l E ⟨_, hsmall g⟩ ⟨_, hsmall h⟩
    simpa [Units.val_pow_eq_pow_val, mul_pow] using this
  · let := normedFieldOfAlgebra l E
    have hnorm' (y : E) : ‖y‖ = ‖ι y‖ := rfl
    have hball (g : G) : logExpConst l * ‖(χ g : E) ^ N - 1‖ < 1 :=
      mul_logExpConst_lt_one_of_div_mem_integers (hsmall' g)
    have ha : Continuous fun g ↦ ι ((χ g : E) ^ N - 1) := by
      simp only [map_sub, map_pow, map_one]
      exact (hχ.pow N).sub continuous_const
    have hdist (g g' : G) : dist (ι (smallLog l E ((χ g : E) ^ N - 1)))
        (ι (smallLog l E ((χ g' : E) ^ N - 1))) =
          dist (ι ((χ g : E) ^ N - 1)) (ι ((χ g' : E) ^ N - 1)) := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub, ← hnorm', ← hnorm']
      exact norm_smallLog_sub_smallLog (hball g) (hball g')
    refine Metric.continuous_iff'.2 fun g₀ ε hε ↦ ?_
    filter_upwards [Metric.continuous_iff'.1 ha g₀ ε hε] with g hg
    rwa [hdist]

end Characters

end PadicAlgCl
