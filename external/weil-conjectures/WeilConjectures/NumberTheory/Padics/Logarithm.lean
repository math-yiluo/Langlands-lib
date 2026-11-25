/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecificLimits.Basic
public import WeilConjectures.Mathlib.Data.Nat.Choose.Dvd
public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# The small logarithm of a finite extension of `ℚ_ℓ`

For a finite extension `E/ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l` the series
`∑ (-1)^(n+1) x ^ n / n` converges for `x` in the maximal ideal of the ring of integers `𝒪_E`,
and on the subgroup `U_E = 1 + ℓ² 𝒪_E` of principal units it is an injective homomorphism to
`(E, +)`.

The topology and the uniform structure of `E` are those restricted from `ℚ̄_ℓ` along the
embedding `E → ℚ̄_ℓ`, i.e. those of `PadicAlgCl.normedFieldOfAlgebra`; they are definitions
rather than instances, since `ℓ` cannot be recovered from `E`. Finiteness of `E` over `ℚ_ℓ` is
what normalises the valuation, `v_ℓ(ℓ) = 1`, and is what makes the series converge on
`ℓ² 𝒪_E` and the logarithm injective there; accordingly every statement of this file assumes
it, while the two definitions, which make sense for any subfield of `ℚ̄_ℓ`, do not.

## Main definitions

- `PadicAlgCl.smallUnits` : the group `U_E = 1 + ℓ² 𝒪_E` of principal units.
- `PadicAlgCl.smallLog` : the logarithm `log (1 + x) = ∑ (-1)^(n+1) x ^ n / n`.

## Main statements

- `PadicAlgCl.summable_logSeries` : the logarithm series converges on `ℓ² 𝒪_E`.
- `PadicAlgCl.tendsto_pow_sub_one_div_smallLog` : `log u = lim (u ^ ℓⁿ - 1) / ℓⁿ` on `U_E`.
- `PadicAlgCl.smallLog_mul` and `PadicAlgCl.injOn_smallLog` : `u ↦ log u` is an injective
  homomorphism `U_E → (E, +)`.
-/

@[expose] public section

universe w

open Filter Topology
open scoped Nat

namespace PadicAlgCl

section Integers

variable {l : ℕ} [Fact l.Prime] {E : Type w} [Field E] [Algebra E (PadicAlgCl l)]

/-- The prime `ℓ` has norm `< 1` in `ℚ̄_ℓ`. -/
theorem nnnorm_natCast_lt_one : ‖(l : PadicAlgCl l)‖₊ < 1 := by
  have h : ‖(l : PadicAlgCl l)‖₊ = 1 / (l : NNReal) := by
    rw [← PadicAlgCl.valuation_def]; exact PadicAlgCl.valuation_p l
  have hl : (0 : NNReal) < (l : NNReal) := by
    exact_mod_cast (Fact.out : l.Prime).pos
  rw [h, div_lt_one hl]
  exact_mod_cast (Fact.out : l.Prime).one_lt

/-- A subfield of `ℚ̄_ℓ` has characteristic zero, so `ℓ ≠ 0` in it. -/
theorem natCast_ne_zero_of_algebra : (l : E) ≠ 0 := by
  intro h
  have h0 : (l : PadicAlgCl l) = 0 := by
    rw [← map_natCast (algebraMap E (PadicAlgCl l)) l, h, map_zero]
  exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h0

/-- The prime `ℓ` lies in the ring of integers `𝒪_E`. -/
theorem natCast_mem_integers : (l : E) ∈ integers l E := by
  rw [mem_integers_iff, map_natCast]
  exact le_of_lt nnnorm_natCast_lt_one

/-- If `a - 1 ∈ ℓ² 𝒪_E`, then `a` is a unit of `𝒪_E`: it is congruent to `1` modulo the
maximal ideal, so its norm is `1`. -/
theorem inv_mem_integers_of_sub_one_div {a : E}
    (ha : (a - 1) / ((l : E) ^ 2) ∈ integers l E) : a⁻¹ ∈ integers l E := by
  have hl0 : (l : E) ≠ 0 := natCast_ne_zero_of_algebra
  set f := algebraMap E (PadicAlgCl l) with hf
  set y := f ((a - 1) / ((l : E) ^ 2)) * (l : PadicAlgCl l) ^ 2 with hy
  have hsmall : ‖y‖₊ < 1 := by
    rw [hy, nnnorm_mul, nnnorm_pow]
    calc ‖f ((a - 1) / ((l : E) ^ 2))‖₊ * ‖(l : PadicAlgCl l)‖₊ ^ 2
        ≤ 1 * ‖(l : PadicAlgCl l)‖₊ ^ 2 := by
          gcongr
          exact (mem_integers_iff l E _).mp ha
      _ = ‖(l : PadicAlgCl l)‖₊ ^ 2 := one_mul _
      _ < 1 := pow_lt_one₀ zero_le nnnorm_natCast_lt_one two_ne_zero
  have hfa : f a = 1 + y := by
    rw [hy, hf, ← map_natCast (algebraMap E (PadicAlgCl l)) l, ← map_pow, ← map_mul,
      ← map_one (algebraMap E (PadicAlgCl l)), ← map_add]
    congr 1
    field_simp
    ring
  have hone : (1 : NNReal) ≤ ‖f a‖₊ := by
    by_cases h : (1 : NNReal) ≤ ‖f a‖₊
    · exact h
    · exfalso
      rw [not_le] at h
      have heq : (1 : PadicAlgCl l) = f a + -y := by rw [hfa]; ring
      have h1 : ‖(1 : PadicAlgCl l)‖ ≤ max ‖f a‖ ‖-y‖ := by
        rw [heq]; exact PadicAlgCl.isNonarchimedean l _ _
      rw [norm_one] at h1
      have hy1 : ‖(-y)‖ < 1 := by rw [norm_neg]; exact_mod_cast hsmall
      have ha1 : ‖f a‖ < 1 := by exact_mod_cast h
      exact absurd h1 (not_le.mpr (max_lt ha1 hy1))
  rw [mem_integers_iff, map_inv₀, nnnorm_inv, inv_le_one₀ (lt_of_lt_of_le zero_lt_one hone)]
  exact hone

/-- The norm of a natural number `m` in `E ⊆ ℚ̄_ℓ` is its `ℓ`-adic norm. -/
theorem norm_algebraMap_natCast (m : ℕ) :
    ‖algebraMap E (PadicAlgCl l) (m : E)‖ = ‖(m : ℚ_[l])‖ := by
  rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]

/-- The norm of a nonzero natural number `m` in `E ⊆ ℚ̄_ℓ` is `ℓ ^ (-v_ℓ(m))`. -/
theorem norm_natCast_eq_pow_padicValNat {m : ℕ} (hm : m ≠ 0) :
    letI := normedFieldOfAlgebra l E
    ‖(m : E)‖ = (l : ℝ)⁻¹ ^ padicValNat l m := by
  change ‖algebraMap E (PadicAlgCl l) (m : E)‖ = _
  rw [norm_algebraMap_natCast, Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hm),
    Padic.valuation_natCast, inv_pow, zpow_neg, zpow_natCast]

/-- An element `x ∈ ℓ² 𝒪_E` has norm `‖x‖ ≤ ℓ⁻²`. -/
theorem norm_le_of_div_mem_integers {x : E} (hx : x / ((l : E) ^ 2) ∈ integers l E) :
    letI := normedFieldOfAlgebra l E
    ‖x‖ ≤ (l : ℝ)⁻¹ ^ 2 := by
  let := normedFieldOfAlgebra l E
  have hr0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
  have hlE : ‖(l : E)‖ = (l : ℝ)⁻¹ := by
    rw [norm_natCast_eq_pow_padicValNat (Fact.out : l.Prime).ne_zero, padicValNat_self, pow_one]
  have h : ‖x / (l : E) ^ 2‖ ≤ 1 := by
    change ‖algebraMap E (PadicAlgCl l) _‖ ≤ 1
    exact_mod_cast (mem_integers_iff l E _).mp hx
  rwa [norm_div, norm_pow, hlE, div_le_one (pow_pos hr0 2)] at h

/-- On `ℓ² 𝒪_E` the `n`-th term `(-1)^n x ^ (n + 1) / (n + 1)` of the logarithm series has norm
at most `‖x‖ ℓ⁻ⁿ`, as `v_ℓ(n + 1) ≤ n`. -/
theorem norm_logSeries_term_le {x : E} (hx : x / ((l : E) ^ 2) ∈ integers l E) (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    ‖(-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ)‖ ≤ ‖x‖ * (l : ℝ)⁻¹ ^ n := by
  let := normedFieldOfAlgebra l E
  set r : ℝ := (l : ℝ)⁻¹ with hr
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr0 : 0 < r := inv_pos.mpr (zero_lt_one.trans hl)
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ hl.le
  have hxr : ‖x‖ ≤ r ^ 2 := norm_le_of_div_mem_integers hx
  have hv : padicValNat l (n + 1) ≤ n := Nat.lt_succ_iff.mp
    ((padicValNat_le_nat_log (p := l) (n + 1)).trans_lt (Nat.log_lt_self l n.succ_ne_zero))
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_natCast_eq_pow_padicValNat n.succ_ne_zero, div_le_iff₀ (pow_pos hr0 _), pow_succ',
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg x)
  calc ‖x‖ ^ n ≤ (r ^ 2) ^ n := pow_le_pow_left₀ (norm_nonneg x) hxr n
    _ = r ^ n * r ^ n := by rw [← pow_mul, ← pow_add, two_mul]
    _ ≤ r ^ n * r ^ padicValNat l (n + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1 hv) (by positivity)

/-- For `‖x‖ ≤ ℓ⁻¹` the difference quotient `((1 + x) ^ q - 1) / q` agrees with the `q`-th
partial sum of the logarithm series up to an error of norm at most `‖q‖`: the coefficient of
`x ^ (j + 1)` in it is `C(q - 1, j) / (j + 1)`, and `j! C(q - 1, j) ≡ (-1)^j j!` modulo `q`. -/
theorem norm_pow_sub_one_div_sub_sum_le {x : E}
    (hx : letI := normedFieldOfAlgebra l E; ‖x‖ ≤ (l : ℝ)⁻¹) (q : ℕ) :
    letI := normedFieldOfAlgebra l E
    ‖((1 + x) ^ q - 1) / q - ∑ j ∈ Finset.range q, (-1) ^ j * x ^ (j + 1) / (j + 1 : ℕ)‖ ≤
      ‖(q : E)‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
  set r : ℝ := (l : ℝ)⁻¹ with hr
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr0 : 0 < r := inv_pos.mpr (zero_lt_one.trans hl)
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ hl.le
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
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j hj ↦ ?_
  obtain ⟨w, hw⟩ := Nat.add_one_dvd_factorial_mul_choose_sub_neg_one_pow
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hw' : (j ! : E) * ((p.choose j : E) - (-1) ^ j) = ((p + 1 : ℕ) : E) * (w : E) := by
    exact_mod_cast hw
  have hj1 : ((j + 1 : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr j.succ_ne_zero
  have hfac : ((j + 1)! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hterm : ((p.choose j : E) * x ^ (j + 1) / (j + 1 : ℕ) -
      (-1) ^ j * x ^ (j + 1) / (j + 1 : ℕ)) * ((j + 1)! : E) =
      ((p + 1 : ℕ) : E) * (w : E) * x ^ (j + 1) := by
    rw [Nat.factorial_succ, Nat.cast_mul, ← hw']
    field_simp
  have hfacn : r ^ (j + 1) ≤ ‖((j + 1)! : E)‖ := by
    rw [norm_natCast_eq_pow_padicValNat (Nat.factorial_ne_zero _)]
    exact pow_le_pow_of_le_one hr0.le hr1 (padicValNat_factorial_le l _)
  have hpos : 0 < ‖((j + 1)! : E)‖ := norm_pos_iff.mpr hfac
  refine le_of_mul_le_mul_right ?_ hpos
  rw [← norm_mul, hterm, norm_mul, norm_mul, norm_pow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖(w : E)‖ * ‖x‖ ^ (j + 1) ≤ 1 * r ^ (j + 1) := by
        gcongr
        exact IsUltrametricDist.norm_intCast_le_one E w
    _ ≤ ‖((j + 1)! : E)‖ := by rw [one_mul]; exact hfacn

end Integers

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [instQ : Algebra ℚ_[l] E] [instT : IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [instF : FiniteDimensional ℚ_[l] E]

include instQ instT instF

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: Small logarithm.

The subgroup `U_E = 1 + ℓ² 𝒪_E` of `Eˣ`, where `𝒪_E = PadicAlgCl.integers l E` is the ring of
integers of `E`. -/
def smallUnits : Subgroup Eˣ where
  carrier := {u | ((u : E) - 1) / ((l : E) ^ 2) ∈ integers l E}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have hl0 : (l : E) ≠ 0 := natCast_ne_zero_of_algebra
    have key : (((a * b : Eˣ) : E) - 1) / ((l : E) ^ 2)
        = (((a : E) - 1) / ((l : E) ^ 2)) * (((b : E) - 1) / ((l : E) ^ 2)) * ((l : E) ^ 2)
          + ((a : E) - 1) / ((l : E) ^ 2) + ((b : E) - 1) / ((l : E) ^ 2) := by
      push_cast
      field_simp
      ring
    rw [key]
    exact add_mem (add_mem (mul_mem (mul_mem ha hb)
      (pow_mem natCast_mem_integers 2)) ha) hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hl0 : (l : E) ≠ 0 := natCast_ne_zero_of_algebra
    have ha0 : (a : E) ≠ 0 := a.ne_zero
    have key : (((a⁻¹ : Eˣ) : E) - 1) / ((l : E) ^ 2)
        = -((((a : E) - 1) / ((l : E) ^ 2)) * ((a : E)⁻¹)) := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
      ring
    rw [key]
    exact neg_mem (mul_mem ha (inv_mem_integers_of_sub_one_div ha))

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: Small logarithm.

`smallLog l E x` is the sum of the series `log (1 + x) = ∑_{n ≥ 1} (-1)^(n+1) x ^ n / n`,
formed in the topology restricted from `ℚ̄_ℓ`. It converges for `x ∈ ℓ² 𝒪_E`
(`PadicAlgCl.summable_logSeries`), and `u ↦ smallLog l E (u - 1)` is then an injective
homomorphism from `PadicAlgCl.smallUnits` to the additive group of `E`. -/
noncomputable def smallLog (x : E) : E :=
  letI := normedFieldOfAlgebra l E
  ∑' n : ℕ, (-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ)

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: Small logarithm.

The logarithm series converges on `ℓ² 𝒪_E`: the `n`-th term has valuation at least
`2 (n + 1) - v_ℓ(n + 1)`, which tends to infinity, and `E` is complete. -/
theorem summable_logSeries {x : E} (hx : x / ((l : E) ^ 2) ∈ integers l E) :
    letI := normedFieldOfAlgebra l E
    Summable fun n : ℕ ↦ (-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ) := by
  let := normedFieldOfAlgebra l E
  have := completeSpace_ofAlgebra l E
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one
    (inv_nonneg.mpr (zero_le_one.trans hl.le)) (inv_lt_one_of_one_lt₀ hl)).mul_left ‖x‖)
    (norm_logSeries_term_le hx)

omit instQ instT instF in
/-- Blueprint `theorem-rank-one-sheaves-have-finite`: Small logarithm.

On `ℓ² 𝒪_E` the logarithm does not increase the norm, `‖log (1 + x)‖ ≤ ‖x‖`: the term
`x ^ (n + 1) / (n + 1)` has norm `‖x‖ ^ (n + 1) / ‖n + 1‖ ≤ ‖x‖`, as
`‖x‖ ^ n ≤ ‖ℓ‖ ^ (2 n) ≤ ‖ℓ‖ ^ v_ℓ(n + 1) = ‖n + 1‖`, and the norm is nonarchimedean. In
particular `u ↦ log u` is continuous at `1`. -/
theorem norm_smallLog_le {x : E} (hx : x / ((l : E) ^ 2) ∈ integers l E) :
    ‖algebraMap E (PadicAlgCl l) (smallLog l E x)‖ ≤ ‖algebraMap E (PadicAlgCl l) x‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have hnorm (y : E) : ‖y‖ = ‖algebraMap E (PadicAlgCl l) y‖ := rfl
  rw [← hnorm, ← hnorm, smallLog]
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦
    (norm_logSeries_term_le hx n).trans (mul_le_of_le_one_right (norm_nonneg x) ?_)
  exact pow_le_one₀ (inv_nonneg.mpr (zero_le_one.trans hl.le)) (inv_le_one_of_one_le₀ hl.le)

/-- On `ℓ² 𝒪_E` the logarithm is the limit of the difference quotients
`((1 + x) ^ ℓⁿ - 1) / ℓⁿ`: these are within `‖ℓⁿ‖` of the `ℓⁿ`-th partial sum of the
logarithm series (`PadicAlgCl.norm_pow_sub_one_div_sub_sum_le`). -/
theorem tendsto_pow_sub_one_div_smallLog {x : E} (hx : x / ((l : E) ^ 2) ∈ integers l E) :
    letI := normedFieldOfAlgebra l E
    Tendsto (fun n : ℕ ↦ ((1 + x) ^ (l ^ n) - 1) / (l ^ n : ℕ)) atTop (𝓝 (smallLog l E x)) := by
  let := normedFieldOfAlgebra l E
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := inv_nonneg.mpr (zero_le_one.trans hl.le)
  have hr1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hx1 : ‖x‖ ≤ (l : ℝ)⁻¹ :=
    (norm_le_of_div_mem_integers hx).trans (pow_le_of_le_one hr0 hr1.le two_ne_zero)
  have hS := ((summable_logSeries l E hx).hasSum.tendsto_sum_nat).comp
    (tendsto_pow_atTop_atTop_of_one_lt (Fact.out : l.Prime).one_lt)
  have hdiff : Tendsto (fun n : ℕ ↦ ((1 + x) ^ (l ^ n) - 1) / (l ^ n : ℕ) -
      ∑ j ∈ Finset.range (l ^ n), (-1) ^ j * x ^ (j + 1) / (j + 1 : ℕ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ (norm_pow_sub_one_div_sub_sum_le hx1 _).trans_eq ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
    rw [norm_natCast_eq_pow_padicValNat (pow_ne_zero _ (Fact.out : l.Prime).ne_zero),
      padicValNat.prime_pow]
  have h := hdiff.add hS
  simp only [Function.comp_apply, sub_add_cancel, zero_add] at h
  exact h

/-- On `ℓ² 𝒪_E` the norm of `log (1 + x) - x` is at most `ℓ⁻¹ ‖x‖`, so the logarithm vanishes
only at `x = 0`. -/
theorem eq_zero_of_smallLog_eq_zero {x : E} (hx : x / ((l : E) ^ 2) ∈ integers l E)
    (h0 : smallLog l E x = 0) : x = 0 := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  set r : ℝ := (l : ℝ)⁻¹ with hr
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr0 : 0 ≤ r := inv_nonneg.mpr (zero_le_one.trans hl.le)
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hl
  have hsplit := (summable_logSeries l E hx).tsum_eq_zero_add
  change smallLog l E x = _ at hsplit
  simp only [pow_zero, zero_add, pow_one, one_mul, Nat.cast_one, div_one] at hsplit
  have hle : ‖∑' n : ℕ, (-1) ^ (n + 1) * x ^ (n + 1 + 1) / (n + 1 + 1 : ℕ)‖ ≤ ‖x‖ * r :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n ↦
      (norm_logSeries_term_le hx (n + 1)).trans
        (mul_le_mul_of_nonneg_left (pow_le_of_le_one hr0 hr1.le n.succ_ne_zero) (norm_nonneg x))
  rw [h0, eq_comm, add_eq_zero_iff_eq_neg] at hsplit
  have hxT : ‖x‖ = ‖∑' n : ℕ, (-1) ^ (n + 1) * x ^ (n + 1 + 1) / (n + 1 + 1 : ℕ)‖ := by
    conv_lhs => rw [hsplit]
    exact norm_neg _
  by_contra hne
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
  nlinarith

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: Small logarithm.

The logarithm turns the multiplication of `U_E` into the addition of `E`: writing
`a_n(u) = (u ^ ℓⁿ - 1) / ℓⁿ`, one has `a_n(uv) = ℓⁿ a_n(u) a_n(v) + a_n(u) + a_n(v)`, and
`a_n(u) → log u` (`PadicAlgCl.tendsto_pow_sub_one_div_smallLog`). -/
theorem smallLog_mul (u v : smallUnits l E) :
    smallLog l E (((u * v : smallUnits l E) : Eˣ) - 1)
      = smallLog l E (((u : Eˣ) : E) - 1) + smallLog l E (((v : Eˣ) : E) - 1) := by
  let := normedFieldOfAlgebra l E
  have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
  set a : E := ((u : Eˣ) : E)
  set b : E := ((v : Eˣ) : E)
  change smallLog l E (a * b - 1) = smallLog l E (a - 1) + smallLog l E (b - 1)
  have hu := tendsto_pow_sub_one_div_smallLog l E (x := a - 1) u.2
  have hv := tendsto_pow_sub_one_div_smallLog l E (x := b - 1) v.2
  have huv := tendsto_pow_sub_one_div_smallLog l E (x := a * b - 1) (u * v).2
  simp only [add_sub_cancel] at hu hv huv
  have hq : Tendsto (fun n : ℕ ↦ ((l ^ n : ℕ) : E)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (zero_le_one.trans hl.le))
      (inv_lt_one_of_one_lt₀ hl)).congr fun n ↦ ?_
    rw [norm_natCast_eq_pow_padicValNat (pow_ne_zero _ (Fact.out : l.Prime).ne_zero),
      padicValNat.prime_pow]
  have key (n : ℕ) : ((l ^ n : ℕ) : E) * ((a ^ (l ^ n) - 1) / (l ^ n : ℕ)) *
      ((b ^ (l ^ n) - 1) / (l ^ n : ℕ)) + (a ^ (l ^ n) - 1) / (l ^ n : ℕ) +
      (b ^ (l ^ n) - 1) / (l ^ n : ℕ) = ((a * b) ^ (l ^ n) - 1) / (l ^ n : ℕ) := by
    have hq0 : ((l ^ n : ℕ) : E) ≠ 0 :=
      Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    field_simp
    ring
  have hlim := (((hq.mul hu).mul hv).add hu).add hv
  rw [zero_mul, zero_mul, zero_add] at hlim
  exact tendsto_nhds_unique huv (hlim.congr key)

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: Small logarithm.

The logarithm is injective on `U_E = 1 + ℓ² 𝒪_E`: it is a homomorphism there, and its kernel
is trivial since `‖log (1 + x) - x‖ ≤ ℓ⁻¹ ‖x‖` (`PadicAlgCl.eq_zero_of_smallLog_eq_zero`).
This is what `theorem-rank-one-sheaves-have-finite` uses to turn a character of `π₁` with values in
`U_E` into a continuous additive character. -/
theorem injOn_smallLog :
    Set.InjOn (fun u : Eˣ ↦ smallLog l E ((u : E) - 1)) (smallUnits l E) := by
  intro u hu v hv huv
  have hw : u * v⁻¹ ∈ smallUnits l E := mul_mem hu (inv_mem hv)
  have h := smallLog_mul l E ⟨u * v⁻¹, hw⟩ ⟨v, hv⟩
  change smallLog l E (((u * v⁻¹ * v : Eˣ) : E) - 1) =
    smallLog l E (((u * v⁻¹ : Eˣ) : E) - 1) + smallLog l E ((v : E) - 1) at h
  rw [inv_mul_cancel_right] at h
  change smallLog l E ((u : E) - 1) = smallLog l E ((v : E) - 1) at huv
  rw [huv] at h
  have h0 := eq_zero_of_smallLog_eq_zero l E (x := ((u * v⁻¹ : Eˣ) : E) - 1) hw
    (by linear_combination -h)
  rw [sub_eq_zero, ← Units.val_one, Units.val_inj, mul_inv_eq_one] at h0
  exact h0

end PadicAlgCl
