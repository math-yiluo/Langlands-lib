/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Derivative
public import WeilConjectures.ZetaLinearAlgebra.DetTrace
public import WeilConjectures.ZetaSeries

/-!
# Trace data and the cohomological determinant factorisation

A *trace datum* over a field `K` is the linear algebra shadow of a Lefschetz trace formula:
finitely many finite dimensional `K`-vector spaces `V 0, …, V r`, each equipped with an
endomorphism `F i`, together with a sequence of integers `N n` computing the alternating
traces `N n = ∑ i, (-1) ^ i * tr (F i ^ n)`.

The determinant-trace identity of `WeilConjectures.ZetaLinearAlgebra.DetTrace` then factors
the counting exponential `Z = exp (∑ N n tⁿ / n)` as the alternating product of the reciprocal
characteristic polynomials `P i = det (1 - t F i)`:

`Z * ∏_{i even} P i = ∏_{i odd} P i`,

which is exactly the shape of `AlgebraicGeometry.IsWeilFactorization.factorization`.

## Main definitions

- `TraceDatum`: the structure above.
- `TraceDatum.P`: the reciprocal characteristic polynomial `det (1 - t F i)`.
- `TraceDatum.zeta`: the counting series `exp (∑ N n tⁿ / n) ∈ K⟦t⟧`.

## Main results

- `TraceDatum.zeta_mul_prod_even_eq_prod_odd`: the cohomological determinant factorisation
  `Z * ∏_{i even} P i = ∏_{i odd} P i`.
- `TraceDatum.map_zetaOfInt`: the counting series is the image of the corresponding rational
  counting series under `PowerSeries.map (algebraMap ℚ K)`.
- `TraceDatum.map_zetaSeries`: in particular, if the integers `N n` are the point counts of a
  scheme over a finite field, then `zeta` is the image of `Scheme.Hom.zetaSeries`.
-/

@[expose] public section

open PowerSeries

universe u v w

namespace PowerSeries

/-- The logarithmic derivative of the counting series `exp (∑_{n ≥ 1} a n tⁿ / n)` is the
generating series `∑_{n ≥ 1} a n tⁿ`. -/
theorem X_mul_derivative_exp_subst {K : Type*} [Field K] [CharZero K] (a : ℕ → K) :
    X * derivative (R := K) ((exp K).subst (mk fun n ↦ if n = 0 then 0 else a n / n)) =
      (mk fun n ↦ if n = 0 then 0 else a n) *
        (exp K).subst (mk fun n ↦ if n = 0 then 0 else a n / n) := by
  have hsub : HasSubst (mk fun n ↦ if n = 0 then 0 else a n / n) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have hXF : X * derivative (R := K) (mk fun n ↦ if n = 0 then 0 else a n / n) =
      mk fun n ↦ if n = 0 then 0 else a n := by
    ext n
    match n with
    | 0 => simp
    | m + 1 =>
      rw [coeff_succ_X_mul, coeff_derivative, coeff_mk, coeff_mk, ite_eq_right m.succ_ne_zero,
        ite_eq_right m.succ_ne_zero]
      have hm : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      push_cast
      rw [div_mul_cancel₀ _ hm]
  rw [derivative_subst hsub, derivative_exp, mul_comm (subst _ (exp K)), ← mul_assoc, hXF]

end PowerSeries

/-- A trace datum over a field `K`: finitely many finite dimensional `K`-vector spaces
`V 0, …, V r` with endomorphisms `F i`, together with integers `N n` computing the
alternating traces `∑ i, (-1) ^ i * tr (F i ^ n)`. This is the linear algebra shadow of a
Lefschetz trace formula. -/
structure TraceDatum (K : Type u) [Field K] (r : ℕ) where
  /-- The family of vector spaces, the shadow of the cohomology groups. -/
  V : Fin (r + 1) → Type v
  [addCommGroup : ∀ i, AddCommGroup (V i)]
  [module : ∀ i, Module K (V i)]
  [finiteDimensional : ∀ i, FiniteDimensional K (V i)]
  /-- The endomorphisms, the shadow of the action of Frobenius. -/
  F : ∀ i, Module.End K (V i)
  /-- The integers to be counted, the shadow of the numbers of rational points. -/
  N : ℕ → ℤ
  /-- The Lefschetz trace formula: `N n` is the alternating sum of the traces of `F i ^ n`. -/
  trace_eq : ∀ n, 1 ≤ n →
    (N n : K) = ∑ i : Fin (r + 1), (-1) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n)

attribute [instance] TraceDatum.addCommGroup TraceDatum.module TraceDatum.finiteDimensional

namespace TraceDatum

variable {K : Type u} [Field K] {r : ℕ}

/-- The alternating sum `∑ i, (-1) ^ i * c i` is the sum over the even indices minus the sum
over the odd indices. -/
private theorem sum_neg_one_pow_mul (c : Fin (r + 1) → K) :
    ∑ i : Fin (r + 1), (-1 : K) ^ (i : ℕ) * c i =
      (∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) ↦ Even (i : ℕ)), c i) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) ↦ Odd (i : ℕ)), c i := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Nat.even_or_odd (i : ℕ) with h | h
  · rw [ite_eq_left h, ite_eq_right (by simpa using h), h.neg_one_pow, one_mul, sub_zero]
  · rw [ite_eq_right (by simpa using h), ite_eq_left h, h.neg_one_pow, neg_one_mul, zero_sub]

variable (D : TraceDatum.{u, v} K r)

/-- The reciprocal characteristic polynomial `det (1 - t F i)` of the `i`-th endomorphism of a
trace datum. -/
noncomputable def P (i : Fin (r + 1)) : Polynomial K := (D.F i).charpolyRev

theorem P_def (i : Fin (r + 1)) : D.P i = (D.F i).charpolyRev := rfl

/-- The logarithmic derivative of `P i` is minus the generating series of the traces of the
powers of `F i`. -/
theorem X_mul_derivative_P (i : Fin (r + 1)) :
    X * derivative (R := K) (D.P i : K⟦X⟧) =
      (-PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K (D.V i) (D.F i ^ n)) *
        (D.P i : K⟦X⟧) :=
  LinearMap.X_mul_derivative_charpolyRev (D.F i)

/-- Every `P i` has constant coefficient `1`. -/
theorem constantCoeff_P (i : Fin (r + 1)) :
    PowerSeries.constantCoeff (D.P i : K⟦X⟧) = 1 := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, P_def,
    LinearMap.eval_charpolyRev]

/-- The counting series `exp (∑_{n ≥ 1} N n tⁿ / n)` of a trace datum, the linear algebra
analogue of `AlgebraicGeometry.Scheme.Hom.zetaSeries`. -/
noncomputable def zeta [CharZero K] : PowerSeries K :=
  (PowerSeries.exp K).subst (PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : K) / n)

private theorem hasSubst_zeta :
    PowerSeries.HasSubst (PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : K) / n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

/-- The counting series of a trace datum has constant coefficient `1`. -/
theorem constantCoeff_zeta [CharZero K] : PowerSeries.constantCoeff D.zeta = 1 := by
  have h0 : PowerSeries.coeff 0 D.zeta = 1 := by
    unfold zeta
    rw [PowerSeries.coeff_subst' (hb := D.hasSubst_zeta), finsum_eq_single _ 0
      fun d hd ↦ by simp [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, zero_pow hd]]
    simp [PowerSeries.coeff_exp]
  simpa using h0

/-- The logarithmic derivative of the counting series of a trace datum is the generating
series of the integers `N n`. -/
theorem X_mul_derivative_zeta [CharZero K] :
    X * derivative (R := K) D.zeta =
      (PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : K)) * D.zeta :=
  PowerSeries.X_mul_derivative_exp_subst _

/-- **The cohomological determinant factorisation**: the counting series of a trace datum is
the alternating product of the reciprocal characteristic polynomials of its endomorphisms,
`Z * ∏_{i even} det (1 - t F i) = ∏_{i odd} det (1 - t F i)`. -/
theorem zeta_mul_prod_even_eq_prod_odd [CharZero K] :
    D.zeta * ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) ↦ Even (i : ℕ)),
        (D.P i : PowerSeries K) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) ↦ Odd (i : ℕ)),
        (D.P i : PowerSeries K) := by
  set T : Fin (r + 1) → K⟦X⟧ := fun i ↦
    -PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K (D.V i) (D.F i ^ n)
    with hT
  set NS : K⟦X⟧ := PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : K) with hNS
  set se : Finset (Fin (r + 1)) := Finset.univ.filter (fun i : Fin (r + 1) ↦ Even (i : ℕ))
    with hse
  set so : Finset (Fin (r + 1)) := Finset.univ.filter (fun i : Fin (r + 1) ↦ Odd (i : ℕ))
    with hso
  have hP : ∀ i ∈ se, X * derivative (R := K) (D.P i : K⟦X⟧) = T i * (D.P i : K⟦X⟧) :=
    fun i _ ↦ D.X_mul_derivative_P i
  have hP' : ∀ i ∈ so, X * derivative (R := K) (D.P i : K⟦X⟧) = T i * (D.P i : K⟦X⟧) :=
    fun i _ ↦ D.X_mul_derivative_P i
  have hEven : X * derivative (R := K) (∏ i ∈ se, (D.P i : K⟦X⟧)) =
      (∑ i ∈ se, T i) * ∏ i ∈ se, (D.P i : K⟦X⟧) := X_mul_derivative_prod se hP
  have hOdd : X * derivative (R := K) (∏ i ∈ so, (D.P i : K⟦X⟧)) =
      (∑ i ∈ so, T i) * ∏ i ∈ so, (D.P i : K⟦X⟧) := X_mul_derivative_prod so hP'
  have hzeta := D.X_mul_derivative_zeta
  rw [← hNS] at hzeta
  have hLHS : X * derivative (R := K) (D.zeta * ∏ i ∈ se, (D.P i : K⟦X⟧)) =
      (NS + ∑ i ∈ se, T i) * (D.zeta * ∏ i ∈ se, (D.P i : K⟦X⟧)) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    linear_combination D.zeta * hEven + (∏ i ∈ se, (D.P i : K⟦X⟧)) * hzeta
  have hTcoeff : ∀ (i : Fin (r + 1)) (n : ℕ), n ≠ 0 →
      PowerSeries.coeff n (T i) = -LinearMap.trace K (D.V i) (D.F i ^ n) := by
    intro i n hn
    rw [hT]
    simp [ite_eq_right hn]
  have hkey : NS + ∑ i ∈ se, T i = ∑ i ∈ so, T i := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hT, hNS]
    · rw [map_add, map_sum, map_sum, hNS, PowerSeries.coeff_mk, ite_eq_right hn.ne',
        D.trace_eq n hn, sum_neg_one_pow_mul]
      simp only [hTcoeff _ _ hn.ne', Finset.sum_neg_distrib]
      ring
  have hconst : PowerSeries.constantCoeff (D.zeta * ∏ i ∈ se, (D.P i : K⟦X⟧)) =
      PowerSeries.constantCoeff (∏ i ∈ so, (D.P i : K⟦X⟧)) := by
    rw [map_mul, map_prod, map_prod, D.constantCoeff_zeta]
    simp [D.constantCoeff_P]
  have hA0 : PowerSeries.constantCoeff (NS + ∑ i ∈ se, T i) = 0 := by
    rw [map_add, map_sum, hNS]
    simp [hT]
  ext n
  exact PowerSeries.coeff_eq_of_X_mul_derivative_eq hLHS hOdd hconst hA0
    (m := n) (fun i _ ↦ by rw [hkey]) n le_rfl

/-- The counting series of a trace datum whose `N` is a sequence of integers is the image,
under `PowerSeries.map (algebraMap ℚ K)`, of the corresponding rational counting series. -/
theorem map_zetaOfInt [CharZero K] :
    PowerSeries.map (algebraMap ℚ K)
        ((PowerSeries.exp ℚ).subst
          (PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : ℚ) / n)) = D.zeta := by
  have hsub : PowerSeries.HasSubst
      (PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : ℚ) / n) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have hmk : PowerSeries.map (algebraMap ℚ K)
      (PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : ℚ) / n) =
      PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : K) / n := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    split
    · exact map_zero _
    · rw [map_div₀, map_intCast, map_natCast]
  have key : PowerSeries.map (algebraMap ℚ K)
      ((PowerSeries.exp ℚ).subst
        (PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : ℚ) / n)) =
      PowerSeries.subst
        (PowerSeries.map (algebraMap ℚ K)
          (PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : ℚ) / n))
        (PowerSeries.map (algebraMap ℚ K) (PowerSeries.exp ℚ)) :=
    PowerSeries.map_subst hsub _
  rw [key, PowerSeries.map_exp, hmk]
  rfl

section ZetaSeries

open AlgebraicGeometry

variable {Y : Scheme.{w}} {k : Type w} [Field k]

/-- If the integers of a trace datum are the point counts of a scheme `Y` over a finite field
`k`, then the counting series of the trace datum is the image of the zeta function of `Y`
under `PowerSeries.map (algebraMap ℚ K)`. -/
theorem map_zetaSeries [CharZero K] (f : Y.Hom (Spec (.of k)))
    (h : ∀ n, D.N n = f.pointCount n) :
    PowerSeries.map (algebraMap ℚ K) f.zetaSeries = D.zeta := by
  have hg : (PowerSeries.mk fun n ↦ if n = 0 then 0 else (f.pointCount n : ℚ) / n) =
      PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : ℚ) / n := by
    ext n
    simp only [PowerSeries.coeff_mk, h n]
    split <;> push_cast <;> ring
  have hz : f.zetaSeries = (PowerSeries.exp ℚ).subst
      (PowerSeries.mk fun n ↦ if n = 0 then 0 else (D.N n : ℚ) / n) := by
    unfold AlgebraicGeometry.Scheme.Hom.zetaSeries
    rw [hg]
  rw [hz, D.map_zetaOfInt]

end ZetaSeries

end TraceDatum
