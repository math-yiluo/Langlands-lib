/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Coefficients of powers of the combined power series ideal

Source: literature/stacks-project/algebra.tex, Remark Tag 032C; the coefficient
argument is steps 1--3 of lem-weil-pbc-power-series-complete-over-complete-base.
-/

@[expose] public section

universe u

private def coefficientIdeal {Λ : Type u} [CommRing Λ] (J : Ideal Λ) (d n : ℕ) :
    Ideal (MvPowerSeries (Fin d) Λ) where
  carrier := {F | ∀ E : Fin d →₀ ℕ, MvPowerSeries.coeff E F ∈ J ^ (n - E.degree)}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG E
    simpa only [map_add] using (J ^ (n - E.degree)).add_mem (hF E) (hG E)
  smul_mem' := by
    classical
    intro G F hF E
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    apply Submodule.sum_mem
    intro p hp
    have heq : p.1 + p.2 = E := Finset.mem_antidiagonal.mp hp
    have hdeg : p.2.degree ≤ E.degree := by
      rw [← heq, map_add]
      omega
    exact (J ^ (n - E.degree)).mul_mem_left _
      (Ideal.pow_le_pow_right (by omega) (hF p.2))

private theorem coefficientIdeal_mul {Λ : Type u} [CommRing Λ]
    (J : Ideal Λ) (d m n : ℕ) :
    coefficientIdeal J d m * coefficientIdeal J d n ≤ coefficientIdeal J d (m + n) := by
  classical
  apply Ideal.mul_le.mpr
  intro F hF G hG E
  rw [MvPowerSeries.coeff_mul]
  apply Submodule.sum_mem
  intro p hp
  have heq : p.1 + p.2 = E := Finset.mem_antidiagonal.mp hp
  have hdeg : p.1.degree + p.2.degree = E.degree := by rw [← heq, map_add]
  have hprod := Ideal.mul_mem_mul (hF p.1) (hG p.2)
  rw [← pow_add] at hprod
  exact Ideal.pow_le_pow_right (by omega) hprod

private theorem combinedIdeal_le_coefficientIdeal {Λ : Type u} [CommRing Λ]
    (J : Ideal Λ) (d : ℕ) :
    Ideal.map (algebraMap Λ (MvPowerSeries (Fin d) Λ)) J ⊔
      Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) Λ)) ≤
      coefficientIdeal J d 1 := by
  classical
  apply sup_le
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr E
    change MvPowerSeries.coeff E (MvPowerSeries.C r) ∈ J ^ (1 - E.degree)
    by_cases hE : E = 0
    · subst E
      simpa using hr
    · simp [MvPowerSeries.coeff_C, hE]
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩ E
    by_cases hE : E = Finsupp.single i 1
    · subst E
      simp
    · simp [MvPowerSeries.coeff_X, hE]

private theorem combinedIdeal_pow_le_coefficientIdeal {Λ : Type u} [CommRing Λ]
    (J : Ideal Λ) (d n : ℕ) :
    (Ideal.map (algebraMap Λ (MvPowerSeries (Fin d) Λ)) J ⊔
      Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) Λ))) ^ n ≤
      coefficientIdeal J d n := by
  induction n with
  | zero => intro F hF E; simp
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (combinedIdeal_le_coefficientIdeal J d)).trans
      (coefficientIdeal_mul J d n 1)

private theorem monomial_one_mem_variables_pow {Λ : Type u} [CommRing Λ]
    (d : ℕ) (E : Fin d →₀ ℕ) :
    MvPowerSeries.monomial E (1 : Λ) ∈
      (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) Λ))) ^
        E.degree := by
  classical
  let v : Ideal (MvPowerSeries (Fin d) Λ) := Ideal.span (Set.range MvPowerSeries.X)
  rw [MvPowerSeries.monomial_one_eq]
  have h := Ideal.prod_mem_prod (I := fun i : Fin d => v ^ E i)
    (x := fun i : Fin d => MvPowerSeries.X i ^ E i) (s := E.support)
    (fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) (E i))
  simpa [Finsupp.prod, Finsupp.degree, Finsupp.sum, Finset.prod_pow_eq_pow_sum, v] using h

private theorem zero_low_coefficients_mem_variables_pow {Λ : Type u} [CommRing Λ]
    (d n : ℕ) (F : MvPowerSeries (Fin d) Λ)
    (hF : ∀ E : Fin d →₀ ℕ, E.degree < n → MvPowerSeries.coeff E F = 0) :
    F ∈ (Ideal.span (Set.range
      (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) Λ))) ^ n := by
  classical
  let μ (E : Fin d →₀ ℕ) : Fin d →₀ ℕ :=
    if h : n ≤ E.degree then (Finsupp.exists_le_degree_eq E n h).choose else 0
  have hμ (E : Fin d →₀ ℕ) (h : n ≤ E.degree) : μ E ≤ E ∧ (μ E).degree = n := by
    simpa only [μ, dite_eq_left h] using (Finsupp.exists_le_degree_eq E n h).choose_spec
  let s : Finset (Fin d →₀ ℕ) := (Finsupp.finite_of_degree_eq n).toFinset
  let G (M : Fin d →₀ ℕ) : MvPowerSeries (Fin d) Λ :=
    fun B => if μ (M + B) = M then MvPowerSeries.coeff (M + B) F else 0
  have hsum : F = ∑ M ∈ s, MvPowerSeries.monomial M (1 : Λ) * G M := by
    apply MvPowerSeries.ext
    intro E
    simp only [map_sum, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hn : n ≤ E.degree
    · have hmem : μ E ∈ s := by simpa [s] using (hμ E hn).2
      rw [Finset.sum_eq_single (μ E)]
      · rw [ite_eq_left (hμ E hn).1]
        change MvPowerSeries.coeff E F =
          if μ (μ E + (E - μ E)) = μ E then
            MvPowerSeries.coeff (μ E + (E - μ E)) F else 0
        rw [add_tsub_cancel_of_le (hμ E hn).1, ite_eq_left rfl]
      · intro M hM hne
        by_cases hME : M ≤ E
        · rw [ite_eq_left hME]
          change (if μ (M + (E - M)) = M then
            MvPowerSeries.coeff (M + (E - M)) F else 0) = 0
          rw [add_tsub_cancel_of_le hME, ite_eq_right (Ne.symm hne)]
        · rw [ite_eq_right hME]
      · exact fun h => (h hmem).elim
    · rw [hF E (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro M hM
      have hdeg : M.degree = n := by simpa [s] using hM
      have hME : ¬ M ≤ E := by
        intro h
        have := Finsupp.degree_mono h
        omega
      rw [ite_eq_right hME]
  rw [hsum]
  apply Submodule.sum_mem
  intro M hM
  have hdeg : M.degree = n := by simpa [s] using hM
  exact Ideal.mul_mem_right _ _ (hdeg ▸ monomial_one_mem_variables_pow d M)

/-- Membership in a power of the ideal generated by the base ideal and the variables
is detected by the coefficients of total degree below that power.

Source: literature/stacks-project/algebra.tex, Remark Tag 032C, used without proof;
explicit coefficient argument, steps 1--3 of
lem-weil-pbc-power-series-complete-over-complete-base.
(blueprint: lem-weil-pbc-power-series-combined-ideal-coefficients).

Proof: Let S_n be the series whose coefficient at E of degree below n belongs to
J^(n-degree E). Coefficientwise addition and the finite Cauchy product show that S_n
is an ideal and S_n*S_m is contained in S_(n+m). The generators of the combined
ideal lie in S_1, so its nth power is contained in S_n. The nth power of the variables
ideal consists exactly of series with zero coefficients below degree n: partition
the exponents of degree at least n according to a chosen degree-n divisor, and
express the series as a finite sum of these monomials times power series. For the
reverse inclusion S_n is the sum of its finite low-degree part and its tail. The
tail belongs to the nth power of the variables ideal. Each low-degree monomial
has its coefficient in J^(n-degree E) and its variable factor in the degree E power
of the variables ideal, so belongs to the nth power of the combined ideal. This
also covers n=0 (both sides impose no condition) and d=0 (only E=0 occurs).
-/
theorem power_series_mem_combined_ideal_pow_iff
    (Λ : Type u) [CommRing Λ] (J : Ideal Λ) (d n : ℕ)
    (F : MvPowerSeries (Fin d) Λ) :
    F ∈ (Ideal.map (algebraMap Λ (MvPowerSeries (Fin d) Λ)) J ⊔
      Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) Λ))) ^ n ↔
    ∀ E : Fin d →₀ ℕ, E.degree < n → MvPowerSeries.coeff E F ∈ J ^ (n - E.degree) := by
  constructor
  · intro hF E hE
    exact combinedIdeal_pow_le_coefficientIdeal J d n hF E
  · intro hF
    classical
    let a : Ideal (MvPowerSeries (Fin d) Λ) :=
      Ideal.map (algebraMap Λ (MvPowerSeries (Fin d) Λ)) J ⊔
        Ideal.span (Set.range MvPowerSeries.X)
    let s : Finset (Fin d →₀ ℕ) := (Finsupp.finite_of_degree_lt n).toFinset
    let low : MvPowerSeries (Fin d) Λ := ∑ E ∈ s,
      MvPowerSeries.monomial E (MvPowerSeries.coeff E F)
    have hlow_coeff (E : Fin d →₀ ℕ) :
        MvPowerSeries.coeff E low = if E.degree < n then MvPowerSeries.coeff E F else 0 := by
      simp [low, MvPowerSeries.coeff_monomial, s]
    have htail : F - low ∈ a ^ n := by
      apply Ideal.pow_right_mono le_sup_right n
      apply zero_low_coefficients_mem_variables_pow d n
      intro E hE
      simp [map_sub, hlow_coeff, hE]
    have hlow : low ∈ a ^ n := by
      apply Submodule.sum_mem
      intro E hE
      have hdeg : E.degree < n := by simpa [s] using hE
      have hbase : MvPowerSeries.C (MvPowerSeries.coeff E F) ∈ a ^ (n - E.degree) := by
        apply Ideal.pow_right_mono le_sup_left (n - E.degree)
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ (hF E hdeg)
      have hvar : MvPowerSeries.monomial E (1 : Λ) ∈ a ^ E.degree :=
        Ideal.pow_right_mono le_sup_right E.degree (monomial_one_mem_variables_pow d E)
      have hprod := Ideal.mul_mem_mul hbase hvar
      rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hdeg)] at hprod
      change MvPowerSeries.monomial 0 (MvPowerSeries.coeff E F) *
        MvPowerSeries.monomial E (1 : Λ) ∈ a ^ n at hprod
      simpa only [MvPowerSeries.monomial_mul_monomial, zero_add, mul_one] using hprod
    exact (sub_add_cancel F low) ▸ (a ^ n).add_mem htail hlow
