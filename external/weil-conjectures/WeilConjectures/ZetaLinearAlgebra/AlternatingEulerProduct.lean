/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Expand
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.ZetaLinearAlgebra.CharpolyRevExpand
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# Euler products of alternating determinants

For a finite graded family `(W i, F i)` of endomorphisms of finite dimensional vector spaces
and `e ≥ 1`, the alternating determinant `Δ_e = ∏_i det (1 - T ^ e F i)^{(-1)^i}`
(`LinearMap.alternatingCharpolyRevProd`) is the expansion `T ↦ T ^ e` of `Δ_1`, has constant
coefficient `1`, and the logarithmic derivative of `Δ_e⁻¹` is the generating series

`∑_{e ∣ m} e (∑_i (-1)^i tr (F_i^{m / e})) T^m`.

Comparing logarithmic derivatives, a trace identity

`∑_i (-1)^i tr (A_i^m) = ∑_{j, e_j ∣ m} e_j ∑_i (-1)^i tr (B_{j,i}^{m / e_j})`, `m ≥ 1`,

between a family `A` and families `B_j` indexed by a set `J` with finitely many `j` of each
degree `e_j` gives the Euler product `∏_j Δ_{e_j}(B_j)⁻¹ = Δ_1(A)⁻¹`, the product being
coefficientwise locally finite.

## Main statements

- `LinearMap.X_mul_derivative_inv_alternatingCharpolyRevProd`: the logarithmic derivative of
  `Δ_e⁻¹`.
- `LinearMap.hasProd_inv_alternatingCharpolyRevProd_of_sum_trace_eq`: the Euler product.
-/

@[expose] public section

open PowerSeries

namespace LinearMap

variable {K : Type*} [Field K] {W : ℤ → Type*} [∀ i, AddCommGroup (W i)]
  [∀ i, Module K (W i)] [∀ i, FiniteDimensional K (W i)]

/-- The alternating determinant `∏_i det (1 - T ^ e F i)^{(-1)^i}` is the expansion `T ↦ T ^ e`
of `∏_i det (1 - T F i)^{(-1)^i}`. -/
theorem alternatingCharpolyRevProd_eq_expand (s : Finset ℤ) (F : ∀ i, Module.End K (W i))
    {e : ℕ} (he : e ≠ 0) :
    alternatingCharpolyRevProd s F e = expand e he (alternatingCharpolyRevProd s F 1) := by
  rw [alternatingCharpolyRevProd, alternatingCharpolyRevProd, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [pow_one, Polynomial.comp_X, ← Polynomial.expand_eq_comp_X_pow, coe_expand e he]
  split_ifs
  · rfl
  · rw [expand_inv]

/-- The alternating determinant `∏_i det (1 - T ^ e F i)^{(-1)^i}`, `e ≠ 0`, has constant
coefficient `1`. -/
theorem constantCoeff_alternatingCharpolyRevProd (s : Finset ℤ) (F : ∀ i, Module.End K (W i))
    {e : ℕ} (he : e ≠ 0) : constantCoeff (alternatingCharpolyRevProd s F e) = 1 := by
  rw [alternatingCharpolyRevProd, map_prod]
  refine Finset.prod_eq_one fun i _ ↦ ?_
  have h : constantCoeff (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) :
      K⟦X⟧) = 1 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
      Polynomial.eval_pow, Polynomial.eval_X, zero_pow he, eval_charpolyRev]
  split_ifs
  · exact h
  · rw [constantCoeff_inv, h, inv_one]

/-- The inverse `∏_i det (1 - T ^ e F i)^{(-1)^{i+1}}` of an alternating determinant, `e ≠ 0`, is
congruent to `1` modulo `T ^ e`. -/
theorem X_pow_dvd_inv_alternatingCharpolyRevProd_sub_one (s : Finset ℤ)
    (F : ∀ i, Module.End K (W i)) {e : ℕ} (he : e ≠ 0) :
    X ^ e ∣ (alternatingCharpolyRevProd s F e)⁻¹ - 1 := by
  rw [alternatingCharpolyRevProd_eq_expand s F he, ← expand_inv]
  have h := X_pow_dvd_expand_sub_C_constantCoeff e he (alternatingCharpolyRevProd s F 1)⁻¹
  rwa [constantCoeff_inv, constantCoeff_alternatingCharpolyRevProd s F one_ne_zero, inv_one,
    map_one] at h

/-- The logarithmic derivative of the inverse `∏_i det (1 - T ^ e F i)^{(-1)^{i+1}}` of an
alternating determinant, `e ≠ 0`, is the generating series
`∑_{e ∣ m} e (∑_i (-1)^i tr (F_i^{m / e})) T^m` of the alternating traces. -/
theorem X_mul_derivative_inv_alternatingCharpolyRevProd (s : Finset ℤ)
    (F : ∀ i, Module.End K (W i)) {e : ℕ} (he : e ≠ 0) :
    X * derivative (R := K) (alternatingCharpolyRevProd s F e)⁻¹ =
      (PowerSeries.mk fun m ↦ if m ≠ 0 ∧ e ∣ m then
        (e : K) * ∑ i ∈ s, (i.negOnePow : ℤ) • trace K (W i) (F i ^ (m / e)) else 0) *
        (alternatingCharpolyRevProd s F e)⁻¹ := by
  set B : ℤ → K⟦X⟧ := fun i ↦ PowerSeries.mk fun m ↦
    if m ≠ 0 ∧ e ∣ m then (e : K) * trace K (W i) (F i ^ (m / e)) else 0 with hB
  have hP (i : ℤ) : X * derivative (R := K) (((F i).charpolyRev.comp (Polynomial.X ^ e) :
      Polynomial K) : K⟦X⟧) = -B i * (((F i).charpolyRev.comp (Polynomial.X ^ e) :
      Polynomial K) : K⟦X⟧) := by
    rw [← Polynomial.expand_eq_comp_X_pow, coe_expand e he]
    exact X_mul_derivative_expand_charpolyRev (F i) e he
  have hP0 (i : ℤ) : constantCoeff (((F i).charpolyRev.comp (Polynomial.X ^ e) :
      Polynomial K) : K⟦X⟧) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
      Polynomial.eval_pow, Polynomial.eval_X, zero_pow he, eval_charpolyRev]
    exact one_ne_zero
  have hfac : ∀ i ∈ s, X * derivative (R := K) (if Even i then
      (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧) else
      (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧)⁻¹) =
      (-((i.negOnePow : ℤ) • B i)) * (if Even i then
      (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧) else
      (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧)⁻¹) := by
    intro i _
    split_ifs with h
    · rw [Int.negOnePow_even _ h, Units.val_one, one_smul]
      exact hP i
    · rw [Int.negOnePow_odd _ (Int.not_even_iff_odd.1 h), Units.val_neg, Units.val_one,
        neg_smul, one_smul, neg_neg, X_mul_derivative_inv (hP i) (hP0 i), neg_neg]
  have h0 := constantCoeff_alternatingCharpolyRevProd s F he
  rw [alternatingCharpolyRevProd] at h0 ⊢
  rw [X_mul_derivative_inv (PowerSeries.X_mul_derivative_prod s hfac)
    (by rw [h0]; exact one_ne_zero), Finset.sum_neg_distrib, neg_neg]
  congr 1
  ext m
  rw [map_sum, PowerSeries.coeff_mk]
  simp only [hB, coeff_smul, PowerSeries.coeff_mk]
  split_ifs
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_smul_comm]
  · simp

open scoped PowerSeries.WithPiTopology in
/-- **Euler products of alternating determinants.** Let `A` be a finite graded family of
endomorphisms and `(B j)_{j ∈ J}` finite graded families with degrees `e j ≥ 1`, finitely many
of each degree, such that for every `m ≥ 1`

`∑_i (-1)^i tr (A_i^m) = ∑_{j, e_j ∣ m} e_j ∑_i (-1)^i tr (B_{j,i}^{m / e_j})`

(the right hand side being computed over any finite set of indices containing those `j` with
`e_j ∣ m`). Then `∏_j Δ_{e_j}(B_j)⁻¹ = Δ_1(A)⁻¹` for the alternating determinants
`Δ_e(F) = ∏_i det (1 - T ^ e F i)^{(-1)^i}`, the product being coefficientwise locally
finite. -/
theorem hasProd_inv_alternatingCharpolyRevProd_of_sum_trace_eq [CharZero K]
    [TopologicalSpace K] (s : Finset ℤ) (A : ∀ i, Module.End K (W i)) {J : Type*}
    {U : J → ℤ → Type*} [∀ j i, AddCommGroup (U j i)] [∀ j i, Module K (U j i)]
    [∀ j i, FiniteDimensional K (U j i)] (B : ∀ j i, Module.End K (U j i)) (e : J → ℕ)
    (he : ∀ j, e j ≠ 0) (hfin : ∀ n, {j | e j ≤ n}.Finite)
    (htr : ∀ m, 1 ≤ m → ∀ T : Finset J, (∀ j, e j ∣ m → j ∈ T) →
      ∑ i ∈ s, (i.negOnePow : ℤ) • trace K (W i) (A i ^ m) =
        ∑ j ∈ T with e j ∣ m,
          e j • ∑ i ∈ s, (i.negOnePow : ℤ) • trace K (U j i) (B j i ^ (m / e j))) :
    HasProd (fun j ↦ (alternatingCharpolyRevProd s (B j) (e j))⁻¹)
      (alternatingCharpolyRevProd s A 1)⁻¹ := by
  classical
  set S : ℕ → Finset J := fun n ↦ (hfin n).toFinset with hS
  have hmem {n : ℕ} {j : J} (h : e j ≤ n) : j ∈ S n := (hfin n).mem_toFinset.2 h
  have hdvd (n : ℕ) (j : J) (hj : j ∉ S n) :
      X ^ (n + 1) ∣ (alternatingCharpolyRevProd s (B j) (e j))⁻¹ - 1 := by
    have hnj : n + 1 ≤ e j := by
      by_contra h
      exact hj (hmem (by omega))
    exact (pow_dvd_pow X hnj).trans (X_pow_dvd_inv_alternatingCharpolyRevProd_sub_one s (B j)
      (he j))
  convert WithPiTopology.hasProd_of_X_pow_dvd_sub_one S hdvd using 1
  ext n
  rw [PowerSeries.coeff_mk]
  refine (coeff_eq_of_X_mul_derivative_eq (PowerSeries.X_mul_derivative_prod (S n)
    fun j _ ↦ X_mul_derivative_inv_alternatingCharpolyRevProd s (B j) (he j))
    (X_mul_derivative_inv_alternatingCharpolyRevProd s A one_ne_zero) ?_ ?_ ?_ n le_rfl).symm
  · rw [map_prod, constantCoeff_inv, constantCoeff_alternatingCharpolyRevProd s A one_ne_zero,
      inv_one]
    refine Finset.prod_eq_one fun j _ ↦ ?_
    rw [constantCoeff_inv, constantCoeff_alternatingCharpolyRevProd s (B j) (he j), inv_one]
  · simp
  · intro m hm
    rw [map_sum, PowerSeries.coeff_mk]
    simp only [PowerSeries.coeff_mk]
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    · rw [ite_eq_left ⟨hm0, one_dvd m⟩, Nat.cast_one, one_mul, Nat.div_one,
        htr m (Nat.one_le_iff_ne_zero.2 hm0) (S n) fun j hj ↦
          hmem ((Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hj).trans hm), Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hj : e j ∣ m
      · rw [ite_eq_left ⟨hm0, hj⟩, ite_eq_left hj, nsmul_eq_mul]
      · rw [ite_eq_right fun h ↦ hj h.2, ite_eq_right hj]

end LinearMap
