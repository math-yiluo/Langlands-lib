/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.RingTheory.PowerSeries.Expand
public import WeilConjectures.ZetaLinearAlgebra.DetTrace

/-!
# Reciprocal characteristic polynomials determined by traces of powers

Let `A` be an endomorphism of a finite dimensional vector space over a field of characteristic
zero, and let `Bᵢ` be finitely many endomorphisms together with positive integers `eᵢ`. If the
traces of the powers of `A` are

`tr (Aᵐ) = ∑_{i, eᵢ ∣ m} eᵢ tr (Bᵢ^{m / eᵢ})`, `m ≥ 1`,

then `det (1 - T A) = ∏ᵢ det (1 - T^{eᵢ} Bᵢ)`
(`LinearMap.charpolyRev_eq_prod_expand_of_trace_pow_eq`): both sides have constant term `1` and
logarithmic derivative minus the generating series of these traces. This is the linear algebra
behind the computation of the local Frobenius of a finite direct image: the Frobenius at a point
permutes the points above it, an orbit of length `e` contributing `det (1 - T^e F_x)`.

Over an algebraically closed field, every nonzero eigenvalue `β` of `A` then has a power `β^{eᵢ}`
which is an eigenvalue of some `Bᵢ` (`LinearMap.exists_hasEigenvalue_pow_of_trace_pow_eq`).
-/

@[expose] public section

open PowerSeries

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The image in `K⟦X⟧` of the expansion `f (Xᵖ)` of a polynomial is the expansion of its
image. -/
theorem coe_expand (p : ℕ) (hp : p ≠ 0) (f : Polynomial K) :
    ((Polynomial.expand K p f : Polynomial K) : K⟦X⟧) = PowerSeries.expand p hp (f : K⟦X⟧) := by
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_expand,
    Polynomial.coeff_expand (Nat.pos_of_ne_zero hp)]
  split_ifs <;> simp

/-- The logarithmic derivative of the expansion `det (1 - Tᵉ B)`: it is minus the generating
series of the traces `e tr (B^{m / e})`, `e ∣ m`. -/
theorem X_mul_derivative_expand_charpolyRev {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (B : Module.End K W) (e : ℕ) (he : e ≠ 0) :
    X * derivative (R := K) (PowerSeries.expand e he (B.charpolyRev : K⟦X⟧)) =
      (-PowerSeries.mk fun m ↦ if m ≠ 0 ∧ e ∣ m then (e : K) * trace K W (B ^ (m / e)) else 0) *
        PowerSeries.expand e he (B.charpolyRev : K⟦X⟧) := by
  set P : K⟦X⟧ := (B.charpolyRev : K⟦X⟧)
  set T : K⟦X⟧ := PowerSeries.mk fun n ↦ if n = 0 then 0 else trace K W (B ^ n)
  have hP := X_mul_derivative_charpolyRev B
  have hsubst : PowerSeries.HasSubst (X ^ e : K⟦X⟧) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [he])
  have hD : derivative (R := K) (PowerSeries.expand e he P) =
      PowerSeries.expand e he (derivative (R := K) P) * ((e : K⟦X⟧) * X ^ (e - 1)) := by
    rw [PowerSeries.expand_apply, PowerSeries.expand_apply, PowerSeries.derivative_subst hsubst]
    congr 1
    rw [Derivation.leibniz_pow, PowerSeries.derivative_X, smul_eq_mul, nsmul_eq_mul, mul_one]
  have hT : PowerSeries.expand e he ((e : K⟦X⟧) * T) =
      PowerSeries.mk fun m ↦ if m ≠ 0 ∧ e ∣ m then (e : K) * trace K W (B ^ (m / e)) else 0 := by
    ext m
    rw [map_mul, map_natCast, PowerSeries.coeff_mk, ← map_natCast (PowerSeries.C (R := K)),
      PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]
    by_cases hm : e ∣ m
    · obtain ⟨k, rfl⟩ := hm
      rw [ite_eq_left (dvd_mul_right e k), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he)]
      by_cases hk : k = 0
      · subst hk; simp [T]
      · rw [ite_eq_left ⟨mul_ne_zero he hk, dvd_mul_right e k⟩]
        simp [T, hk]
    · rw [ite_eq_right hm, ite_eq_right fun h ↦ hm h.2, mul_zero]
  have key := congrArg (PowerSeries.expand e he) hP
  rw [map_mul, map_mul, PowerSeries.expand_X, map_neg] at key
  rw [hD, ← hT, map_mul]
  calc X * (PowerSeries.expand e he (derivative (R := K) P) * ((e : K⟦X⟧) * X ^ (e - 1)))
      = (e : K⟦X⟧) * (X ^ e * PowerSeries.expand e he (derivative (R := K) P)) := by
        rw [show X ^ e = X ^ (e - 1) * X from by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero he)]]
        ring
    _ = _ := by
        rw [key, map_natCast]
        ring

/-- The logarithmic derivative of a finite product of expansions `det (1 - T^{eᵢ} Bᵢ)`. -/
theorem X_mul_derivative_prod_expand_charpolyRev {ι : Type*} (s : Finset ι) {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] [∀ i, FiniteDimensional K (W i)]
    (B : ∀ i, Module.End K (W i)) (e : ι → ℕ) (he : ∀ i, e i ≠ 0) :
    X * derivative (R := K) (∏ i ∈ s, PowerSeries.expand (e i) (he i) ((B i).charpolyRev : K⟦X⟧)) =
      (-∑ i ∈ s, PowerSeries.mk fun m ↦
          if m ≠ 0 ∧ e i ∣ m then (e i : K) * trace K (W i) (B i ^ (m / e i)) else 0) *
        ∏ i ∈ s, PowerSeries.expand (e i) (he i) ((B i).charpolyRev : K⟦X⟧) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have h1 := X_mul_derivative_expand_charpolyRev (B a) (e a) (he a)
    linear_combination (PowerSeries.expand (e a) (he a) ((B a).charpolyRev : K⟦X⟧)) * ih +
      (∏ i ∈ s, PowerSeries.expand (e i) (he i) ((B i).charpolyRev : K⟦X⟧)) * h1

/-- **The reciprocal characteristic polynomial is determined by the traces of the powers.** If
`tr (Aᵐ) = ∑_{i ∈ s, eᵢ ∣ m} eᵢ tr (Bᵢ^{m / eᵢ})` for every `m ≥ 1`, then
`det (1 - T A) = ∏_{i ∈ s} det (1 - T^{eᵢ} Bᵢ)`. -/
theorem charpolyRev_eq_prod_expand_of_trace_pow_eq [CharZero K] (A : Module.End K V)
    {ι : Type*} (s : Finset ι) {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)] (B : ∀ i, Module.End K (W i)) (e : ι → ℕ)
    (he : ∀ i, e i ≠ 0)
    (h : ∀ m, m ≠ 0 → trace K V (A ^ m) =
      ∑ i ∈ s, if e i ∣ m then (e i : K) * trace K (W i) (B i ^ (m / e i)) else 0) :
    A.charpolyRev = ∏ i ∈ s, Polynomial.expand K (e i) (B i).charpolyRev := by
  rw [← Polynomial.coe_inj, show ((∏ i ∈ s, Polynomial.expand K (e i) (B i).charpolyRev :
      Polynomial K) : K⟦X⟧) = ∏ i ∈ s, ((Polynomial.expand K (e i) (B i).charpolyRev :
        Polynomial K) : K⟦X⟧) from map_prod Polynomial.coeToPowerSeries.ringHom _ _]
  simp only [coe_expand _ (he _)]
  have hA := X_mul_derivative_charpolyRev A
  have hB := X_mul_derivative_prod_expand_charpolyRev s B e he
  have hsum : (∑ i ∈ s, PowerSeries.mk fun m ↦
      if m ≠ 0 ∧ e i ∣ m then (e i : K) * trace K (W i) (B i ^ (m / e i)) else 0) =
        PowerSeries.mk fun n ↦ if n = 0 then 0 else trace K V (A ^ n) := by
    ext m
    rw [map_sum, PowerSeries.coeff_mk]
    simp only [PowerSeries.coeff_mk]
    by_cases hm : m = 0
    · simp [hm]
    · rw [ite_eq_right hm, h m hm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [hm]
  rw [hsum] at hB
  have h0 : PowerSeries.constantCoeff (A.charpolyRev : K⟦X⟧) =
      PowerSeries.constantCoeff
        (∏ i ∈ s, PowerSeries.expand (e i) (he i) ((B i).charpolyRev : K⟦X⟧)) := by
    rw [map_prod]
    simp only [PowerSeries.constantCoeff_expand, Polynomial.constantCoeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, eval_charpolyRev, Finset.prod_const_one]
  ext n
  exact PowerSeries.coeff_eq_of_X_mul_derivative_eq hA hB h0 (by simp) (m := n)
    (fun _ _ ↦ rfl) n le_rfl

section IsAlgClosed

variable [IsAlgClosed K]

omit [FiniteDimensional K V] in
/-- Over an algebraically closed field, if `t` is a root of `det (1 - T B)`, then `t⁻¹` is an
eigenvalue of `B`. -/
theorem hasEigenvalue_inv_of_eval_charpolyRev_eq_zero {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (B : Module.End K W) {t : K}
    (ht : Polynomial.eval t B.charpolyRev = 0) : B.HasEigenvalue t⁻¹ := by
  rw [charpolyRev_eq_prod_roots, Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff,
    Multiset.mem_map] at ht
  obtain ⟨_, ha, hz⟩ := ht
  obtain ⟨a, ha', rfl⟩ := Multiset.mem_map.1 ha
  have hat : a * t = 1 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hz
    linear_combination -hz
  rw [← eq_inv_of_mul_eq_one_left hat, Module.End.hasEigenvalue_iff_isRoot_charpoly]
  exact (Polynomial.mem_roots (charpoly_monic B).ne_zero).1 ha'

omit [FiniteDimensional K V] in
/-- Over an algebraically closed field, the inverse of a nonzero eigenvalue `β` of `B` is a root
of `det (1 - T B)`. -/
theorem eval_inv_charpolyRev_eq_zero_of_hasEigenvalue {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (B : Module.End K W) {β : K} (hβ : B.HasEigenvalue β)
    (hβ0 : β ≠ 0) : Polynomial.eval β⁻¹ B.charpolyRev = 0 := by
  rw [charpolyRev_eq_prod_roots, Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff,
    Multiset.mem_map]
  refine ⟨1 - Polynomial.C β * Polynomial.X, Multiset.mem_map.2 ⟨β, ?_, rfl⟩, ?_⟩
  · rw [Module.End.hasEigenvalue_iff_isRoot_charpoly] at hβ
    exact (Polynomial.mem_roots (charpoly_monic B).ne_zero).2 hβ
  · simp [hβ0]

/-- If `det (1 - T A) = ∏_{i ∈ s} det (1 - T^{eᵢ} Bᵢ)`, then for every nonzero eigenvalue `β`
of `A` some power `β^{eᵢ}` is an eigenvalue of `Bᵢ`. -/
theorem exists_hasEigenvalue_pow_of_charpolyRev_eq (A : Module.End K V)
    {ι : Type*} (s : Finset ι) {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)] (B : ∀ i, Module.End K (W i)) (e : ι → ℕ)
    (hA : A.charpolyRev = ∏ i ∈ s, Polynomial.expand K (e i) (B i).charpolyRev) {β : K}
    (hβ : A.HasEigenvalue β) (hβ0 : β ≠ 0) : ∃ i ∈ s, (B i).HasEigenvalue (β ^ e i) := by
  have h0 := eval_inv_charpolyRev_eq_zero_of_hasEigenvalue A hβ hβ0
  rw [hA, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨i, hi, hz⟩ := h0
  rw [Polynomial.expand_eval, inv_pow] at hz
  exact ⟨i, hi, by simpa using hasEigenvalue_inv_of_eval_charpolyRev_eq_zero (B i) hz⟩

/-- If `det (1 - T A) = det (1 - T^d B)` with `d ≠ 0`, then every nonzero eigenvalue `γ` of `B`
is the `d`-th power of an eigenvalue of `A`: any `d`-th root of `γ` is one. -/
theorem exists_hasEigenvalue_pow_eq_of_charpolyRev_eq_expand (A : Module.End K V) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (B : Module.End K W) {d : ℕ}
    (hd : d ≠ 0) (hA : A.charpolyRev = Polynomial.expand K d B.charpolyRev) {γ : K}
    (hγ : B.HasEigenvalue γ) (hγ0 : γ ≠ 0) : ∃ β, A.HasEigenvalue β ∧ β ^ d = γ := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq γ (Nat.pos_of_ne_zero hd)
  refine ⟨β, ?_, hβ⟩
  have h0 := eval_inv_charpolyRev_eq_zero_of_hasEigenvalue B hγ hγ0
  rw [← hβ, ← inv_pow, ← Polynomial.expand_eval, ← hA] at h0
  simpa using hasEigenvalue_inv_of_eval_charpolyRev_eq_zero A h0

end IsAlgClosed

end LinearMap

namespace Polynomial

variable {R L : Type*} [CommSemiring R] [CommSemiring L] (ι : R →+* L) (σ : L →+* L)

/-- The coefficients of `P` have images under `ι` fixed by `σ` if and only if the image of `P`
under `ι` is fixed by `σ`. -/
theorem forall_coeff_fixed_iff_map_map (P : R[X]) :
    (∀ n, σ (ι (P.coeff n)) = ι (P.coeff n)) ↔ (P.map ι).map σ = P.map ι := by
  simp only [Polynomial.ext_iff, coeff_map]

/-- If the coefficients of the `Pₐ` have images under `ι` fixed by `σ`, so do those of their
product. (For `σ` the complex conjugation: a product of `ι`-real polynomials is `ι`-real.) -/
theorem coeff_prod_fixed {α : Type*} (s : Finset α) (P : α → R[X])
    (h : ∀ a ∈ s, ∀ n, σ (ι ((P a).coeff n)) = ι ((P a).coeff n)) (n : ℕ) :
    σ (ι ((∏ a ∈ s, P a).coeff n)) = ι ((∏ a ∈ s, P a).coeff n) := by
  revert n
  rw [forall_coeff_fixed_iff_map_map, Polynomial.map_prod, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun a ha ↦ (forall_coeff_fixed_iff_map_map ι σ _).1 (h a ha)

/-- The coefficients of the expansion `P (Xᵖ)`, `p ≠ 0`, have images under `ι` fixed by `σ` if
and only if those of `P` do. -/
theorem forall_coeff_expand_fixed_iff {p : ℕ} (hp : p ≠ 0) (P : R[X]) :
    (∀ n, σ (ι ((expand R p P).coeff n)) = ι ((expand R p P).coeff n)) ↔
      ∀ n, σ (ι (P.coeff n)) = ι (P.coeff n) := by
  refine ⟨fun h n ↦ ?_, fun h n ↦ ?_⟩
  · simpa [coeff_expand_mul (Nat.pos_of_ne_zero hp)] using h (n * p)
  · rw [coeff_expand (Nat.pos_of_ne_zero hp)]
    split_ifs
    · exact h _
    · simp

end Polynomial
