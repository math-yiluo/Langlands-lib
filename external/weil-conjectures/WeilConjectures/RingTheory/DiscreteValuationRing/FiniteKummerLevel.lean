/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The finite Kummer level of `𝒪_E / ϖ^n`

Let `R` be a discrete valuation ring (for instance the valuation ring `𝒪_E` of a finite extension
`E` of `ℚ_ℓ`) with uniformizer `ϖ`, and let `ℓ` be a prime with `ℓ = (unit) · ϖ^e`, `e ≥ 1`, so
that `e` is the ramification index of `R` over `ℤ_ℓ`. If `e ∣ n`, say `n = e N`, then
`ϖ^n R = ℓ^N R` and the characteristic of `A = R / ϖ^n` is `ℓ^N`
(`IsDiscreteValuationRing.ringChar_quotient_span_pow`): `N` is the smallest exponent with
`ℓ^N A = 0`. This is the arithmetic part of blueprint `lem-pur-finite-kummer-level`.
-/

@[expose] public section

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  (hϖ : Irreducible ϖ) {ℓ : ℕ} (hℓ : ℓ.Prime) {e : ℕ} (he : 0 < e)
  (hℓe : Associated (ℓ : R) (ϖ ^ e))

omit [IsDiscreteValuationRing R] in
include hℓe in
/-- `ϖ^{e N} R = ℓ^N R`. -/
lemma span_pow_mul_eq_span_natCast_pow (N : ℕ) :
    Ideal.span {ϖ ^ (e * N)} = Ideal.span {(ℓ : R) ^ N} := by
  rw [Ideal.span_singleton_eq_span_singleton, pow_mul]
  exact (hℓe.pow_pow (n := N)).symm

include hϖ hℓ he hℓe in
/-- An integer `m` lies in `ℓ^N R` if and only if `ℓ^N` divides `m`: the prime-to-`ℓ` part of `m`
is a unit of `R`, the residue field having characteristic `ℓ`. -/
lemma natCast_mem_span_natCast_pow_iff (N m : ℕ) :
    (m : R) ∈ Ideal.span {(ℓ : R) ^ N} ↔ ℓ ^ N ∣ m := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ Ideal.mem_span_singleton.2 ⟨k, by simp [hk]⟩⟩
  rcases eq_or_ne m 0 with rfl | hm
  · exact dvd_zero _
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm ℓ hℓ.ne_one
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := hϖ.not_isUnit
  obtain ⟨v, hv⟩ := hℓe
  have hℓv : (ℓ : R) = ϖ ^ e * ↑v⁻¹ := by rw [← hv, mul_assoc, Units.mul_inv, mul_one]
  have hℓm : (ℓ : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [hℓv]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm e he)
  have hbu : IsUnit (b : R) := by
    by_contra hb'
    have hbm : (b : R) ∈ IsLocalRing.maximalIdeal R := hb'
    have hcop : Nat.Coprime b ℓ := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hb))
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := congrArg (Int.cast : ℤ → R) hxy
      push_cast at this
      rw [← this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hbm) (Ideal.mul_mem_left _ _ hℓm)
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hℓ0 : (ℓ : R) ≠ 0 := by
    rw [hℓv]
    exact mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) (Units.ne_zero _)
  have hℓu : ¬IsUnit (ℓ : R) := hℓm
  rw [Ideal.mem_span_singleton, Nat.cast_mul, Nat.cast_pow, hbu.dvd_mul_right,
    pow_dvd_pow_iff hℓ0 hℓu] at h
  exact Dvd.dvd.mul_right (pow_dvd_pow ℓ h) b

include hϖ hℓ he hℓe in
/-- Blueprint `lem-pur-finite-kummer-level`: Finite Kummer level of the Tate twist

The arithmetic part: if `ℓ = (unit) · ϖ^e` with `e ≥ 1` and `n = e N`, then `A = R / ϖ^n` has
characteristic `ℓ^N`, so `N` is the smallest exponent with `ℓ^N A = 0`. -/
lemma charP_quotient_span_pow (N : ℕ) : CharP (R ⧸ Ideal.span {ϖ ^ (e * N)}) (ℓ ^ N) := by
  refine ⟨fun m ↦ ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem,
    span_pow_mul_eq_span_natCast_pow hℓe, natCast_mem_span_natCast_pow_iff hϖ hℓ he hℓe]

include hϖ hℓ he hℓe in
/-- Blueprint `lem-pur-finite-kummer-level`: Finite Kummer level of the Tate twist

If `ℓ = (unit) · ϖ^e` with `e ≥ 1` and `n = e N`, the characteristic of `A = R / ϖ^n` is `ℓ^N`. -/
theorem ringChar_quotient_span_pow (N : ℕ) :
    ringChar (R ⧸ Ideal.span {ϖ ^ (e * N)}) = ℓ ^ N :=
  have := charP_quotient_span_pow hϖ hℓ he hℓe N
  ringChar.eq _ _

end IsDiscreteValuationRing
