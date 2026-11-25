/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse

/-!
# Normalized Gauss lemma and the reduced normalized fraction over `ℤ`

Call a polynomial *normalized* if its constant coefficient is `1`. This file collects the
polynomial algebra behind the integral Fatou theorem: a normalized factorisation over `ℚ` of a
normalized integer polynomial is automatically integral, and a quotient of two normalized integer
polynomials can be brought into a reduced normalized integral form.

## Main results

- `Polynomial.exists_int_of_coeff_zero_eq_one_of_dvd` — a normalized rational divisor of a
  normalized integer polynomial is the image of a normalized integer polynomial.
- `Polynomial.exists_int_of_coeff_zero_eq_one_of_mul` — the normalized Gauss factor lemma: in a
  factorisation of a normalized integer polynomial into two normalized rational polynomials, both
  factors are integral.
- `Polynomial.eq_of_coeff_zero_eq_one_of_isCoprime` — a normalized fraction of coprime polynomials
  over a field is unique: `O / E = A / B` forces `O = A` and `E = B`.
- `Polynomial.exists_reduced_int_fraction` — a quotient of two normalized integer polynomials can
  be written as a quotient of two normalized integer polynomials whose images in `ℚ[X]` are
  coprime.
-/

@[expose] public section

namespace Polynomial

open scoped Polynomial

section Integer

private lemma natTrailingDegree_eq_zero_of_coeff_zero_eq_one {R : Type*} [Semiring R]
    [Nontrivial R] {p : R[X]} (hp : p.coeff 0 = 1) : p.natTrailingDegree = 0 :=
  natTrailingDegree_eq_zero.2 (.inr (by rw [hp]; exact one_ne_zero))

/-- A normalized rational divisor of a normalized integer polynomial comes from a normalized
integer polynomial. Here *normalized* means that the constant coefficient is `1`. -/
theorem exists_int_of_coeff_zero_eq_one_of_dvd {a : ℤ[X]} (ha : a.coeff 0 = 1) {p : ℚ[X]}
    (hp : p.coeff 0 = 1) (hdvd : p ∣ a.map (Int.castRingHom ℚ)) :
    ∃ p' : ℤ[X], p'.coeff 0 = 1 ∧ p'.map (Int.castRingHom ℚ) = p := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hamonic : a.reverse.Monic := monic_reverse_of_coeff_zero_eq_one ha
  have hpmonic : p.reverse.Monic := monic_reverse_of_coeff_zero_eq_one hp
  obtain ⟨c, hc⟩ := hdvd
  have hrev : p.reverse ∣ a.reverse.map (algebraMap ℤ ℚ) := by
    refine ⟨c.reverse, ?_⟩
    rw [algebraMap_int_eq, ← reverse_map hinj, hc, reverse_mul_of_domain]
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hamonic hrev
  rw [hpmonic.leadingCoeff, C_1, mul_one, algebraMap_int_eq] at hg
  have hgmonic : g.Monic := monic_of_injective hinj (hg ▸ hpmonic)
  refine ⟨g.reverse, ?_, ?_⟩
  · rw [coeff_zero_reverse, hgmonic.leadingCoeff]
  · rw [← reverse_map hinj, hg,
      reverse_reverse (natTrailingDegree_eq_zero_of_coeff_zero_eq_one hp)]

/-- **Normalized Gauss lemma**: if a normalized integer polynomial factors as a product of two
normalized rational polynomials, then both factors are images of normalized integer polynomials.
Here *normalized* means that the constant coefficient is `1`. -/
theorem exists_int_of_coeff_zero_eq_one_of_mul {a : ℤ[X]} (ha : a.coeff 0 = 1) {p q : ℚ[X]}
    (hp : p.coeff 0 = 1) (hq : q.coeff 0 = 1) (h : a.map (Int.castRingHom ℚ) = p * q) :
    ∃ p' q' : ℤ[X], p'.coeff 0 = 1 ∧ q'.coeff 0 = 1 ∧
      p'.map (Int.castRingHom ℚ) = p ∧ q'.map (Int.castRingHom ℚ) = q := by
  obtain ⟨p', hp', hp'p⟩ := exists_int_of_coeff_zero_eq_one_of_dvd ha hp ⟨q, h⟩
  obtain ⟨q', hq', hq'q⟩ := exists_int_of_coeff_zero_eq_one_of_dvd ha hq ⟨p, by rw [h, mul_comm]⟩
  exact ⟨p', q', hp', hq', hp'p, hq'q⟩

end Integer

/-- A normalized fraction of coprime polynomials over a field determines its numerator and
denominator: if `O * B = E * A` with all four polynomials normalized, `A` coprime to `B` and `O`
coprime to `E`, then `O = A` and `E = B`. Here *normalized* means that the constant coefficient
is `1`. -/
theorem eq_of_coeff_zero_eq_one_of_isCoprime {K : Type*} [Field K] {A B O E : K[X]}
    (hA : A.coeff 0 = 1) (hO : O.coeff 0 = 1) (hAB : IsCoprime A B) (hOE : IsCoprime O E)
    (h : O * B = E * A) : O = A ∧ E = B := by
  have hAO : A ∣ O := hAB.dvd_of_dvd_mul_right ⟨E, by rw [h, mul_comm]⟩
  have hOA : O ∣ A := hOE.dvd_of_dvd_mul_left ⟨B, h.symm⟩
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hAO hOA
  obtain ⟨r, -, hr⟩ := isUnit_iff.1 u.isUnit
  have hOA' : O = A * C r := by rw [hr, hu]
  have hr1 : r = 1 := by
    have := congrArg (fun p ↦ Polynomial.coeff p 0) hOA'
    simpa [hA, hO, coeff_C] using this.symm
  have hOA'' : O = A := by rw [hOA', hr1, C_1, mul_one]
  refine ⟨hOA'', ?_⟩
  have hA0 : A ≠ 0 := fun h0 ↦ by simp [h0] at hA
  rw [hOA''] at h
  exact (mul_right_cancel₀ hA0 (by rw [← h, mul_comm])).symm

/-- The quotient of two normalized integer polynomials can be reduced: there are normalized
integer polynomials `A` and `B` with coprime images in `ℚ[X]` such that `A₀ * B = B₀ * A`, i.e.
`A / B = A₀ / B₀`. Here *normalized* means that the constant coefficient is `1`. -/
theorem exists_reduced_int_fraction {A₀ B₀ : ℤ[X]} (hA₀ : A₀.coeff 0 = 1) (hB₀ : B₀.coeff 0 = 1) :
    ∃ A B : ℤ[X], A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
      IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧ A₀ * B = B₀ * A := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  set a : ℚ[X] := A₀.map (Int.castRingHom ℚ) with ha_def
  set b : ℚ[X] := B₀.map (Int.castRingHom ℚ) with hb_def
  have ha0 : a.coeff 0 = 1 := by rw [ha_def, coeff_map, hA₀, map_one]
  have hb0 : b.coeff 0 = 1 := by rw [hb_def, coeff_map, hB₀, map_one]
  have hbne : b ≠ 0 := fun h0 ↦ by simp [h0] at hb0
  -- reduce the fraction in `ℚ[X]`
  set g : ℚ[X] := gcd a b with hg_def
  have hgne : g ≠ 0 := gcd_ne_zero_of_right hbne
  set A₁ : ℚ[X] := a / g with hA₁_def
  set B₁ : ℚ[X] := b / g with hB₁_def
  have hcop : IsCoprime A₁ B₁ := isCoprime_div_gcd_div_gcd hbne
  have hga : g * A₁ = a := EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left a b)
  have hgb : g * B₁ = b := EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right a b)
  -- normalize the common factor
  set c : ℚ := g.coeff 0 with hc_def
  have hcA : c * A₁.coeff 0 = 1 := by rw [hc_def, ← mul_coeff_zero, hga, ha0]
  have hcB : c * B₁.coeff 0 = 1 := by rw [hc_def, ← mul_coeff_zero, hgb, hb0]
  have hc : c ≠ 0 := left_ne_zero_of_mul_eq_one hcA
  have hCc : IsUnit (C c) := isUnit_C.2 hc.isUnit
  set gN : ℚ[X] := C c⁻¹ * g with hgN_def
  set A' : ℚ[X] := C c * A₁ with hA'_def
  set B' : ℚ[X] := C c * B₁ with hB'_def
  have hA'0 : A'.coeff 0 = 1 := by rw [hA'_def, mul_coeff_zero, coeff_C_zero, hcA]
  have hB'0 : B'.coeff 0 = 1 := by rw [hB'_def, mul_coeff_zero, coeff_C_zero, hcB]
  have hgNA : gN * A' = a := by
    rw [hgN_def, hA'_def, mul_mul_mul_comm, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul, hga]
  have hgNB : gN * B' = b := by
    rw [hgN_def, hB'_def, mul_mul_mul_comm, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul, hgb]
  have hcopN : IsCoprime A' B' := (isCoprime_mul_units_left hCc hCc _ _).2 hcop
  -- pull the reduced fraction back to `ℤ[X]`
  have hdvdA : A' ∣ A₀.map (Int.castRingHom ℚ) := ⟨gN, by rw [← ha_def, ← hgNA, mul_comm]⟩
  have hdvdB : B' ∣ B₀.map (Int.castRingHom ℚ) := ⟨gN, by rw [← hb_def, ← hgNB, mul_comm]⟩
  obtain ⟨A, hA, hAmap⟩ := exists_int_of_coeff_zero_eq_one_of_dvd hA₀ hA'0 hdvdA
  obtain ⟨B, hB, hBmap⟩ := exists_int_of_coeff_zero_eq_one_of_dvd hB₀ hB'0 hdvdB
  refine ⟨A, B, hA, hB, by rw [hAmap, hBmap]; exact hcopN, ?_⟩
  refine map_injective (Int.castRingHom ℚ) hinj ?_
  rw [Polynomial.map_mul, Polynomial.map_mul, hAmap, hBmap, ← ha_def, ← hb_def, ← hgNA, ← hgNB]
  ring

end Polynomial
