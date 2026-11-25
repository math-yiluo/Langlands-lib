/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import WeilConjectures.ZetaLinearAlgebra.IntegralRecurrence
public import WeilConjectures.ZetaLinearAlgebra.NormalizedGauss

/-!
# The integral Fatou theorem

A power series with integer coefficients that is rational over `ℚ` is rational over `ℤ`: it can
be written as `A / B` with `A` and `B` integer polynomials whose constant coefficients are `1`.
This file combines the integral rational presentation
(`PowerSeries.exists_int_normalized_fraction'`) with the normalized Gauss lemma
(`Polynomial.exists_reduced_int_fraction`) to obtain the reduced form of such a presentation,
and to show that it is unique.

## Main statements

- `PowerSeries.exists_unique_reduced_int_fraction`: **the integral Fatou theorem**. An integral
  power series with constant coefficient `1` that is rational over `ℚ` has a *unique* pair of
  integer polynomials `(A, B)` with constant coefficients `1`, coprime over `ℚ`, and `f * B = A`.
- `PowerSeries.exists_int_fraction_of_rational`: the plain existence statement in the form the
  zeta function application needs, with the identity read in `ℚ⟦X⟧`.
-/

@[expose] public section

open Polynomial

namespace PowerSeries

/-- **The integral Fatou theorem**: a power series `f` with integer coefficients and constant
coefficient `1` that is rational over `ℚ` has a unique reduced normalized integral presentation,
that is a unique pair `(A, B)` of integer polynomials with constant coefficients `1`, coprime
after mapping to `ℚ[X]`, and satisfying `f * B = A`. -/
theorem exists_unique_reduced_int_fraction (f : ℤ⟦X⟧) (h₀ : constantCoeff f = 1)
    (h : ∃ A B : ℚ[X], B.coeff 0 = 1 ∧
      map (Int.castRingHom ℚ) f * (B : ℚ⟦X⟧) = (A : ℚ⟦X⟧)) :
    ∃! p : ℤ[X] × ℤ[X],
      p.1.coeff 0 = 1 ∧ p.2.coeff 0 = 1 ∧
      IsCoprime (p.1.map (Int.castRingHom ℚ)) (p.2.map (Int.castRingHom ℚ)) ∧
      f * (p.2 : ℤ⟦X⟧) = (p.1 : ℤ⟦X⟧) := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  obtain ⟨A₀, B₀, hB₀, hA₀f, hfB₀⟩ := exists_int_normalized_fraction' f h
  have hA₀ : A₀.coeff 0 = 1 := by
    rw [hA₀f, ← h₀, coeff_zero_eq_constantCoeff]
  obtain ⟨A, B, hA, hB, hcop, hfrac⟩ := Polynomial.exists_reduced_int_fraction hA₀ hB₀
  have hB₀ne : (B₀ : ℤ⟦X⟧) ≠ 0 := by
    simp only [ne_eq, Polynomial.coe_eq_zero_iff]
    intro h0
    simp [h0] at hB₀
  have key : f * (B : ℤ⟦X⟧) = (A : ℤ⟦X⟧) := by
    refine mul_left_cancel₀ hB₀ne ?_
    calc (B₀ : ℤ⟦X⟧) * (f * (B : ℤ⟦X⟧))
        = f * (B₀ : ℤ⟦X⟧) * (B : ℤ⟦X⟧) := by ring
      _ = ((A₀ * B : ℤ[X]) : ℤ⟦X⟧) := by rw [hfB₀, Polynomial.coe_mul]
      _ = ((B₀ * A : ℤ[X]) : ℤ⟦X⟧) := by rw [hfrac]
      _ = (B₀ : ℤ⟦X⟧) * (A : ℤ⟦X⟧) := Polynomial.coe_mul B₀ A
  refine ⟨(A, B), ⟨hA, hB, hcop, key⟩, ?_⟩
  rintro ⟨O, E⟩ ⟨hO, hE, hcop', hfOE⟩
  -- the two presentations agree as fractions
  have hcross : O * B = E * A := by
    refine Polynomial.coe_injective ℤ ?_
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← key, ← hfOE]
    ring
  have hcrossQ : O.map (Int.castRingHom ℚ) * B.map (Int.castRingHom ℚ)
      = E.map (Int.castRingHom ℚ) * A.map (Int.castRingHom ℚ) := by
    rw [← Polynomial.map_mul, ← Polynomial.map_mul, hcross]
  have hAQ : (A.map (Int.castRingHom ℚ)).coeff 0 = 1 := by rw [Polynomial.coeff_map, hA, map_one]
  have hOQ : (O.map (Int.castRingHom ℚ)).coeff 0 = 1 := by rw [Polynomial.coeff_map, hO, map_one]
  obtain ⟨hOA, hEB⟩ :=
    Polynomial.eq_of_coeff_zero_eq_one_of_isCoprime hAQ hOQ hcop hcop' hcrossQ
  exact Prod.ext (Polynomial.map_injective _ hinj hOA) (Polynomial.map_injective _ hinj hEB)

/-- A power series with integer coefficients that is rational over `ℚ` is the quotient of two
integer polynomials with constant coefficient `1`, the identity being read in `ℚ⟦X⟧`. This is
the form in which rationality of a zeta function is stated. -/
theorem exists_int_fraction_of_rational (f : ℤ⟦X⟧)
    (h : ∃ A B : ℚ[X], B.coeff 0 = 1 ∧
      map (Int.castRingHom ℚ) f * (B : ℚ⟦X⟧) = (A : ℚ⟦X⟧)) :
    ∃ P Q : ℤ[X], Q.coeff 0 = 1 ∧
      map (Int.castRingHom ℚ) f * (Q.map (Int.castRingHom ℚ) : ℚ⟦X⟧) =
        (P.map (Int.castRingHom ℚ) : ℚ⟦X⟧) := by
  obtain ⟨P, Q, hQ, hPQ⟩ := exists_int_normalized_fraction f h
  refine ⟨P, Q, hQ, ?_⟩
  rw [Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe, ← map_mul, hPQ]

end PowerSeries
