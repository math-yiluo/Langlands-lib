/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.Rationality
public import WeilConjectures.ZetaLinearAlgebra.Recovery
public import Weil.Definitions

/-!
# The Weil factorisation and the Riemann hypothesis for a pure trace datum

Let `D` be a trace datum of length `2 * d` over a field `K` of characteristic zero, let
`ι : K →+* ℂ` be a ring embedding, and assume that the `i`-th reciprocal characteristic
polynomial `D.P i` becomes universally pure of weight `i` over `ℂ`, that `D.P 0 = 1 - t` and
that `D.P (2 * d) = 1 - qᵈ t`. If the counting series `Z` of `D` has integer coefficients,
then `Z` admits a Weil factorisation by integer polynomials satisfying the Riemann hypothesis.

This file is the junction of the two halves of the argument:

* the power-series half (`WeilConjectures.ZetaLinearAlgebra.Rationality`) writes `Z` as a
  normalized fraction of integer polynomials;
* the polynomial half (`WeilConjectures.ZetaLinearAlgebra.Recovery`) recovers the individual
  pure factors from a *reduced* such fraction.

Reducing the fraction is `Polynomial.exists_reduced_int_fraction`, and cross-multiplying the
resulting identity in `ℚ⟦X⟧` against the cohomological factorisation
`TraceDatum.zeta_mul_prod_even_eq_prod_odd` in `K⟦X⟧`, both transported into `ℂ⟦X⟧`, produces
the polynomial identity that the recovery theorem consumes.

The purity and normalisation hypotheses are stated over `ℂ`, that is for `(D.P i).map ι`
rather than for `D.P i`: purity is a statement about complex roots and has no meaning over
`K`, and the recovery theorem is stated over `ℂ`, so this is the form in which the hypotheses
are used.

## Main results

- `TraceDatum.exists_reduced_int_normalized_fraction`: the counting series of a trace datum is
  a fraction `A₀ / B₀` of normalized integer polynomials whose rational images are coprime.
- `TraceDatum.prod_odd_mul_eq_prod_even_mul`: the parity products of the complexified
  reciprocal characteristic polynomials cross-multiply against such a fraction.
- `TraceDatum.exists_isWeilFactorization`: a pure trace datum with integral counting series
  yields integer polynomials giving a Weil factorisation of the counting series and satisfying
  the Riemann hypothesis.
-/

@[expose] public section

universe u v

open PowerSeries

namespace TraceDatum

section General

variable {K : Type u} [Field K] [CharZero K] {r : ℕ} (D : TraceDatum.{u, v} K r)

/-- **A reduced normalized integral fraction for the counting series.** A power series with
integer coefficients whose image in `K⟦X⟧` is the counting series of a trace datum is a
fraction `A₀ / B₀` of integer polynomials with constant coefficient `1` whose images in `ℚ[X]`
are coprime. This is `TraceDatum.exists_int_normalized_fraction` followed by
`Polynomial.exists_reduced_int_fraction`. -/
theorem exists_reduced_int_normalized_fraction {Z : PowerSeries ℚ}
    (hZ : PowerSeries.map (algebraMap ℚ K) Z = D.zeta)
    (hint : ∃ Z' : PowerSeries ℤ, PowerSeries.map (Int.castRingHom ℚ) Z' = Z) :
    ∃ A₀ B₀ : Polynomial ℤ, A₀.coeff 0 = 1 ∧ B₀.coeff 0 = 1 ∧
      IsCoprime (A₀.map (Int.castRingHom ℚ)) (B₀.map (Int.castRingHom ℚ)) ∧
      Z * ((B₀.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
        ((A₀.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by
  obtain ⟨P, Q, hQ0, hPQ⟩ := D.exists_int_normalized_fraction hZ hint
  have hZ0 : PowerSeries.constantCoeff Z = 1 := by
    refine (algebraMap ℚ K).injective ?_
    rw [map_one, ← D.constantCoeff_zeta, ← hZ]
    rfl
  have hP0 : P.coeff 0 = 1 := by
    have h := congrArg (fun φ : PowerSeries ℚ ↦ PowerSeries.constantCoeff φ) hPQ
    simp only [map_mul, hZ0, one_mul, Polynomial.constantCoeff_coe, Polynomial.coeff_map,
      hQ0, map_one, eq_intCast] at h
    exact_mod_cast h.symm
  obtain ⟨A₀, B₀, hA₀, hB₀, hcop, hcross⟩ := Polynomial.exists_reduced_int_fraction hP0 hQ0
  refine ⟨A₀, B₀, hA₀, hB₀, hcop, ?_⟩
  have hQne : ((Q.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) ≠ 0 := by
    intro h0
    have h1 : PowerSeries.coeff 0
        ((Q.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) = 0 := by
      rw [h0, map_zero]
    rw [Polynomial.coeff_coe, Polynomial.coeff_map, hQ0] at h1
    simp at h1
  refine mul_right_cancel₀ hQne ?_
  calc Z * ((B₀.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
        ((Q.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ)
      = Z * ((Q.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
        ((B₀.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by ring
    _ = (((P * B₀).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by
        rw [hPQ, Polynomial.map_mul, Polynomial.coe_mul]
    _ = (((Q * A₀).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by rw [hcross]
    _ = ((A₀.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
        ((Q.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by
        rw [Polynomial.map_mul, Polynomial.coe_mul]; ring

/-- The cohomological factorisation of the counting series, transported from `K⟦X⟧` to `ℂ⟦X⟧`
along a ring embedding `ι : K →+* ℂ`. -/
theorem map_zeta_mul_prod_even_eq_prod_odd (ι : K →+* ℂ) {Z : PowerSeries ℚ}
    (hZ : PowerSeries.map (algebraMap ℚ K) Z = D.zeta) :
    PowerSeries.map (algebraMap ℚ ℂ) Z *
        ∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1,
          (((D.P i).map ι : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1,
        (((D.P i).map ι : Polynomial ℂ) : PowerSeries ℂ) := by
  have hcomp : ι.comp (algebraMap ℚ K) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hmapZ : PowerSeries.map (algebraMap ℚ ℂ) Z = PowerSeries.map ι D.zeta := by
    rw [← hZ, ← hcomp, PowerSeries.map_comp]
    rfl
  have h := congrArg (fun φ : PowerSeries K ↦ PowerSeries.map ι φ)
    D.zeta_mul_prod_even_eq_prod_odd
  simpa only [hmapZ, map_mul, map_prod, ← Polynomial.polynomial_map_coe] using h

/-- **The cross-multiplication identity consumed by the recovery theorem.** If `A / B` is a
normalized rational fraction for the counting series of a trace datum, then the parity products
of the complexified reciprocal characteristic polynomials cross-multiply against it. -/
theorem prod_odd_mul_eq_prod_even_mul (ι : K →+* ℂ) {Z : PowerSeries ℚ}
    (hZ : PowerSeries.map (algebraMap ℚ K) Z = D.zeta) {A B : Polynomial ℚ}
    (h : Z * (B : PowerSeries ℚ) = (A : PowerSeries ℚ)) :
    (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, (D.P i).map ι) *
        B.map (algebraMap ℚ ℂ) =
      (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, (D.P i).map ι) *
        A.map (algebraMap ℚ ℂ) := by
  have hcoe : ∀ s : Finset (Fin (r + 1)),
      ((∏ i ∈ s, (D.P i).map ι : Polynomial ℂ) : PowerSeries ℂ) =
        ∏ i ∈ s, (((D.P i).map ι : Polynomial ℂ) : PowerSeries ℂ) := fun s ↦ by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ Polynomial.coeToPowerSeries.ringHom_apply
  have hAB : PowerSeries.map (algebraMap ℚ ℂ) Z *
      ((B.map (algebraMap ℚ ℂ) : Polynomial ℂ) : PowerSeries ℂ) =
        ((A.map (algebraMap ℚ ℂ) : Polynomial ℂ) : PowerSeries ℂ) := by
    have h' := congrArg (fun φ : PowerSeries ℚ ↦ PowerSeries.map (algebraMap ℚ ℂ) φ) h
    simpa only [map_mul, ← Polynomial.polynomial_map_coe] using h'
  refine Polynomial.coe_injective ℂ ?_
  rw [Polynomial.coe_mul, Polynomial.coe_mul, hcoe, hcoe,
    ← D.map_zeta_mul_prod_even_eq_prod_odd ι hZ, ← hAB]
  ring

end General

section Weil

variable {K : Type u} [Field K] [CharZero K] {q d : ℕ} (D : TraceDatum.{u, v} K (2 * d))

/-- **The Weil factorisation and the Riemann hypothesis from a trace datum.** Let `D` be a
trace datum of length `2 * d` over a field of characteristic zero, embedded in `ℂ` by `ι`, such
that `(D.P i).map ι` is universally pure of weight `i` for every `i`, that `(D.P 0).map ι` is
`1 - t` and that `(D.P (2 * d)).map ι` is `1 - qᵈ t`. If the counting series `Z` of `D` has
integer coefficients, then there are integer polynomials `P 0, …, P (2 * d)` complexifying to
the `(D.P i).map ι` which give a Weil factorisation of `Z` and satisfy the Riemann hypothesis:
every complex root of `P i` has absolute value `q ^ (-i / 2)`. -/
theorem exists_isWeilFactorization (hq : 1 < q) (ι : K →+* ℂ)
    (hpure : ∀ i, ((D.P i).map ι).IsUniversallyPureOfWeight q i.1)
    (hzero : (D.P 0).map ι = 1 - Polynomial.X)
    (hlast : (D.P (Fin.last (2 * d))).map ι =
      1 - Polynomial.C ((q : ℂ) ^ d) * Polynomial.X)
    {Z : PowerSeries ℚ} (hZ : PowerSeries.map (algebraMap ℚ K) Z = D.zeta)
    (hint : ∃ Z' : PowerSeries ℤ, PowerSeries.map (Int.castRingHom ℚ) Z' = Z) :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      AlgebraicGeometry.IsWeilFactorization q d Z P ∧
      AlgebraicGeometry.WeilRiemannHypothesis q d P ∧
      ∀ i, (P i).map (Int.castRingHom ℂ) = (D.P i).map ι := by
  obtain ⟨A₀, B₀, hA₀, hB₀, hcop, hfrac⟩ := D.exists_reduced_int_normalized_fraction hZ hint
  obtain ⟨P, hP1, hP2, hP3⟩ := Polynomial.exists_int_norm_eq_of_isUniversallyPure
    (P := fun i ↦ (D.P i).map ι) hq hpure hcop hA₀ hB₀ rfl rfl
    (D.prod_odd_mul_eq_prod_even_mul ι hZ hfrac)
  have hcast : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  refine ⟨P, ⟨hP1, ?_, ?_, ?_⟩, hP3, hP2⟩
  · refine Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective ?_
    rw [hP2 0, hzero, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
  · refine Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective ?_
    rw [hP2 (Fin.last (2 * d)), hlast, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    norm_num
  · refine PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective ?_
    have hstep : ∀ i : Fin (2 * d + 1), PowerSeries.map (algebraMap ℚ ℂ)
        ((((P i).map (Int.castRingHom ℚ)) : Polynomial ℚ) : PowerSeries ℚ) =
          ((((D.P i).map ι) : Polynomial ℂ) : PowerSeries ℂ) := fun i ↦ by
      rw [← Polynomial.polynomial_map_coe, Polynomial.map_map, hcast, hP2 i]
    rw [map_mul, map_prod, map_prod]
    simp only [hstep]
    exact D.map_zeta_mul_prod_even_eq_prod_odd ι hZ

end Weil

end TraceDatum

end
