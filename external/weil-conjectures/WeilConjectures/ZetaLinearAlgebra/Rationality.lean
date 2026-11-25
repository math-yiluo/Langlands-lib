/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaIntegrality
public import WeilConjectures.ZetaLinearAlgebra.Fatou
public import WeilConjectures.ZetaLinearAlgebra.Hankel
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# Rationality and integrality of the counting series of a trace datum

A trace datum `D` over a field `K` of characteristic zero factors its counting series as an
alternating product of reciprocal characteristic polynomials,
`D.zeta * ∏_{i even} D.P i = ∏_{i odd} D.P i`
(`TraceDatum.zeta_mul_prod_even_eq_prod_odd`). This file turns that factorisation over `K`
into the rationality statement the Weil conjectures need, over `ℚ` and then over `ℤ`:

* Hankel descent (`PowerSeries.exists_normalized_fraction_of_map_rat`) pushes a normalized
  fraction over `K` down to a normalized fraction over `ℚ`;
* the integral Fatou theorem (`PowerSeries.exists_int_fraction_of_rational`) upgrades a
  normalized fraction over `ℚ` of a series with integer coefficients to one over `ℤ`.

A trace datum says nothing about the arithmetic of its integers `D.N n`, so integrality of the
counting series is a hypothesis at this level of generality. For the zeta series of a scheme of
finite type over a finite field it is a theorem, `Scheme.Hom.exists_int_zetaSeries`, and the
final corollary of this file therefore assumes nothing beyond the existence of a trace datum
computing the point counts.

That corollary is `AlgebraicGeometry.Scheme.zetaSeries_rational` up to the trace datum: the
`sorry` in `WeilConjectures.Statement` remains, since producing a trace datum out of a scheme
requires a cohomology theory, which this subtree does not build.

## Main results

- `TraceDatum.exists_rat_normalized_fraction`: any rational power series whose image in `K⟦X⟧`
  is the counting series of a trace datum is a normalized fraction `A / B` of rational
  polynomials, `B 0 = 1`.
- `TraceDatum.exists_int_normalized_fraction`: if moreover that rational series has integer
  coefficients, then it is a normalized fraction `P / Q` of integer polynomials, `Q 0 = 1`.
- `AlgebraicGeometry.Scheme.Hom.zetaSeries_rational_of_traceDatum`: the zeta series of a
  scheme of finite type over a finite field admitting a trace datum for its point counts is a
  normalized fraction of integer polynomials.
-/

@[expose] public section

universe u v w

open PowerSeries

namespace TraceDatum

variable {K : Type u} [Field K] [CharZero K] {r : ℕ} (D : TraceDatum.{u, v} K r)

/-- **Rationality of the counting series over `ℚ`**: a rational power series whose image in
`K⟦X⟧` is the counting series of a trace datum is a fraction `A / B` of rational polynomials
with `B 0 = 1`. The numerator and the denominator are the odd and the even part of the
cohomological factorisation, pushed down to `ℚ` by Hankel descent. -/
theorem exists_rat_normalized_fraction {Z : PowerSeries ℚ}
    (hZ : PowerSeries.map (algebraMap ℚ K) Z = D.zeta) :
    ∃ A B : Polynomial ℚ, B.coeff 0 = 1 ∧ Z * (B : PowerSeries ℚ) = (A : PowerSeries ℚ) := by
  have hcoe : ∀ s : Finset (Fin (r + 1)), ((∏ i ∈ s, D.P i : Polynomial K) : PowerSeries K) =
      ∏ i ∈ s, (D.P i : PowerSeries K) := fun s ↦ by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ Polynomial.coeToPowerSeries.ringHom_apply
  refine PowerSeries.exists_normalized_fraction_of_map_rat K Z
    ⟨∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) ↦ Odd (i : ℕ)), D.P i,
      ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) ↦ Even (i : ℕ)), D.P i, ?_, ?_⟩
  · have h1 : ∀ i : Fin (r + 1), Polynomial.constantCoeff (D.P i) = 1 := fun i ↦ by
      have h := D.constantCoeff_P i
      rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe] at h
    rw [← Polynomial.constantCoeff_apply, map_prod]
    exact Finset.prod_eq_one fun i _ ↦ h1 i
  · rw [hZ, hcoe, hcoe, D.zeta_mul_prod_even_eq_prod_odd]

/-- **Rationality and integrality of the counting series**: a power series with integer
coefficients whose image in `K⟦X⟧` is the counting series of a trace datum is a fraction
`P / Q` of integer polynomials with `Q 0 = 1`. This is the shape of
`AlgebraicGeometry.Scheme.zetaSeries_rational`. -/
theorem exists_int_normalized_fraction {Z : PowerSeries ℚ}
    (hZ : PowerSeries.map (algebraMap ℚ K) Z = D.zeta)
    (hint : ∃ Z' : PowerSeries ℤ, PowerSeries.map (Int.castRingHom ℚ) Z' = Z) :
    ∃ P Q : Polynomial ℤ, Q.coeff 0 = 1 ∧
      Z * (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (P.map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
  obtain ⟨Z', rfl⟩ := hint
  exact PowerSeries.exists_int_fraction_of_rational Z' (D.exists_rat_normalized_fraction hZ)

end TraceDatum

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory

/-- **Rationality of the zeta series, given a trace datum**: if the point counts of a scheme
`X` of finite type over a finite field `k` are the alternating traces of a trace datum, then
the zeta series of `X` is a fraction of integer polynomials with denominator `Q 0 = 1`. This
is `AlgebraicGeometry.Scheme.zetaSeries_rational` with the cohomological input made explicit;
supplying the trace datum requires a cohomology theory. -/
theorem zetaSeries_rational_of_traceDatum {X : Scheme.{u}} {k : Type u} [Field k] [Finite k]
    (f : X ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f] {K : Type v} [Field K]
    [CharZero K] {r : ℕ} (D : TraceDatum.{v, w} K r) (hN : ∀ n, D.N n = f.pointCount n) :
    ∃ P Q : Polynomial ℤ, Q.coeff 0 = 1 ∧
      f.zetaSeries * (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (P.map (Int.castRingHom ℚ) : PowerSeries ℚ) :=
  D.exists_int_normalized_fraction (D.map_zetaSeries f hN) f.exists_int_zetaSeries

end AlgebraicGeometry.Scheme.Hom

end
