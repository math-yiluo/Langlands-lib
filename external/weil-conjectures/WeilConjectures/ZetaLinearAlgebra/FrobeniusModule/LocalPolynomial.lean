/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Basic
public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceSeries

/-!
# The local polynomial determines the traces of the powers of the Frobenius

The determinant-trace identity `T (det (1 - T F))' = -(∑_{n ≥ 1} tr (Fⁿ) Tⁿ) det (1 - T F)`
(`LinearMap.X_mul_derivative_charpolyRev`) recovers the traces `tr (Fⁿ)`, `n ≥ 1`, from the
local polynomial `det (1 - T F)`, which has constant coefficient `1`; its degree is the dimension,
the trace of `F⁰`. Hence two Frobenius modules whose local polynomials have the same images under
ring homomorphisms `φ` and `ψ` into a field have traces of the powers of the Frobenius with the
same images under `φ` and `ψ`.

## Main results

- `LinearMap.map_trace_pow_eq_of_map_charpolyRev_eq`: the statement for endomorphisms, for
  powers `n ≥ 1`.
- `FrobeniusModule.map_trace_frobeniusEnd_pow_eq_of_map_localPolynomial_eq`: the statement for
  Frobenius modules, for all powers.
-/

@[expose] public section

open PowerSeries

namespace LinearMap

variable {K L V : Type*} [Field K] [Field L] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The image under `φ` of the generating series `∑_{n ≥ 1} tr (fⁿ) Xⁿ` of the traces of the
powers of `f` is `-X P'/P` for the image `P` of `det (1 - X f)`. -/
theorem map_mk_trace_pow (f : Module.End K V) (φ : K →+* L) :
    PowerSeries.map φ (PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (f ^ n)) =
      -(X * derivative (R := L) ((f.charpolyRev.map φ : Polynomial L) : L⟦X⟧)) *
        ((f.charpolyRev.map φ : Polynomial L) : L⟦X⟧)⁻¹ := by
  set P : L⟦X⟧ := ((f.charpolyRev.map φ : Polynomial L) : L⟦X⟧)
  have hP : constantCoeff P = 1 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_map, LinearMap.coeff_zero_charpolyRev,
      map_one]
  have h := congrArg (PowerSeries.map φ) (X_mul_derivative_charpolyRev f)
  rw [map_mul, map_mul, map_X, map_derivative, map_neg, ← Polynomial.polynomial_map_coe] at h
  change X * derivative (R := L) P = _ * P at h
  change _ = -(X * derivative (R := L) P) * P⁻¹
  have hPP : P * P⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hP]; exact one_ne_zero)
  rw [h]
  linear_combination (-PowerSeries.map φ (PowerSeries.mk fun n ↦
    if n = 0 then 0 else LinearMap.trace K V (f ^ n))) * hPP

/-- If the images of the local polynomials `det (1 - X g)` and `det (1 - X f)` under `φ` and `ψ`
agree, then so do the images of the traces of the `n`-th powers, `n ≥ 1`. -/
theorem map_trace_pow_eq_of_map_charpolyRev_eq {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W) (φ ψ : K →+* L)
    (h : g.charpolyRev.map φ = f.charpolyRev.map ψ) {n : ℕ} (hn : n ≠ 0) :
    φ (LinearMap.trace K W (g ^ n)) = ψ (LinearMap.trace K V (f ^ n)) := by
  have h' := congrArg (coeff n) ((map_mk_trace_pow g φ).trans
    ((congrArg (fun P : Polynomial L ↦ -(X * derivative (R := L) (P : L⟦X⟧)) *
      (P : L⟦X⟧)⁻¹) h).trans
      (map_mk_trace_pow f ψ).symm))
  simpa [hn] using h'

end LinearMap

namespace FrobeniusModule

universe u v t

variable {K L : Type*} [Field K] [Field L]

/-- Two Frobenius modules whose local polynomials `det (1 - T F)` have the same images under
`φ` and `ψ` have traces of the powers of the Frobenius with the same images under `φ` and `ψ`:
for `n ≥ 1` by the determinant-trace identity, and for `n = 0` because the degree of the local
polynomial is the dimension. -/
theorem map_trace_frobeniusEnd_pow_eq_of_map_localPolynomial_eq (M : FrobeniusModule.{u} K)
    (N : FrobeniusModule.{t} K) (φ ψ : K →+* L)
    (h : N.localPolynomial.map φ = M.localPolynomial.map ψ) (n : ℕ) :
    φ (LinearMap.trace K _ (N.frobeniusEnd ^ n)) =
      ψ (LinearMap.trace K _ (M.frobeniusEnd ^ n)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hd := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map, natDegree_localPolynomial,
      natDegree_localPolynomial] at hd
    simp [LinearMap.trace_one, hd]
  · exact LinearMap.map_trace_pow_eq_of_map_charpolyRev_eq _ _ φ ψ h hn

/-- The zeros of the image under `ι` of the local polynomial `det(1 - T F)` of a module pure of
weight `w` relative to `q` have absolute value `q^{-w/2}`: they are the inverses of the images of
the eigenvalues of `F`. -/
theorem IsPureOfWeight.norm_eq_of_eval_map_localPolynomial_eq_zero [IsAlgClosed K] {ι : K →+* ℂ}
    {q : ℕ} {M : FrobeniusModule.{u} K} {w : ℝ} (h : M.IsPureOfWeight ι q w) {z : ℂ}
    (hz : (M.localPolynomial.map ι).eval z = 0) : ‖z‖ = (q : ℝ) ^ (-(w / 2)) := by
  rw [localPolynomial, LinearMap.charpolyRev_eq_prod_roots,
    Polynomial.map_multiset_prod_one_sub_C_mul_X, Polynomial.eval_multiset_prod,
    Multiset.prod_eq_zero_iff, Multiset.map_map] at hz
  obtain ⟨a, ha, hza⟩ := Multiset.mem_map.1 hz
  simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hza
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
  have hb' : M.frobeniusEnd.HasEigenvalue b := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).1 hb
  have hnorm := h b hb'
  have h1 : ι b * z = 1 := (sub_eq_zero.1 hza).symm
  have h2 : ‖ι b‖ * ‖z‖ = 1 := by rw [← norm_mul, h1, norm_one]
  rw [Real.rpow_neg (Nat.cast_nonneg q), ← hnorm]
  exact eq_inv_of_mul_eq_one_right h2

end FrobeniusModule
