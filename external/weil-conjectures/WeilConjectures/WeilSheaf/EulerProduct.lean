/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Curve
public import WeilConjectures.WeilSheaf.LSeries
public import WeilConjectures.WeilSheaf.StalkTensorTrace

/-!
# The `L`-series of a lisse Weil sheaf on an affine curve

On a smooth geometrically connected affine curve `U₀`, the Grothendieck–Lefschetz trace formula
writes the `L`-series of a lisse Weil sheaf `G` as the ratio
`det(1 - Ft | H_c¹(U, G)) / det(1 - Ft | H_c²(U, G))` of the determinants of the Frobenius on
compactly supported cohomology. For an `ι`-real `G` the local factors of the `L`-series of the
tensor square `G ⊗ G` have nonnegative coefficients.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsReal.hasNonnegCoeffs_lFactor_tensorObj`: the local factors of
  `L(U₀, G ⊗ G, t)` have nonnegative coefficients.
- `AlgebraicGeometry.WeilSheaf.lSeries_mul_localPolynomial_compactlySupportedCohomology_two`: the
  Euler product of the `L`-series, the curve case of the Grothendieck–Lefschetz trace formula,
  deduced from its coefficientwise form
  `AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk_eq`.
-/

@[expose] public section

universe u

open CategoryTheory PowerSeries

open scoped ComplexOrder

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Positivity

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- For an `ι`-real Weil sheaf the images under `ι` of the traces of the powers of the local
Frobenius are real: the local polynomial has real coefficients. -/
theorem IsReal.conj_map_trace_frobeniusEnd_pow {ι : PadicAlgCl l →+* ℂ} {G : WeilSheaf k₀ l X}
    (hreal : G.IsReal ι) (x : X.finitePoints) (k : ℕ) :
    (starRingEnd ℂ) (ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ k))) =
      ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ k)) := by
  refine (FrobeniusModule.map_trace_frobeniusEnd_pow_eq_of_map_localPolynomial_eq (G.stalk x)
    (G.stalk x) ι ((starRingEnd ℂ).comp ι) ?_ k).symm
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_map, RingHom.comp_apply, hreal x n]

/-- **Even tensor powers of a real sheaf are positive**, for tensor squares: if `G` is lisse and
`ι`-real, then every local factor `ι det(1 - Fₓ t^{d(x)} | (G ⊗ G)_x̄)⁻¹` of the `L`-series of
`G ⊗ G` has nonnegative real coefficients (and constant coefficient `1`,
`AlgebraicGeometry.WeilSheaf.constantCoeff_lFactor`). The traces of the powers of the local
Frobenius of `G ⊗ G` are the squares `(ι tr(Gₓᵏ))²` of real numbers, and the logarithmic
derivative of the local factor is their generating series.
(blueprint: `lemma-positivity-euler-factors--1`, the case of tensor squares) -/
theorem IsReal.hasNonnegCoeffs_lFactor_tensorObj {ι : PadicAlgCl l →+* ℂ}
    {G : WeilSheaf k₀ l X} (hG : G.IsLisse) (hreal : G.IsReal ι) (x : X.finitePoints) :
    ((G.tensorObj G hG).lFactor ι x).HasNonnegCoeffs := by
  rw [hasNonnegCoeffs_iff]
  refine coeff_nonneg_of_X_mul_derivative_eq (X_mul_derivative_lFactor ι _ x) (fun n ↦ ?_)
    (by simp [coeff_lFactorLogDeriv]) (by simp [constantCoeff_lFactor])
  rw [coeff_lFactorLogDeriv]
  split_ifs
  · rw [trace_stalk_tensorObj_frobeniusEnd_pow, map_mul]
    set z := ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^
      (n / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1)))
    have hz : z = (z.re : ℂ) := (Complex.conj_eq_iff_re.1 (hreal.conj_map_trace_frobeniusEnd_pow
      x _)).symm
    rw [hz, ← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    exact Complex.zero_le_real.2 (mul_nonneg (Nat.cast_nonneg _) (mul_self_nonneg _))
  · exact le_rfl

end Positivity

section EulerProduct

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [IsAffine U]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))]

open scoped PowerSeries.WithPiTopology in
/-- **Euler product of the `L`-function of a lisse sheaf.** Let `U₀` be a smooth geometrically
connected affine curve and `G` a lisse Weil sheaf on `U₀`. Then, as power series in `t`,

`∏_{x ∈ |U₀|} ι det(1 - Fₓ t^{d(x)} | G_x̄)⁻¹ =
  ι det(1 - F t | H_c¹(U, G)) / ι det(1 - F t | H_c²(U, G))`,

stated as `L(U₀, G, t) · ι det(1 - F t | H_c²(U, G)) = ι det(1 - F t | H_c¹(U, G))`. This is the
graded form of the Grothendieck–Lefschetz trace formula on the curve, `H_c⁰(U, G)` vanishing
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero`).
(blueprint: `theorem-trace-formula-euler-product--4`) -/
theorem lSeries_mul_localPolynomial_compactlySupportedCohomology_two (ι : PadicAlgCl l →+* ℂ)
    (G : WeilSheaf k₀ l U) (hG : G.IsLisse) :
    G.lSeries ι *
        (((G.compactlySupportedCohomology 2).localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧) =
      (((G.compactlySupportedCohomology 1).localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧) := by
  classical
  have : IsSeparated (U ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := inferInstance
  -- the images under `ι` of power series with nonzero constant coefficient commute with `⁻¹`
  have hinv (φ : (PadicAlgCl l)⟦X⟧) (hφ : constantCoeff φ ≠ 0) :
      PowerSeries.map ι φ⁻¹ = (PowerSeries.map ι φ)⁻¹ := by
    have hφ' : constantCoeff (PowerSeries.map ι φ) ≠ 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
      exact (map_ne_zero ι).2 hφ
    rw [PowerSeries.eq_inv_iff_mul_eq_one hφ', ← map_mul, PowerSeries.inv_mul_cancel _ hφ,
      map_one]
  have hP (M : FrobeniusModule.{u + 1, 0} (PadicAlgCl l)) :
      constantCoeff ((M.localPolynomial : Polynomial (PadicAlgCl l)) : (PadicAlgCl l)⟦X⟧) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, FrobeniusModule.localPolynomial,
      LinearMap.coeff_zero_charpolyRev]
    exact one_ne_zero
  set P₁ : (PadicAlgCl l)⟦X⟧ :=
    ((G.compactlySupportedCohomology 1).localPolynomial : (PadicAlgCl l)⟦X⟧)
  set P₂ : (PadicAlgCl l)⟦X⟧ :=
    ((G.compactlySupportedCohomology 2).localPolynomial : (PadicAlgCl l)⟦X⟧)
  -- coefficientwise, `L(U₀, G, t)` is the image of `P₁ / P₂`
  have key : G.lSeries ι = PowerSeries.map ι (P₁ * P₂⁻¹) := by
    ext n
    have hfin := (U ↘ Spec (CommRingCat.of k₀)).finite_setOf_degreeOver_le n
    refine tendsto_nhds_unique (((WithPiTopology.continuous_coeff ℂ n).tendsto _).comp
      (G.hasProd_lFactor ι)) (tendsto_const_nhds.congr' ?_)
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with t ht
    rw [Function.comp_apply, coeff_map, ← coeff_prod_inv_localPolynomial_stalk_eq G hG n t
      fun x hx ↦ ht (hfin.mem_toFinset.2 hx), ← coeff_map, map_prod]
    refine congrArg _ (Finset.prod_congr rfl fun x _ ↦ ?_)
    rw [lFactor, hinv _ (by
        rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
          Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
        simpa [Polynomial.coeff_zero_eq_eval_zero,
          zero_pow ((U ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2)] using hP (G.stalk x)),
      ← Polynomial.polynomial_map_coe, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
  rw [key, Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe, ← map_mul, mul_assoc,
    PowerSeries.inv_mul_cancel _ (hP _), mul_one]

end EulerProduct

end WeilSheaf

end AlgebraicGeometry
