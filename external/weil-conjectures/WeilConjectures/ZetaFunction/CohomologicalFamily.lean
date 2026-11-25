/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TraceSeries
public import WeilConjectures.ZetaFunction.TraceFormula
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# The smooth-proper cohomological family and the trace-to-determinant identity

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over the
finite field `k₀ = 𝔽_q`, and let `ℓ ≠ p` be a prime. The *smooth-proper cohomological family*
consists of the cohomology groups `Vᵢ = Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`, `0 ≤ i ≤ 2d`, of the constant Weil
sheaf, the geometric Frobenius `Fᵢ` on them, and the polynomials

`P_{i,ℓ}(T) = det(1 - T Fᵢ | Vᵢ) ∈ ℚ̄_ℓ[T]`

(`AlgebraicGeometry.Scheme.frobeniusCharpolyRev`). The Grothendieck–Lefschetz trace formula
`N_n = ∑ᵢ (-1)ⁱ Tr(Fᵢⁿ | Vᵢ)` and the log-determinant identity give the factorization

`Z(X₀, T) = ∏ᵢ P_{i,ℓ}(T)^{(-1)^{i+1}}` in `ℚ̄_ℓ⟦T⟧`.

## Coefficients

The cohomology with Frobenius available in this repository is that of Weil sheaves, with
coefficients `ℚ̄_ℓ` (`AlgebraicGeometry.WeilSheaf.cohomology`). The blueprint's `ℚ_ℓ`-family is
recovered from it by the flat base change `Hⁱ(X, ℚ_ℓ) ⊗ ℚ̄_ℓ = Hⁱ(X, ℚ̄_ℓ)`, which does not change
`P_{i,ℓ}`; so everything is stated with the `ℚ̄_ℓ`-family, as for Poincaré duality
(`AlgebraicGeometry.WeilSheaf.poincareDuality`).

## Main definitions

- `AlgebraicGeometry.Scheme.frobeniusCharpolyRev`: the polynomial `P_{i,ℓ}`
  (`prose-19-07`).
- `AlgebraicGeometry.Scheme.IsIntegralFrobeniusFactor`: an integral polynomial realizing
  `P_{i,ℓ}` for every `ℓ ≠ p` (`theorem-weil-conjectures-smooth-proper-schemes--1`).
- `AlgebraicGeometry.Scheme.oddFrobeniusProduct`, `AlgebraicGeometry.Scheme.evenFrobeniusProduct`:
  the parity products `N_ℓ`, `D_ℓ` (`lemma-reciprocal-roots-zeta`).

## Main statements

- `AlgebraicGeometry.Scheme.exists_traceDatum`: the cohomological family is a trace datum whose
  integers are the point counts.
- `AlgebraicGeometry.Scheme.map_zetaSeries_mul_evenFrobeniusProduct`: the trace-to-determinant
  identity (`corollary-point-counting-zeta-function--5`).
- `LinearMap.inv_alternatingCharpolyRevProd_eq_exp` and
  `AlgebraicGeometry.Scheme.trace_determinant`: `lemma-logarithm-determinant--3`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace LinearMap

variable {K : Type*} [Field K] [CharZero K] {W : ℤ → Type*} [∀ i, AddCommGroup (W i)]
  [∀ i, Module K (W i)] [∀ i, FiniteDimensional K (W i)]

/-- The exponential form of the trace-to-determinant identity for a finite graded family
`(W i, u i)`: the inverse of the alternating determinant
`∏ᵢ det (1 - T uᵢ)^{(-1)^i}` is `exp (∑_{n ≥ 1} (∑ᵢ (-1)ⁱ Tr(uᵢⁿ)) Tⁿ / n)`, the exponential of
the alternating trace series. Equivalently, `log Δ` is the alternating trace series, for
`Δ = ∏ᵢ det (1 - T uᵢ)^{(-1)^{i+1}}` (blueprint `lemma-logarithm-determinant--3`). -/
theorem inv_alternatingCharpolyRevProd_eq_exp (s : Finset ℤ) (u : ∀ i, Module.End K (W i)) :
    (alternatingCharpolyRevProd s u 1)⁻¹ =
      (PowerSeries.exp K).subst (alternatingTraceSeries s u) := by
  set T : ℤ → PowerSeries K := fun i ↦
    PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K (W i) (u i ^ n) with hT
  set a : ℕ → K := fun n ↦ ∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace K (W i) (u i ^ n)
    with ha
  have hg : alternatingTraceSeries s u = PowerSeries.mk fun n ↦ if n = 0 then 0 else a n / n := by
    ext n
    rw [coeff_alternatingTraceSeries, PowerSeries.coeff_mk]
  have hsum : ∑ i ∈ s, (i.negOnePow : ℤ) • T i =
      PowerSeries.mk fun n ↦ if n = 0 then 0 else a n := by
    ext n
    rw [map_sum, PowerSeries.coeff_mk]
    split_ifs with hn
    · simp [hT, hn]
    · simp only [hT, PowerSeries.coeff_smul, PowerSeries.coeff_mk, ite_eq_right hn, ha]
  have hP1 (i : ℤ) :
      PowerSeries.constantCoeff (((u i).charpolyRev.comp (Polynomial.X ^ 1) :
        Polynomial K) : PowerSeries K) = 1 := by
    rw [pow_one, Polynomial.comp_X, Polynomial.constantCoeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, eval_charpolyRev]
  have hf : ∀ i ∈ s, PowerSeries.X * PowerSeries.derivative (R := K)
      (if Even i then (((u i).charpolyRev.comp (Polynomial.X ^ 1) : Polynomial K) :
        PowerSeries K)
      else (((u i).charpolyRev.comp (Polynomial.X ^ 1) : Polynomial K) : PowerSeries K)⁻¹) =
      (-((i.negOnePow : ℤ) • T i)) *
      (if Even i then (((u i).charpolyRev.comp (Polynomial.X ^ 1) : Polynomial K) :
        PowerSeries K)
      else (((u i).charpolyRev.comp (Polynomial.X ^ 1) : Polynomial K) : PowerSeries K)⁻¹) := by
    intro i _
    simp only [pow_one, Polynomial.comp_X]
    split_ifs with h
    · rw [Int.negOnePow_even _ h, Units.val_one, one_smul]
      exact X_mul_derivative_charpolyRev (u i)
    · rw [Int.negOnePow_odd _ (Int.not_even_iff_odd.1 h), Units.val_neg, Units.val_one,
        neg_smul, one_smul, neg_neg, inv_charpolyRev_eq_exp]
      exact PowerSeries.X_mul_derivative_exp_subst _
  set A := alternatingCharpolyRevProd s u 1 with hAdef
  have hA : PowerSeries.X * PowerSeries.derivative (R := K) A =
      (-PowerSeries.mk fun n ↦ if n = 0 then 0 else a n) * A := by
    rw [hAdef, alternatingCharpolyRevProd, PowerSeries.X_mul_derivative_prod s hf,
      Finset.sum_neg_distrib, hsum]
  set E := (PowerSeries.exp K).subst (alternatingTraceSeries s u) with hEdef
  have hE : PowerSeries.X * PowerSeries.derivative (R := K) E =
      (PowerSeries.mk fun n ↦ if n = 0 then 0 else a n) * E := by
    rw [hEdef, hg]
    exact PowerSeries.X_mul_derivative_exp_subst a
  have hconstA : PowerSeries.constantCoeff A = 1 := by
    rw [hAdef, alternatingCharpolyRevProd, map_prod]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    split_ifs
    · exact hP1 i
    · rw [PowerSeries.constantCoeff_inv, hP1, inv_one]
  have hconstE : PowerSeries.constantCoeff E = 1 := by
    have hsub : PowerSeries.HasSubst (alternatingTraceSeries s u) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_alternatingTraceSeries s u)
    have h0 : PowerSeries.coeff 0 E = 1 := by
      rw [hEdef, PowerSeries.coeff_subst' (hb := hsub), finsum_eq_single _ 0
        fun d hd ↦ by simp [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, zero_pow hd]]
      simp [PowerSeries.coeff_exp]
    simpa using h0
  have h1 : PowerSeries.X * PowerSeries.derivative (R := K) (A * E) = 0 * (A * E) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    linear_combination A * hE + E * hA
  have h2 : PowerSeries.X * PowerSeries.derivative (R := K) (1 : PowerSeries K) = 0 * 1 := by
    rw [Derivation.map_one_eq_zero, mul_zero, zero_mul]
  have hAE : A * E = 1 := by
    ext n
    exact PowerSeries.coeff_eq_of_X_mul_derivative_eq h1 h2
      (by rw [map_mul, hconstA, hconstE, map_one, mul_one]) (map_zero _) (m := n)
      (fun _ _ ↦ rfl) n le_rfl
  rw [eq_comm, PowerSeries.eq_inv_iff_mul_eq_one (by rw [hconstA]; exact one_ne_zero),
    mul_comm, hAE]

end LinearMap

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace Scheme

section Defs

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `prose-19-07` (and `prose-19-07`): the
determinant factor

`P_{i,ℓ}(T) = det(1 - T Fᵢ | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))`

of the geometric Frobenius `Fᵢ` on the cohomology of the constant Weil sheaf, the reverse
characteristic polynomial `FrobeniusModule.localPolynomial` of the Frobenius module
`Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`. It has constant coefficient `1`, degree `dim Hⁱ` and leading coefficient
`(-1)^{dim Hⁱ} det Fᵢ` (`AlgebraicGeometry.Scheme.coeff_zero_frobeniusCharpolyRev`,
`AlgebraicGeometry.Scheme.natDegree_frobeniusCharpolyRev`,
`AlgebraicGeometry.Scheme.leadingCoeff_frobeniusCharpolyRev`). -/
noncomputable def frobeniusCharpolyRev (i : ℤ) : Polynomial (PadicAlgCl l) :=
  ((WeilSheaf.adicConstant k₀ l X).cohomology i).localPolynomial

theorem frobeniusCharpolyRev_def (i : ℤ) :
    frobeniusCharpolyRev k₀ l X i =
      ((WeilSheaf.adicConstant k₀ l X).cohomology i).localPolynomial :=
  rfl

/-- `P_{i,ℓ}` has constant coefficient `1` (`prose-19-07`). -/
@[simp]
theorem coeff_zero_frobeniusCharpolyRev (i : ℤ) : (frobeniusCharpolyRev k₀ l X i).coeff 0 = 1 :=
  FrobeniusModule.coeff_zero_localPolynomial _

/-- `P_{i,ℓ}` has degree `dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` (`prose-19-07`). -/
theorem natDegree_frobeniusCharpolyRev (i : ℤ) :
    (frobeniusCharpolyRev k₀ l X i).natDegree =
      Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l X).cohomology i).carrier :=
  FrobeniusModule.natDegree_localPolynomial _

/-- `P_{i,ℓ}` has leading coefficient `(-1)^{dim Hⁱ} det Fᵢ`
(`prose-19-07`). -/
theorem leadingCoeff_frobeniusCharpolyRev (i : ℤ) :
    (frobeniusCharpolyRev k₀ l X i).leadingCoeff =
      (-1) ^ Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).carrier *
        LinearMap.det ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd :=
  FrobeniusModule.leadingCoeff_localPolynomial _

/-- Blueprint `lemma-reciprocal-roots-zeta`: the odd parity product
`N_ℓ(T) = ∏_{0 ≤ i ≤ 2d, i odd} P_{i,ℓ}(T)`. -/
noncomputable def oddFrobeniusProduct (d : ℕ) : Polynomial (PadicAlgCl l) :=
  ∏ i ∈ (Finset.range (2 * d + 1)).filter Odd, frobeniusCharpolyRev k₀ l X i

/-- Blueprint `lemma-reciprocal-roots-zeta`: the even parity product
`D_ℓ(T) = ∏_{0 ≤ i ≤ 2d, i even} P_{i,ℓ}(T)`. -/
noncomputable def evenFrobeniusProduct (d : ℕ) : Polynomial (PadicAlgCl l) :=
  ∏ i ∈ (Finset.range (2 * d + 1)).filter Even, frobeniusCharpolyRev k₀ l X i

end Defs

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes--1`: an *integral
realization-independent factor* in degree `i` of a `k₀`-scheme `X₀` is a polynomial `P ∈ ℤ[T]` whose
coefficientwise extension `P^{(ℓ)}` to `ℚ̄_ℓ` is the determinant factor `P_{i,ℓ}` of
`AlgebraicGeometry.Scheme.frobeniusCharpolyRev`, for every prime `ℓ ≠ p`. -/
def IsIntegralFrobeniusFactor (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (i : ℤ) (P : Polynomial ℤ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)],
    P.map (Int.castRingHom (PadicAlgCl l)) = frobeniusCharpolyRev k₀ l X i

section SmoothProper

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]

/-- The smooth-proper cohomological family is a trace datum: the cohomology groups
`Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`, `0 ≤ i ≤ 2d`, with the geometric Frobenius, and the point counts
`N_n = #X₀(𝔽_{qⁿ})`, related by the Grothendieck–Lefschetz trace formula
(`AlgebraicGeometry.WeilSheaf.pointCount_eq_sum_trace_cohomology`). The spaces and the
endomorphisms are the cohomology groups and their Frobenius, on the nose. -/
theorem exists_traceDatum :
    ∃ D : TraceDatum.{0, u + 1} (PadicAlgCl l) (2 * d),
      (∀ i, D.V i = ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier) ∧
      (∀ i, D.P i = frobeniusCharpolyRev k₀ l X (i : ℕ)) ∧
      ∀ n, D.N n = (X ↘ Spec (CommRingCat.of k₀)).pointCount n :=
  ⟨{ V := fun i ↦ ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier
     F := fun i ↦ ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd
     N := fun n ↦ (X ↘ Spec (CommRingCat.of k₀)).pointCount n
     trace_eq := fun n hn ↦ by
       rw [Int.cast_natCast, WeilSheaf.pointCount_eq_sum_trace_cohomology k₀ l X d hn]
       exact (Fin.sum_univ_eq_sum_range (fun i ↦ (-1) ^ i * LinearMap.trace (PadicAlgCl l) _
         (((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^ n)) _).symm },
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Blueprint `corollary-point-counting-zeta-function--5` and
`corollary-point-counting-zeta-function--5` (trace-to-determinant identity): for `X₀` smooth and
proper of pure dimension `d`,

`Z(X₀, T) = ∏_{i = 0}^{2d} P_{i,ℓ}(T)^{(-1)^{i+1}}` in `ℚ̄_ℓ⟦T⟧`,

stated with the denominators cleared:
`Z(X₀, T) · ∏_{i even} P_{i,ℓ}(T) = ∏_{i odd} P_{i,ℓ}(T)`. The right hand side is a quotient of
polynomials with constant coefficient `1`, so the identity holds in `ℚ̄_ℓ(T) ∩ ℚ̄_ℓ⟦T⟧`. -/
theorem map_zetaSeries_mul_evenFrobeniusProduct :
    PowerSeries.map (algebraMap ℚ (PadicAlgCl l)) (X ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        (evenFrobeniusProduct k₀ l X d : PowerSeries (PadicAlgCl l)) =
      (oddFrobeniusProduct k₀ l X d : PowerSeries (PadicAlgCl l)) := by
  obtain ⟨D, -, hP, hN⟩ := exists_traceDatum k₀ l X d
  have h := D.zeta_mul_prod_even_eq_prod_odd
  rw [← D.map_zetaSeries _ hN] at h
  have hpar (p : ℕ → Prop) [DecidablePred p] :
      ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ p i),
          (D.P i : PowerSeries (PadicAlgCl l)) =
        ((∏ i ∈ (Finset.range (2 * d + 1)).filter p, frobeniusCharpolyRev k₀ l X i :
          Polynomial (PadicAlgCl l)) : PowerSeries (PadicAlgCl l)) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, Finset.prod_filter,
      Finset.prod_filter]
    simp only [hP, Polynomial.coeToPowerSeries.ringHom_apply]
    exact Fin.prod_univ_eq_prod_range (fun i ↦ if p i then
      ((frobeniusCharpolyRev k₀ l X i : Polynomial (PadicAlgCl l)) :
        PowerSeries (PadicAlgCl l)) else 1) _
  rw [hpar Even, hpar Odd] at h
  exact h

/-- Blueprint `lemma-logarithm-determinant--3` (trace-to-determinant factorization): for a finite
graded family `(Vᵢ, uᵢ)_{i ∈ I}` of endomorphisms of finite-dimensional vector spaces over a
field `K` of characteristic zero, with `Pᵢ(T) = det(1 - T uᵢ | Vᵢ)` and
`Δ(T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}`,

* `-log Pᵢ(T) = ∑_{n ≥ 1} Tr(uᵢⁿ | Vᵢ) Tⁿ / n` for every `i`
  (`LinearMap.logOf_charpolyRev`);
* `Δ(T) = exp (∑_{n ≥ 1} (∑ᵢ (-1)ⁱ Tr(uᵢⁿ | Vᵢ)) Tⁿ / n)`, i.e. `log Δ` is the alternating
  trace series (`LinearMap.inv_alternatingCharpolyRevProd_eq_exp`; the alternating determinant
  `LinearMap.alternatingCharpolyRevProd` is `Δ⁻¹`);

and, for `X₀` smooth and proper of pure dimension `d` over `k₀`,
`Z(X₀, T) = ∏_{i = 0}^{2d} P_{i,ℓ}(T)^{(-1)^{i+1}}` in `ℚ̄_ℓ⟦T⟧`, with the denominators cleared
(`AlgebraicGeometry.Scheme.map_zetaSeries_mul_evenFrobeniusProduct`). -/
theorem trace_determinant {K : Type*} [Field K] [CharZero K] {W : ℤ → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] [∀ i, FiniteDimensional K (W i)]
    (s : Finset ℤ) (u : ∀ i, Module.End K (W i)) :
    (∀ i, -PowerSeries.logOf ((u i).charpolyRev : PowerSeries K) =
      LinearMap.traceSeries (u i)) ∧
    (LinearMap.alternatingCharpolyRevProd s u 1)⁻¹ =
      (PowerSeries.exp K).subst (LinearMap.alternatingTraceSeries s u) ∧
    PowerSeries.map (algebraMap ℚ (PadicAlgCl l)) (X ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        (evenFrobeniusProduct k₀ l X d : PowerSeries (PadicAlgCl l)) =
      (oddFrobeniusProduct k₀ l X d : PowerSeries (PadicAlgCl l)) :=
  ⟨fun i ↦ by rw [LinearMap.logOf_charpolyRev, neg_neg],
    LinearMap.inv_alternatingCharpolyRevProd_eq_exp s u,
    map_zetaSeries_mul_evenFrobeniusProduct k₀ l X d⟩

end SmoothProper

end Scheme

end AlgebraicGeometry
