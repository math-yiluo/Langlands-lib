/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.DetTrace
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Trace series of Frobenius modules

Let `(V, F)` be a Frobenius module over a field `K`: a finite-dimensional `K`-vector space
with an automorphism `F`. Its *trace series* and its *determinant* are

`tr_F(T) = ∑_{n ≥ 1} tr (F ^ n ∣ V) T ^ n / n ∈ T K⟦T⟧`,  `P_{(V, F)}(T) = det (1 - T F ∣ V)`.

The determinant is `FrobeniusModule.localPolynomial`; it has constant coefficient `1` and
degree `dim V`, its leading coefficient `(-1) ^ dim V det F` being nonzero. For a finite graded
family `(V_i, F_i)_{i ∈ I}`, `I ⊆ ℤ` finite, the *alternating trace series* is

`str_F(T) = ∑_{n ≥ 1} (∑_{i ∈ I} (-1) ^ i tr (F_i ^ n ∣ V_i)) T ^ n / n
  = ∑_{i ∈ I} (-1) ^ i tr_{F_i}(T)`.

No semisimplicity of the Frobenius is assumed. In the geometric situation of the blueprint the
family is the cohomology `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf on a smooth proper
`k₀`-scheme `X` of pure dimension `d`, with its global geometric Frobenius
(`AlgebraicGeometry.WeilSheaf.cohomology (AlgebraicGeometry.WeilSheaf.adicConstant k₀ l X)`), and
`I = {0, …, 2d}`, i.e. `s = Finset.Icc 0 (2 * d)`.

## Main declarations

- `FrobeniusModule.traceSeries`: the trace series of a Frobenius module.
- `FrobeniusModule.alternatingTraceSeries`: the alternating trace series of a finite graded
  family of Frobenius modules.
- `FrobeniusModule.coeff_alternatingTraceSeries`: its coefficients
  `(∑_i (-1) ^ i tr (F_i ^ n)) / n`.
- `FrobeniusModule.coeff_zero_localPolynomial`, `FrobeniusModule.natDegree_localPolynomial` and
  `FrobeniusModule.leadingCoeff_localPolynomial`: `det (1 - T F)` has constant coefficient `1`,
  degree `dim V` and leading coefficient `(-1) ^ dim V det F ≠ 0`.
-/

@[expose] public section

universe u v

open PowerSeries

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The *trace series* `tr_F(T) = ∑_{n ≥ 1} tr (F ^ n ∣ V) T ^ n / n` of a Frobenius module
`(V, F)` (blueprint: `theorem-weil-conjectures-smooth-proper-schemes--7`,
`lemma-logarithm-determinant`). -/
noncomputable def traceSeries (M : FrobeniusModule.{u, v} K) : K⟦X⟧ :=
  M.frobeniusEnd.traceSeries

/-- The `n`-th coefficient of the trace series of a Frobenius module is `tr (F ^ n) / n`, and
`0` for `n = 0`. -/
theorem coeff_traceSeries (M : FrobeniusModule.{u, v} K) (n : ℕ) :
    coeff n M.traceSeries =
      if n = 0 then 0 else LinearMap.trace K M.carrier (M.frobeniusEnd ^ n) / n :=
  LinearMap.coeff_traceSeries _ n

/-- The trace series of a Frobenius module lies in `T K⟦T⟧`. -/
@[simp]
theorem constantCoeff_traceSeries (M : FrobeniusModule.{u, v} K) :
    constantCoeff M.traceSeries = 0 :=
  LinearMap.constantCoeff_traceSeries _

/-- The determinant `det (1 - T F ∣ V)` of a Frobenius module has constant coefficient `1`
(blueprint: `theorem-weil-conjectures-smooth-proper-schemes--7`). -/
@[simp]
theorem coeff_zero_localPolynomial (M : FrobeniusModule.{u, v} K) :
    M.localPolynomial.coeff 0 = 1 :=
  LinearMap.coeff_zero_charpolyRev _

/-- The determinant `det (1 - T F ∣ V)` of a Frobenius module has degree `dim V`, since its
Frobenius is invertible (blueprint: `theorem-weil-conjectures-smooth-proper-schemes--7`). -/
theorem natDegree_localPolynomial (M : FrobeniusModule.{u, v} K) :
    M.localPolynomial.natDegree = Module.finrank K M.carrier :=
  LinearMap.natDegree_charpolyRev (LinearEquiv.isUnit_det' M.frobenius)

/-- The leading coefficient of the determinant `det (1 - T F ∣ V)` of a Frobenius module is
`(-1) ^ dim V * det F` (blueprint: `theorem-weil-conjectures-smooth-proper-schemes--7`). -/
theorem leadingCoeff_localPolynomial (M : FrobeniusModule.{u, v} K) :
    M.localPolynomial.leadingCoeff =
      (-1) ^ Module.finrank K M.carrier * LinearMap.det M.frobeniusEnd :=
  LinearMap.leadingCoeff_charpolyRev (LinearEquiv.isUnit_det' M.frobenius)

/-- The leading coefficient `(-1) ^ dim V * det F` of `det (1 - T F ∣ V)` is nonzero. -/
theorem leadingCoeff_localPolynomial_ne_zero (M : FrobeniusModule.{u, v} K) :
    M.localPolynomial.leadingCoeff ≠ 0 := by
  rw [leadingCoeff_localPolynomial]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (LinearEquiv.isUnit_det' M.frobenius).ne_zero


/-- The *alternating trace series*

`str_F(T) = ∑_{n ≥ 1} (∑_{i ∈ s} (-1) ^ i tr (F_i ^ n ∣ V_i)) T ^ n / n`

of a finite graded family `(V_i, F_i)_{i ∈ s}` of Frobenius modules, indexed by a finite set
`s` of integers. For the cohomology `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` of a smooth proper `k₀`-scheme of pure
dimension `d` with its global geometric Frobenius, and `s = {0, …, 2d}`, this is the alternating
trace series of the blueprint (blueprint: `theorem-weil-conjectures-smooth-proper-schemes--7`,
`lemma-logarithm-determinant`). -/
noncomputable def alternatingTraceSeries (s : Finset ℤ) (M : ℤ → FrobeniusModule.{u, v} K) :
    K⟦X⟧ :=
  LinearMap.alternatingTraceSeries s fun i ↦ (M i).frobeniusEnd

/-- The alternating trace series is the alternating sum `∑_{i ∈ s} (-1) ^ i tr_{F_i}(T)` of the
trace series. -/
theorem alternatingTraceSeries_eq_sum (s : Finset ℤ) (M : ℤ → FrobeniusModule.{u, v} K) :
    alternatingTraceSeries s M = ∑ i ∈ s, (i.negOnePow : ℤ) • (M i).traceSeries :=
  rfl


/-- The `n`-th coefficient of the alternating trace series is
`(∑_{i ∈ s} (-1) ^ i tr (F_i ^ n ∣ V_i)) / n`, and `0` for `n = 0` (blueprint:
`theorem-weil-conjectures-smooth-proper-schemes--7`). -/
theorem coeff_alternatingTraceSeries (s : Finset ℤ) (M : ℤ → FrobeniusModule.{u, v} K)
    (n : ℕ) :
    coeff n (alternatingTraceSeries s M) =
      if n = 0 then 0
      else (∑ i ∈ s, (i.negOnePow : ℤ) •
        LinearMap.trace K (M i).carrier ((M i).frobeniusEnd ^ n)) / n :=
  LinearMap.coeff_alternatingTraceSeries s _ n

/-- The alternating trace series lies in `T K⟦T⟧`. -/
@[simp]
theorem constantCoeff_alternatingTraceSeries (s : Finset ℤ)
    (M : ℤ → FrobeniusModule.{u, v} K) :
    constantCoeff (alternatingTraceSeries s M) = 0 :=
  LinearMap.constantCoeff_alternatingTraceSeries s _

end FrobeniusModule
