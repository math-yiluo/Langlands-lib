/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceSeries

/-!
# The alternating trace series of the cohomology of a variety

Let `X₀` be a scheme of finite type over the finite field `k₀`, `X = X₀ ⊗ k̄`, and `d ≥ 0`. In
every degree `i` the cohomology `Hⁱ(X, ℚ̄_ℓ)` of the constant Weil sheaf, with its global
geometric Frobenius `F`, is a Frobenius module
(`AlgebraicGeometry.WeilSheaf.cohomology`). The *alternating trace series* of the finite graded
family `(Hⁱ(X, ℚ̄_ℓ), F)_{0 ≤ i ≤ 2d}` is

`str_F(T) = ∑_{n ≥ 1} (∑_{i = 0}^{2d} (-1) ^ i tr (F ^ n ∣ Hⁱ(X, ℚ̄_ℓ))) T ^ n / n`.

In the blueprint `X₀` is smooth, proper and geometrically connected of pure dimension `d`, so
that `I = {0, …, 2d}` contains every degree with nonzero cohomology; the definition itself needs
no such hypothesis.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.adicConstantAlternatingTraceSeries`: the alternating trace
  series `str_F(T)` of the cohomology of `X` in degrees `0, …, 2d`.
- `AlgebraicGeometry.WeilSheaf.coeff_adicConstantAlternatingTraceSeries`: its coefficients
  `(∑_{i = 0}^{2d} (-1) ^ i tr (F ^ n ∣ Hⁱ(X, ℚ̄_ℓ))) / n`.
-/

@[expose] public section

universe u

open PowerSeries

namespace AlgebraicGeometry.WeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The alternating trace series

`str_F(T) = ∑_{n ≥ 1} (∑_{i = 0}^{2d} (-1) ^ i tr (F ^ n ∣ Hⁱ(X ⊗ k̄, ℚ̄_ℓ))) T ^ n / n`

of the finite graded family of Frobenius modules `(Hⁱ(X ⊗ k̄, ℚ̄_ℓ), F)_{0 ≤ i ≤ 2d}`, the
cohomology of the constant Weil sheaf `ℚ̄_ℓ` with its global geometric Frobenius `F`
(blueprint: `theorem-weil-conjectures-smooth-proper-schemes--7`, geometric situation,
`lemma-logarithm-determinant`). -/
noncomputable def adicConstantAlternatingTraceSeries (d : ℕ) : (PadicAlgCl l)⟦X⟧ :=
  FrobeniusModule.alternatingTraceSeries (Finset.Icc 0 (2 * d : ℤ))
    (adicConstant k₀ l X).cohomology

/-- The `n`-th coefficient of the alternating trace series of the cohomology of `X` is
`(∑_{i = 0}^{2d} (-1) ^ i tr (F ^ n ∣ Hⁱ(X ⊗ k̄, ℚ̄_ℓ))) / n`, and `0` for `n = 0`
(blueprint: `theorem-weil-conjectures-smooth-proper-schemes--7`). -/
theorem coeff_adicConstantAlternatingTraceSeries (d n : ℕ) :
    coeff n (adicConstantAlternatingTraceSeries k₀ l X d) =
      if n = 0 then 0
      else (∑ i ∈ Finset.Icc 0 (2 * d : ℤ), (i.negOnePow : ℤ) •
        LinearMap.trace (PadicAlgCl l) ((adicConstant k₀ l X).cohomology i).carrier
          (((adicConstant k₀ l X).cohomology i).frobeniusEnd ^ n)) / n :=
  FrobeniusModule.coeff_alternatingTraceSeries _ _ n

/-- The alternating trace series of the cohomology of `X` is the alternating sum
`∑_{i = 0}^{2d} (-1) ^ i tr_{F ∣ Hⁱ}(T)` of the trace series of the individual cohomology
groups (blueprint: `theorem-weil-conjectures-smooth-proper-schemes--7`). -/
theorem adicConstantAlternatingTraceSeries_eq_sum (d : ℕ) :
    adicConstantAlternatingTraceSeries k₀ l X d =
      ∑ i ∈ Finset.Icc 0 (2 * d : ℤ), (i.negOnePow : ℤ) •
        ((adicConstant k₀ l X).cohomology i).traceSeries :=
  rfl

/-- The alternating trace series of the cohomology of `X` lies in `T ℚ̄_ℓ⟦T⟧`. -/
@[simp]
theorem constantCoeff_adicConstantAlternatingTraceSeries (d : ℕ) :
    constantCoeff (adicConstantAlternatingTraceSeries k₀ l X d) = 0 :=
  FrobeniusModule.constantCoeff_alternatingTraceSeries _ _

end AlgebraicGeometry.WeilSheaf
