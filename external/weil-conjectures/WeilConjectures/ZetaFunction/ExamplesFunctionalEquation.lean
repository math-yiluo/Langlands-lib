/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.ClassicalFunctionalEquation
public import WeilConjectures.ZetaFunction.Examples

/-!
# The functional equation of the projective line

For `X₀ = ℙ¹` over a finite field `k = 𝔽_q`, the integral Frobenius factors are
`P₀ = 1 - T`, `P₁ = 1`, `P₂ = 1 - qT` (`AlgebraicGeometry.isWeilFactorization_projectiveLine`,
`AlgebraicGeometry.isIntegralFrobeniusFactor_projectiveLine`), so `d = 1`, `b₀ = b₂ = 1`,
`b₁ = 0`, `χ = 2`, `D = D₀ D₂ = 1 · q = q` and `ε = 1`; here `D₀ = det(F₀)` is checked on
`H⁰`, while `D₂ = det(F₂)` is computed from the factor `P₂`. These are the constants of blueprint
`example-functional-equation-projective-line`; the functional equation
`Z(ℙ¹, 1/(qT)) = q T² Z(ℙ¹, T)` itself is `AlgebraicGeometry.projectiveLine_functional_equation`.

## Main statements

- `AlgebraicGeometry.alternatingNatDegreeSum_projectiveLine`: `χ = 2`.
- `AlgebraicGeometry.weilDeterminantConstant_projectiveLine`: `D₀ = D₁ = 1`, `D₂ = q`.
- `AlgebraicGeometry.det_frobeniusEnd_cohomology_zero_projectiveLine`: `det(F₀) = 1`.
- `AlgebraicGeometry.weilDeterminantScalar_projectiveLine`: `D = q`.
- `AlgebraicGeometry.weilSign_projectiveLine`: `ε = 1`.
-/

@[expose] public section

universe u

open Polynomial

namespace AlgebraicGeometry

variable (k : Type u) [Field k] [Finite k]

/-- The Euler characteristic of the projective line: `χ = b₀ - b₁ + b₂ = 1 - 0 + 1 = 2`
(blueprint `example-functional-equation-projective-line`). -/
theorem alternatingNatDegreeSum_projectiveLine :
    alternatingNatDegreeSum ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] = 2 := by
  obtain ⟨-, h0, h1, h2⟩ := isWeilFactorization_projectiveLine k
  simp only [weilBettiNumber] at h0 h1 h2
  rw [alternatingNatDegreeSum, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  simp_all

/-- The determinant constants `Dᵢ = (-1)^{bᵢ} [T^{bᵢ}] Pᵢ` of the integral Frobenius factors
`P₀ = 1 - T`, `P₁ = 1`, `P₂ = 1 - qT` of the projective line are `D₀ = 1`, `D₁ = 1`, `D₂ = q`
(blueprint `example-functional-equation-projective-line`). -/
theorem weilDeterminantConstant_projectiveLine :
    weilDeterminantConstant (1 - X : ℤ[X]) = 1 ∧ weilDeterminantConstant (1 : ℤ[X]) = 1 ∧
      weilDeterminantConstant (1 - C (Nat.card k : ℤ) * X) = Nat.card k := by
  have hq : (Nat.card k : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hd0 : (1 - X : ℤ[X]).natDegree = 1 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by simp), natDegree_X]
  have hd2 : (1 - C (Nat.card k : ℤ) * X).natDegree = 1 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by
      rw [natDegree_one, natDegree_C_mul_X _ hq]; norm_num), natDegree_C_mul_X _ hq]
  refine ⟨by simp [weilDeterminantConstant, hd0, coeff_one],
    by simp [weilDeterminantConstant], ?_⟩
  rw [weilDeterminantConstant, hd2]
  simp [coeff_one]

/-- The determinant of geometric Frobenius on `H⁰(ℙ¹ ⊗ k̄, ℚ̄_ℓ)` is `det(F₀) = 1`, the
determinant constant `D₀` of `P₀ = 1 - T`: Frobenius acts on `H⁰` of the geometrically
connected `ℙ¹` as the identity (blueprint `example-functional-equation-projective-line`). -/
theorem det_frobeniusEnd_cohomology_zero_projectiveLine (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k ≠ l)] :
    LinearMap.det ((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology
        0).frobeniusEnd = 1 := by
  rw [FrobeniusModule.frobeniusEnd, WeilSheaf.frobenius_cohomology_zero_adicConstant,
    LinearEquiv.refl_toLinearMap, LinearMap.det_id]

/-- The determinant scalar of the projective line:
`D = ∏ᵢ Dᵢ^{(-1)ⁱ} = 1 · 1⁻¹ · q = q` (blueprint `example-functional-equation-projective-line`). -/
theorem weilDeterminantScalar_projectiveLine :
    weilDeterminantScalar ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] = Nat.card k := by
  obtain ⟨hD0, hD1, hD2⟩ := weilDeterminantConstant_projectiveLine k
  have e0 : (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] : Fin 3 → ℤ[X]) 0 = 1 - X := rfl
  have e1 : (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] : Fin 3 → ℤ[X]) 1 = 1 := rfl
  have e2 : (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] : Fin 3 → ℤ[X]) 2 =
      1 - C (Nat.card k : ℤ) * X := rfl
  rw [weilDeterminantScalar, Fin.prod_univ_three, e0, e1, e2, hD0, hD1, hD2]
  norm_num

/-- The sign of the functional equation of the projective line: with `d = 1`, `χ = 2` and
`m = d χ / 2 = 1`, `ε = (-1)^χ q^{-m} D = q⁻¹ q = 1`
(blueprint `example-functional-equation-projective-line`). -/
theorem weilSign_projectiveLine :
    weilSign (Nat.card k) 1 ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] = 1 := by
  have hq : (Nat.card k : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hD := weilDeterminantScalar_projectiveLine k
  rw [weilDeterminantScalar] at hD
  simp only [weilDeterminantConstant, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] at hD
  rw [weilSign, alternatingNatDegreeSum_projectiveLine]
  simp only [leadingCoeff]
  rw [hD, zpow_neg_one]
  simp [hq]

end AlgebraicGeometry
