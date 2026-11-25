/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Weil.Definitions

/-!
# Betti symmetry of a Weil factorization

Let `P 0, …, P_{2d} ∈ ℤ[T]` be a family of Weil factors of the zeta function of a smooth
proper geometrically integral scheme of dimension `d` over a finite field with `q` elements,
in the sense of `AlgebraicGeometry.IsWeilFactorization`. The *Betti numbers* of the family are
the degrees `b i = deg (P i)`.

Poincaré duality — in the form of `AlgebraicGeometry.WeilFunctionalEquation`, which matches the
reciprocal roots in degree `i` with those in degree `2 * d - i` — makes the Betti numbers
symmetric.

This file formalises the Betti-number symmetry of the blueprint block on zeta functions and the
Weil conjectures. Three further clauses of that blueprint statement are not restated here:
the endpoint factors `P 0 = 1 - T` and `P (2 * d) = 1 - qᵈ T` are the fields
`AlgebraicGeometry.IsWeilFactorization.apply_zero` and
`AlgebraicGeometry.IsWeilFactorization.apply_last`; the identification `b i = dim H^i (X, ℚ_ℓ)`
needs étale cohomology, which this repository does not have; and the order of the poles of `Z`
at `T = 1` and `T = q⁻ᵈ` needs the order of vanishing of the rational function attached to a
power series, which this repository also does not have.

## Main statements

- `AlgebraicGeometry.WeilFunctionalEquation.natDegree_rev`: Betti symmetry
  `b i = b (2 * d - i)`.

## References

- [J.-P. Serre, *Zeta and L functions*][serre1965]
-/

@[expose] public section

namespace AlgebraicGeometry

/-- Blueprints `theorem-weil-conjectures-smooth-proper-schemes--6` and `definition-reciprocal-root`
(Betti numbers): for a family `P₀, …, P_n` of integral
Frobenius factors, the `i`-th Betti number is `bᵢ = deg Pᵢ` for `0 ≤ i ≤ n`, and `bᵢ = 0` for
`i < 0` or `i > n`. -/
noncomputable def weilBettiNumber {n : ℕ} (P : Fin (n + 1) → Polynomial ℤ) (i : ℤ) : ℕ :=
  if h : 0 ≤ i ∧ i ≤ n then (P ⟨i.toNat, by omega⟩).natDegree else 0

theorem weilBettiNumber_natCast {n : ℕ} (P : Fin (n + 1) → Polynomial ℤ) (i : Fin (n + 1)) :
    weilBettiNumber P (i : ℕ) = (P i).natDegree := by
  rw [weilBettiNumber, dite_eq_left ⟨by omega, by exact_mod_cast i.is_le⟩]
  congr

theorem weilBettiNumber_eq_zero {n : ℕ} (P : Fin (n + 1) → Polynomial ℤ) {i : ℤ}
    (hi : i < 0 ∨ (n : ℤ) < i) : weilBettiNumber P i = 0 := by
  rw [weilBettiNumber, dite_eq_right (by omega)]

/-- Blueprints `corollary-functional-equation--3` and `definition-reciprocal-root` (determinant
constants): the determinant constant
`D = (-1)^b [T^b] P(T)` of an integral Frobenius factor `P` of degree `b`; under
`P^{(ℓ)} = det(1 - T F | V)` its image in `ℚ̄_ℓ` is `det F`. -/
def weilDeterminantConstant (P : Polynomial ℤ) : ℤ :=
  (-1) ^ P.natDegree * P.coeff P.natDegree

/-- Blueprint `corollary-functional-equation--3`: the alternating determinant scalar
`Δ = ∏ᵢ Dᵢ^{(-1)ⁱ} ∈ ℚ` of a family of integral Frobenius factors. The Euler characteristic
`χ = ∑ᵢ (-1)ⁱ bᵢ` of the family is `Polynomial.alternatingNatDegreeSum`. -/
noncomputable def weilDeterminantScalar {n : ℕ} (P : Fin (n + 1) → Polynomial ℤ) : ℚ :=
  ∏ i : Fin (n + 1), (weilDeterminantConstant (P i) : ℚ) ^ ((-1 : ℤ) ^ (i : ℕ))

/-- Blueprint `corollary-functional-equation--3`: the determinant constant of a polynomial with
constant coefficient `1` is a nonzero integer. -/
theorem weilDeterminantConstant_ne_zero {P : Polynomial ℤ} (h0 : P.coeff 0 = 1) :
    weilDeterminantConstant P ≠ 0 := by
  have hP : P ≠ 0 := fun h ↦ by simp [h] at h0
  exact mul_ne_zero (pow_ne_zero _ (by decide)) (Polynomial.leadingCoeff_ne_zero.2 hP)

/-- Blueprint `corollary-functional-equation--3`: the alternating determinant scalar
`Δ = ∏ᵢ Dᵢ^{(-1)ⁱ}` of a family of polynomials with constant coefficients `1` lies in `ℚ^×`. -/
theorem weilDeterminantScalar_ne_zero {n : ℕ} {P : Fin (n + 1) → Polynomial ℤ}
    (h0 : ∀ i, (P i).coeff 0 = 1) : weilDeterminantScalar P ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ ↦
    zpow_ne_zero _ (Int.cast_ne_zero.2 (weilDeterminantConstant_ne_zero (h0 i)))

/-- **Betti symmetry.** The functional equation matches the reciprocal roots in degree `i` with
those in degree `2 * d - i`, so the two root multisets have the same cardinality; over `ℂ` that
cardinality is the degree, so the Betti numbers `b i = deg (P i)` satisfy
`b i = b (2 * d - i)`. -/
theorem WeilFunctionalEquation.natDegree_rev {q d : ℕ} {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hfe : WeilFunctionalEquation q d P) (i : Fin (2 * d + 1)) :
    (P i.rev).natDegree = (P i).natDegree := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hcard : ∀ j : Fin (2 * d + 1),
      Multiset.card ((P j).map (Int.castRingHom ℂ)).roots = (P j).natDegree := fun j ↦ by
    rw [Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _),
      Polynomial.natDegree_map_eq_of_injective hinj]
  rw [← hcard, ← hcard, hfe i, Multiset.card_map]

end AlgebraicGeometry

end
