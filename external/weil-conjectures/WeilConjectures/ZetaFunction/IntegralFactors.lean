/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Statement
public import WeilConjectures.ZetaFunction.WeilFactorization

/-!
# Uniqueness of the integral Frobenius factors

The second Weil conjecture asserts that the zeta function of a smooth proper geometrically
integral scheme of dimension `d` over a finite field with `q` elements factors as
`Z = ∏ᵢ P i ^ ((-1)^{i+1})` with `P i ∈ ℤ[T]` and `P i (0) = 1`, and that the factors are
unique.

Existence of the factorization is `AlgebraicGeometry.Scheme.weil_conjectures`, and for a pure
trace datum it is `TraceDatum.exists_isWeilFactorization`. What is added here is uniqueness:
under the Riemann hypothesis the reciprocal roots of `P i` have absolute value `q^{i/2}`, these
absolute values are pairwise distinct, and so the weights separate the factors. The general
form of that separation argument, for an arbitrary family of complex polynomials pure of
weights `0, 1, …, r`, is `Polynomial.eq_of_isPureOfWeight_of_prod_mul_eq`.

Uniqueness is what makes the `ℓ`-adic construction of the factors independent of `ℓ`: the
construction produces, for each prime `ℓ ≠ p`, a family satisfying these hypotheses, and any
two such families agree. That reading is a remark, not a statement of this file — nothing here
mentions `ℓ` or the `ℓ`-adic determinants.

This file formalises the uniqueness half of the integral-Frobenius-factors subsection of the
blueprint block on zeta functions and the Weil conjectures.

## Main statements

- `AlgebraicGeometry.IsWeilFactorization.unique`: two Weil factorizations of the same zeta
  function that both satisfy the Riemann hypothesis are equal.
- `AlgebraicGeometry.Scheme.existsUnique_weil_conjectures`: combined with existence, the Weil
  factors of a smooth proper geometrically integral scheme exist and are unique.

## References

- [P. Deligne, *La conjecture de Weil. I*][deligne1974]
- [J.-P. Serre, *Zeta and L functions*][serre1965]
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The Weil conjectures, with uniqueness.** For a smooth proper geometrically integral
scheme of dimension `d` over a finite field, the family of integral Frobenius factors of the
zeta function satisfying the factorization, the functional equation and the Riemann hypothesis
exists and is unique. Existence is `AlgebraicGeometry.Scheme.weil_conjectures` and uniqueness
is `AlgebraicGeometry.IsWeilFactorization.unique`. -/
theorem existsUnique_weil_conjectures (hk : 1 < Nat.card k) (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsProper f] [GeometricallyIntegral f] :
    ∃! P : Fin (2 * d + 1) → Polynomial ℤ,
      IsWeilFactorization (Nat.card k) d f.zetaSeries P ∧
      WeilFunctionalEquation (Nat.card k) d P ∧
      WeilRiemannHypothesis (Nat.card k) d P := by
  obtain ⟨P, hP⟩ := Scheme.weil_conjectures f d
  exact ⟨P, hP, fun P' hP' ↦ (hP'.1.unique hk hP.1 hP'.2.2 hP.2.2)⟩

end Scheme

end AlgebraicGeometry

end
