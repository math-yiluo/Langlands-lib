/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.SmoothProper

/-!
# Integral Frobenius factors

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over
`k₀ = 𝔽_q`. For every `0 ≤ i ≤ 2d` there is a unique polynomial `Pᵢ ∈ ℤ[T]` with `Pᵢ(0) = 1`
whose coefficientwise image in `ℚ̄_ℓ[T]` is the determinant factor
`P_{i,ℓ} = det(1 - T F | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))` for *every* prime `ℓ ≠ p`, and then
`Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}`, a factorization independent of `ℓ` (blueprint
`sk-thm-intfactors`).

Existence is `AlgebraicGeometry.Scheme.exists_isWeilFactorization_of_smoothProper`; uniqueness
holds because `ℤ → ℚ̄_ℓ` is injective.

## Main statements

- `AlgebraicGeometry.Scheme.IsIntegralFrobeniusFactor.unique`: an integral realization of
  `P_{i,ℓ}` is unique.
- `AlgebraicGeometry.Scheme.existsUnique_isIntegralFrobeniusFactor`: existence and uniqueness of
  the integral Frobenius factors.
- `AlgebraicGeometry.Scheme.isWeilFactorization_of_isIntegralFrobeniusFactor`: the integral
  Frobenius factors are a Weil factorization of `Z(X₀, T)`, satisfying the functional equation and
  the Riemann hypothesis.
- `AlgebraicGeometry.Scheme.integral_frobenius_factors`: blueprint `sk-thm-intfactors`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace Scheme

/-- There is a prime `ℓ` different from the characteristic of the finite field `k₀`. -/
theorem exists_prime_ne_ringChar (k₀ : Type u) [Field k₀] :
    ∃ l : ℕ, l.Prime ∧ ringChar k₀ ≠ l := by
  by_cases h : ringChar k₀ = 2
  · exact ⟨3, Nat.prime_three, by omega⟩
  · exact ⟨2, Nat.prime_two, h⟩

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- An integral realization of the determinant factors `P_{i,ℓ}` is unique: its image in
`ℚ̄_ℓ[T]` is prescribed for one prime `ℓ ≠ p`, and `ℤ → ℚ̄_ℓ` is injective (part of
`theorem-weil-conjectures-smooth-proper-schemes--2` and of `lemma-reciprocal-roots-zeta`). -/
theorem IsIntegralFrobeniusFactor.unique [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {i : ℤ} {P P' : Polynomial ℤ}
    (h : IsIntegralFrobeniusFactor k₀ X i P) (h' : IsIntegralFrobeniusFactor k₀ X i P') :
    P = P' := by
  obtain ⟨l, hl, hne⟩ := exists_prime_ne_ringChar k₀
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (ringChar k₀ ≠ l) := ⟨hne⟩
  exact Polynomial.map_injective _ (RingHom.injective_int (Int.castRingHom (PadicAlgCl l)))
    ((h l).trans (h' l).symm)

variable (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- The integral Frobenius factors of `X₀` exist: for every `0 ≤ i ≤ 2d` there is `Pᵢ ∈ ℤ[T]`
with `Pᵢ(0) = 1` and `Pᵢ^{(ℓ)} = P_{i,ℓ}` for every prime `ℓ ≠ p`; they are unique
(`AlgebraicGeometry.Scheme.IsIntegralFrobeniusFactor.unique`). -/
theorem existsUnique_isIntegralFrobeniusFactor {i : ℕ} (hi : i ≤ 2 * d) :
    ∃! P : Polynomial ℤ, P.coeff 0 = 1 ∧ IsIntegralFrobeniusFactor k₀ X i P := by
  obtain ⟨P, hfact, -, -, hP⟩ := exists_isWeilFactorization_of_smoothProper k₀ X d
  exact ⟨P ⟨i, by omega⟩, ⟨hfact.coeff_zero_eq_one _, hP ⟨i, by omega⟩⟩,
    fun P' hP' ↦ hP'.2.unique k₀ X (hP ⟨i, by omega⟩)⟩

/-- The integral Frobenius factors `P₀, …, P_{2d}` of `X₀` are a Weil factorization of
`Z(X₀, T)` satisfying the functional equation and the Riemann hypothesis: they agree with the
factors of `AlgebraicGeometry.Scheme.exists_isWeilFactorization_of_smoothProper`. -/
theorem isWeilFactorization_of_isIntegralFrobeniusFactor {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    IsWeilFactorization (Nat.card k₀) d (X ↘ Spec (CommRingCat.of k₀)).zetaSeries P ∧
      WeilFunctionalEquation (Nat.card k₀) d P ∧ WeilRiemannHypothesis (Nat.card k₀) d P := by
  obtain ⟨P', hfact, hfe, hrh, hP'⟩ := exists_isWeilFactorization_of_smoothProper k₀ X d
  obtain rfl : P = P' := funext fun i ↦ (hP i).unique k₀ X (hP' i)
  exact ⟨hfact, hfe, hrh⟩

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes--3` (integral Frobenius factors): for
`X₀` smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`,

* for every `0 ≤ i ≤ 2d` there is a unique `Pᵢ ∈ ℤ[T]` with `Pᵢ(0) = 1` and
  `Pᵢ^{(ℓ)} = det(1 - T F | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))` for every prime `ℓ ≠ p`;
* for this family, `Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}`, a factorization which does not depend on
  `ℓ`. -/
theorem integral_frobenius_factors :
    (∀ i : ℕ, i ≤ 2 * d →
      ∃! P : Polynomial ℤ, P.coeff 0 = 1 ∧ IsIntegralFrobeniusFactor k₀ X i P) ∧
    ∀ P : Fin (2 * d + 1) → Polynomial ℤ,
      (∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) →
      (X ↘ Spec (CommRingCat.of k₀)).zetaSeries *
          ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
          ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) :=
  ⟨fun _ hi ↦ existsUnique_isIntegralFrobeniusFactor k₀ X d hi,
    fun _ hP ↦ (isWeilFactorization_of_isIntegralFrobeniusFactor k₀ X d hP).1.factorization⟩

end Scheme

end AlgebraicGeometry
