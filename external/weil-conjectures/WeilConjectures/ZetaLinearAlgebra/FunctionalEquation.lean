/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.Pairing
public import WeilConjectures.ZetaLinearAlgebra.WeilFactorization

/-!
# The functional equation for a self-dual trace datum

Let `D` be a trace datum of length `2 * d` over a field `K` of characteristic zero and let
`ι : K →+* ℂ` be a ring embedding. Assume that `D` is *self-dual*: for each `i` there is a
perfect pairing `p i` between `D.V i` and `D.V (2 * d - i)` on which the Frobenius
endomorphisms act by the similitude factor `qᵈ`, that is
`p i (D.F i v) (D.F i.rev w) = qᵈ * p i v w`. This is the linear algebra shadow of Poincaré
duality.

Under this hypothesis the complex roots of `D.P (2 * d - i)` are the images of the roots of
`D.P i` under `z ↦ (qᵈ z)⁻¹`, by the similitude theory of
`WeilConjectures.ZetaLinearAlgebra.Pairing`. Transporting this along the identification of the
integer polynomials produced by `TraceDatum.exists_isWeilFactorization` gives
`AlgebraicGeometry.WeilFunctionalEquation` for that family.

The last theorem of this file is the endpoint of the zeta linear algebra chapter: a trace datum
that is integral, pure, normalized and self-dual yields integer polynomials satisfying all three
of the Weil conjectures for its counting series — the factorisation, the functional equation and
the Riemann hypothesis.

This does *not* close the `sorry` in `WeilConjectures.Statement`: that theorem is about a smooth
proper scheme over a finite field, and producing a trace datum from such a scheme needs an actual
Weil cohomology theory, which this chapter does not build.

## Main results

- `TraceDatum.roots_map_charpolyRev_rev`: the complex roots of `D.P i.rev` are the images of the
  complex roots of `D.P i` under `z ↦ (qᵈ z)⁻¹`.
- `TraceDatum.weilFunctionalEquation_of_pairing`: any family of integer polynomials whose complex
  images are the `ι (D.P i)` satisfies the Weil functional equation.
- `TraceDatum.exists_isWeilFactorization_and_functionalEquation_and_riemannHypothesis`: an
  integral, pure, normalized and self-dual trace datum yields integer polynomials satisfying all
  three Weil conjectures for its counting series.
-/

@[expose] public section

universe u v

namespace TraceDatum

section FunctionalEquation

variable {K : Type u} [Field K] [CharZero K] {q d : ℕ} (D : TraceDatum.{u, v} K (2 * d))
  {p : ∀ i : Fin (2 * d + 1), D.V i →ₗ[K] D.V i.rev →ₗ[K] K}

/-- **The reciprocal root identity for a self-dual trace datum.** If Frobenius acts on a perfect
pairing between `D.V i` and `D.V (2 * d - i)` by the similitude factor `qᵈ`, then the complex
roots of the reciprocal characteristic polynomial in degree `2 * d - i` are the images of those
in degree `i` under `z ↦ (qᵈ z)⁻¹`. -/
theorem roots_map_charpolyRev_rev (hq : 1 < q) (ι : K →+* ℂ)
    (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    (i : Fin (2 * d + 1)) :
    ((D.P i.rev).map ι).roots = (((D.P i).map ι).roots.map fun z ↦ ((q : ℂ) ^ d * z)⁻¹) := by
  have := hp i
  have hc : (q : K) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have h := LinearMap.roots_map_charpolyRev_of_similitude hc (hFG i) ι
  simpa only [P_def, map_pow, map_natCast] using h

/-- **The Weil functional equation for a self-dual trace datum.** Any family of integer
polynomials whose images in `ℂ[X]` are the complexified reciprocal characteristic polynomials of
a self-dual trace datum satisfies `AlgebraicGeometry.WeilFunctionalEquation`. -/
theorem weilFunctionalEquation_of_pairing (hq : 1 < q) (ι : K →+* ℂ)
    (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i, (P i).map (Int.castRingHom ℂ) = (D.P i).map ι) :
    AlgebraicGeometry.WeilFunctionalEquation q d P := fun i ↦ by
  rw [hP i.rev, hP i]
  exact D.roots_map_charpolyRev_rev hq ι hp hFG i

/-- **The Weil conjectures for a trace datum.** A trace datum of length `2 * d` whose counting
series has integer coefficients, whose reciprocal characteristic polynomials are universally pure
of the expected weights and normalized in the extreme degrees, and which is self-dual for the
similitude factor `qᵈ`, yields a family of integer polynomials whose images in `ℂ[X]` are the
`ι (D.P i)` and which satisfies the Weil factorisation, the Weil functional equation and the
Riemann hypothesis. -/
theorem exists_isWeilFactorization_and_functionalEquation_and_riemannHypothesis (hq : 1 < q)
    (ι : K →+* ℂ) (hpure : ∀ i, ((D.P i).map ι).IsUniversallyPureOfWeight q i.1)
    (hzero : (D.P 0).map ι = 1 - Polynomial.X)
    (hlast : (D.P (Fin.last (2 * d))).map ι = 1 - Polynomial.C ((q : ℂ) ^ d) * Polynomial.X)
    (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    {Z : PowerSeries ℚ} (hZ : PowerSeries.map (algebraMap ℚ K) Z = D.zeta)
    (hint : ∃ Z' : PowerSeries ℤ, PowerSeries.map (Int.castRingHom ℚ) Z' = Z) :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      AlgebraicGeometry.IsWeilFactorization q d Z P ∧
      AlgebraicGeometry.WeilFunctionalEquation q d P ∧
      AlgebraicGeometry.WeilRiemannHypothesis q d P ∧
      ∀ i, (P i).map (Int.castRingHom ℂ) = (D.P i).map ι := by
  obtain ⟨P, hfact, hrh, hP⟩ := D.exists_isWeilFactorization hq ι hpure hzero hlast hZ hint
  exact ⟨P, hfact, D.weilFunctionalEquation_of_pairing hq ι hp hFG hP, hrh, hP⟩

end FunctionalEquation

end TraceDatum

end
