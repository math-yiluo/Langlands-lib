/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FunctionalEquation

/-!
# Deligne purity for a self-dual trace datum

Deligne's weight estimate bounds the reciprocal roots of the reciprocal characteristic
polynomial in degree `i` from above by `q ^ (i / 2)`; in the language of
`WeilConjectures.ZetaLinearAlgebra.Weights` it says that `D.P i` is
`Polynomial.IsMixedOfWeightLE q i`. Poincaré duality upgrades the estimate to purity: if a
trace datum of length `2 * d` is self-dual for the similitude factor `qᵈ` — the linear algebra
shadow of Poincaré duality used in `WeilConjectures.ZetaLinearAlgebra.FunctionalEquation` —
then the upper bound in degree `2 * d - i` is a lower bound in degree `i`, and the two bounds
meet.

Since this repository has no étale cohomology yet, the cohomological family `(V i, F i, P i)`
of the blueprint is modelled by a `TraceDatum`, its reciprocal characteristic polynomials
`TraceDatum.P` and a perfect pairing with similitude factor `qᵈ`. The sheaf-theoretic clauses
of the blueprint weight input — purity of the constant Weil sheaf, mixedness of compactly
supported cohomology and the comparison with ordinary cohomology — belong to the six-functor
and weight blocks and enter here as the hypothesis `hmixed`.

This file formalises the two statements of the smooth-proper purity subsection and of the
absolute case of the weight-input subsection of the blueprint block on zeta functions and the
Weil conjectures.

## Main statements

- `TraceDatum.isPureOfWeight_map_P_of_pairing`: a self-dual trace datum whose reciprocal
  characteristic polynomials are mixed of weight at most `i` in degree `i` is pure of weight
  `i` in degree `i`.
- `TraceDatum.norm_eq_of_mem_roots_charpoly_map` and
  `TraceDatum.norm_eq_of_mem_roots_charpoly_map_of_pairing`: purity in degree `i` says that
  every complex eigenvalue of the `i`-th endomorphism has absolute value `q ^ (i / 2)`.

## References

- [P. Deligne, *La conjecture de Weil. I*][deligne1974]
- [P. Deligne, *La conjecture de Weil. II*][deligne1980]
-/

@[expose] public section

universe u v

namespace TraceDatum

variable {K : Type u} [Field K] [CharZero K] {q d : ℕ} (D : TraceDatum.{u, v} K (2 * d))
  {p : ∀ i : Fin (2 * d + 1), D.V i →ₗ[K] D.V i.rev →ₗ[K] K}

/-- **Smooth-proper purity.** Duality supplies the lower bound missing from Deligne's estimate.
If the reciprocal characteristic polynomials of a trace datum of length `2 * d` are mixed of
weight at most `i` in degree `i`, and Frobenius acts on a perfect pairing between `D.V i` and
`D.V (2 * d - i)` by the similitude factor `qᵈ`, then the estimate in degree `2 * d - i` bounds
the reciprocal roots in degree `i` from above by `q ^ (i / 2)`, so `D.P i` is pure of
weight `i`. -/
theorem isPureOfWeight_map_P_of_pairing (hq : 1 < q) (ι : K →+* ℂ)
    (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    (hmixed : ∀ i : Fin (2 * d + 1), ((D.P i).map ι).IsMixedOfWeightLE q i.1)
    (i : Fin (2 * d + 1)) :
    ((D.P i).map ι).IsPureOfWeight q i.1 := by
  refine Polynomial.isPureOfWeight_iff.2 ⟨hmixed i, fun z hz ↦ ?_⟩
  have ha1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have ha0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one ha1
  have ht0 : 0 < ‖z‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos ha0 _) ((hmixed i).2 z hz)
  have hzrev : ((q : ℂ) ^ d * z)⁻¹ ∈ ((D.P i.rev).map ι).roots := by
    rw [D.roots_map_charpolyRev_rev hq ι hp hFG i]
    exact Multiset.mem_map_of_mem _ hz
  have hge := (hmixed i.rev).2 _ hzrev
  have hrev : ((i.rev : ℕ) : ℝ) = 2 * (d : ℝ) - (i : ℕ) := by
    have hle : (i : ℕ) ≤ 2 * d := by omega
    have hv : (i.rev : ℕ) = 2 * d - (i : ℕ) := by simp [Fin.val_rev]
    rw [hv, Nat.cast_sub hle]
    push_cast
    ring
  have hnorm : ‖((q : ℂ) ^ d * z)⁻¹‖ = ((q : ℝ) ^ (d : ℝ) * ‖z‖)⁻¹ := by
    rw [norm_inv, norm_mul, norm_pow, Complex.norm_natCast, Real.rpow_natCast]
  rw [hnorm, hrev] at hge
  have hpos : 0 < (q : ℝ) ^ (d : ℝ) * ‖z‖ := mul_pos (Real.rpow_pos_of_pos ha0 _) ht0
  have h1 := mul_le_mul_of_nonneg_right hge hpos.le
  rw [inv_mul_cancel₀ hpos.ne', ← mul_assoc, ← Real.rpow_add ha0,
    show -(2 * (d : ℝ) - (i : ℕ)) / 2 + (d : ℝ) = ((i : ℕ) : ℝ) / 2 by ring] at h1
  have hp2 : (0 : ℝ) < (q : ℝ) ^ (((i : ℕ) : ℝ) / 2) := Real.rpow_pos_of_pos ha0 _
  calc ‖z‖ = ((q : ℝ) ^ (((i : ℕ) : ℝ) / 2) * ‖z‖) / (q : ℝ) ^ (((i : ℕ) : ℝ) / 2) := by
        field_simp
    _ ≤ 1 / (q : ℝ) ^ (((i : ℕ) : ℝ) / 2) := by gcongr
    _ = (q : ℝ) ^ (-((i : ℕ) : ℝ) / 2) := by
        rw [show (-((i : ℕ) : ℝ) / 2) = -(((i : ℕ) : ℝ) / 2) by ring, Real.rpow_neg ha0.le,
          one_div]

omit [CharZero K] in
/-- **The weight estimate in eigenvalue form.** If the reciprocal characteristic polynomial in
degree `i` is pure of weight `i` and the `i`-th endomorphism is invertible, then every complex
eigenvalue of that endomorphism — every root of the complexified characteristic polynomial —
has absolute value `q ^ (i / 2)`. The eigenvalues are taken in `ℂ` rather than in `K`, which is
not assumed algebraically closed. -/
theorem norm_eq_of_mem_roots_charpoly_map (ι : K →+* ℂ) {i : Fin (2 * d + 1)}
    (hdet : IsUnit (LinearMap.det (D.F i))) (hpure : ((D.P i).map ι).IsPureOfWeight q i.1)
    {z : ℂ} (hz : z ∈ ((D.F i).charpoly.map ι).roots) :
    ‖z‖ = (q : ℝ) ^ (((i : ℕ) : ℝ) / 2) := by
  have hι : Function.Injective ι := ι.injective
  have hcoeff : (D.F i).charpoly.coeff 0 ≠ 0 := by
    intro h
    rw [LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero] at hdet
    exact not_isUnit_zero hdet
  have hcoeff' : ((D.F i).charpoly.map ι).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_map]
    exact fun h ↦ hcoeff (hι (by simpa using h))
  have hrev : (D.P i).map ι = ((D.F i).charpoly.map ι).reverse := by
    rw [P_def, LinearMap.charpolyRev_def, Polynomial.reverse_map hι]
  have hzinv : z⁻¹ ∈ ((D.P i).map ι).roots := by
    rw [hrev, Polynomial.roots_reverse_of_monic ((LinearMap.charpoly_monic _).map ι)
      (IsAlgClosed.splits _) hcoeff']
    exact Multiset.mem_map_of_mem _ hz
  have hnorm := hpure.2 _ hzinv
  rw [norm_inv, inv_eq_iff_eq_inv] at hnorm
  rw [hnorm, show (-((i : ℕ) : ℝ) / 2) = -(((i : ℕ) : ℝ) / 2) by ring,
    Real.rpow_neg (by positivity), inv_inv]

/-- **The weight estimate in eigenvalue form, for a self-dual trace datum.** Under Deligne's
upper bound and the duality of `TraceDatum.isPureOfWeight_map_P_of_pairing`, every complex
eigenvalue of the `i`-th endomorphism of a self-dual trace datum has absolute
value `q ^ (i / 2)`. -/
theorem norm_eq_of_mem_roots_charpoly_map_of_pairing (hq : 1 < q) (ι : K →+* ℂ)
    (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    (hmixed : ∀ i : Fin (2 * d + 1), ((D.P i).map ι).IsMixedOfWeightLE q i.1)
    (i : Fin (2 * d + 1)) {z : ℂ} (hz : z ∈ ((D.F i).charpoly.map ι).roots) :
    ‖z‖ = (q : ℝ) ^ (((i : ℕ) : ℝ) / 2) :=
  have := hp i
  D.norm_eq_of_mem_roots_charpoly_map ι
    (LinearMap.isUnit_det_of_similitude (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))) (hFG i))
    (D.isPureOfWeight_map_P_of_pairing hq ι hp hFG hmixed i) hz

end TraceDatum

end
