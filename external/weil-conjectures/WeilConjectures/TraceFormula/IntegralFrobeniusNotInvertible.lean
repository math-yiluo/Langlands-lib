/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Inductions

/-!

# Integral Frobenius correspondences need not be invertible

Let `R` be a commutative ring with an injective algebra map to a field (resp. ring) `K`, and let
`x ∈ R` be a nonzero non-unit. In the application `R = 𝒪_E`, `K = E` and `x = ℓ` (or the
uniformizer `π_E`). This file proves the two elementary facts behind blueprint
`remark-integral-frobenius-correspondences-not-invertible`, which explains why the integral model
`θ` of a rational Frobenius correspondence `ψ_E`
(`ProEtale.CondensedRing.exists_integralModel_frobeniusCorrespondence`)
needs the factor `ℓ^N` and need not be invertible:

* on a point, the automorphism `x⁻¹` of `K` preserves no lattice: a finitely generated
  `R`-submodule `M ⊆ K` with `x⁻¹ M ⊆ M` is zero (`Submodule.eq_bot_of_fg_of_inv_mul_mem`);
* the two eigenvalues `1` and `x` of `diag(1, x)` cannot both become units of `R` after
  multiplication by a single scalar `c ∈ K`
  (`not_exists_algebraMap_units_eq_and_eq_mul`).

## Main statements

- `isUnit_of_isIntegral_inv_algebraMap`: if the inverse of the image of `x ∈ R` is integral over
  `R`, then `x` is a unit.
- `Submodule.eq_bot_of_fg_of_inv_mul_mem`: no nonzero lattice is stable under `x⁻¹`.
- `not_exists_algebraMap_units_eq_and_eq_mul`: no scalar makes `c` and `c x` both units.

-/

@[expose] public section

open Polynomial

variable {R K : Type*} [CommRing R]

section Field

variable [Field K] [Algebra R K] [FaithfulSMul R K]

/-- If `x ∈ R` is nonzero and the inverse of its image in `K` is integral over `R`, then `x` is a
unit of `R`: reversing an integral equation for `x⁻¹` gives `1 + x s = 0` for some `s ∈ R`
(blueprint `remark-integral-frobenius-correspondences-not-invertible`, auxiliary). -/
theorem isUnit_of_isIntegral_inv_algebraMap {x : R} (hx : x ≠ 0)
    (h : IsIntegral R (algebraMap R K x)⁻¹) : IsUnit x := by
  obtain ⟨p, hp, hpy⟩ := h
  have hx' : algebraMap R K x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).2 hx
  let : Invertible (algebraMap R K x)⁻¹ := invertibleOfNonzero (inv_ne_zero hx')
  have h0 : eval₂ (algebraMap R K) (⅟(algebraMap R K x)⁻¹) (reverse p) = 0 :=
    (eval₂_reverse_eq_zero_iff _ _ p).2 hpy
  rw [invOf_eq_inv, inv_inv, eval₂_at_apply] at h0
  have h1 : (reverse p).eval x = 0 :=
    (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).1 h0
  rw [← divX_mul_X_add (reverse p), coeff_zero_reverse, hp.leadingCoeff] at h1
  simp only [eval_add, eval_mul, eval_X, eval_C] at h1
  exact IsUnit.of_mul_eq_one (-(reverse p).divX.eval x) (by linear_combination -h1)

/-- **No lattice is stable under `x⁻¹`** (blueprint
`remark-integral-frobenius-correspondences-not-invertible`: on a point, the automorphism `ℓ⁻¹` of
`E` preserves no lattice). If `x ∈ R` is a nonzero non-unit, then every finitely generated
`R`-submodule `M` of `K` with `x⁻¹ M ⊆ M` is zero. -/
theorem Submodule.eq_bot_of_fg_of_inv_mul_mem {x : R} (hx0 : x ≠ 0) (hx : ¬IsUnit x)
    {M : Submodule R K} (hM : M.FG) (h : ∀ m ∈ M, (algebraMap R K x)⁻¹ * m ∈ M) : M = ⊥ := by
  by_contra hne
  exact hx (isUnit_of_isIntegral_inv_algebraMap hx0
    (isIntegral_of_smul_mem_submodule M hne hM ((algebraMap R K x)⁻¹) h))

end Field

section Ring

variable [CommRing K] [Algebra R K] [FaithfulSMul R K]

/-- If `c` and `c x` are both images of units of `R`, then `x` is a unit of `R` (blueprint
`remark-integral-frobenius-correspondences-not-invertible`, auxiliary). -/
theorem isUnit_of_algebraMap_units_eq_mul {x : R} {c : K} (u v : Rˣ)
    (hu : algebraMap R K u = c) (hv : algebraMap R K v = c * algebraMap R K x) : IsUnit x := by
  have : (v : R) = u * x :=
    FaithfulSMul.algebraMap_injective R K (by rw [map_mul, hu, hv])
  have hx : x = ((u⁻¹ * v : Rˣ) : R) := by simp [this]
  exact hx ▸ Units.isUnit _

/-- **The eigenvalues of `diag(1, x)` cannot both become units** (blueprint
`remark-integral-frobenius-correspondences-not-invertible`: on `E²`, the two eigenvalues of
`diag(1, ℓ)` cannot both become units after multiplying the operator by a single scalar). If
`x ∈ R` is not a unit, there is no `c ∈ K` such that the eigenvalues `c` and `c x` of
`c • diag(1, x)` are both images of units of `R`. -/
theorem not_exists_algebraMap_units_eq_and_eq_mul {x : R} (hx : ¬IsUnit x) :
    ¬∃ c : K, (∃ u : Rˣ, algebraMap R K u = c) ∧
      ∃ v : Rˣ, algebraMap R K v = c * algebraMap R K x := by
  rintro ⟨c, ⟨u, hu⟩, v, hv⟩
  exact hx (isUnit_of_algebraMap_units_eq_mul u v hu hv)

end Ring
