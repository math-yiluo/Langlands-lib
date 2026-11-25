/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Power series supported on the multiples of an integer

The inverse of `1 - X ^ e` is the series `∑ₖ X ^ (e k)`, supported on the multiples of `e`. The
power series whose coefficients vanish outside the multiples of `f` form a submonoid
(`PowerSeries.dvdSupportSubmonoid`), and its elements are invariant under the rescaling
`X ↦ ζ X` by an `f`-th root of unity `ζ`.

## Main statements

- `PowerSeries.inv_one_sub_X_pow_eq_mk`: `(1 - X ^ e)⁻¹ = ∑ₖ X ^ (e k)`.
- `PowerSeries.rescale_eq_self_of_mem_dvdSupportSubmonoid`: a power series supported on the
  multiples of `f` is invariant under `X ↦ ζ X` for `ζ ^ f = 1`.
- `Polynomial.coe_comp_C_mul_X`: the substitution `X ↦ ζ X` in a polynomial is the rescaling of
  the power series.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [Field R]

/-- The geometric series `∑ₖ X ^ (e k)` is the inverse of `1 - X ^ e`. -/
theorem inv_one_sub_X_pow_eq_mk {e : ℕ} (he : e ≠ 0) :
    ((1 : R⟦X⟧) - X ^ e)⁻¹ = mk fun n ↦ if e ∣ n then 1 else 0 := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · ext n
    rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk, coeff_one]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [he]
    rw [ite_eq_right hn.ne']
    by_cases hen : e ≤ n
    · rw [ite_eq_left hen, coeff_mk, sub_eq_zero]
      exact if_congr (Nat.dvd_sub_iff_left hen dvd_rfl).symm rfl rfl
    · rw [ite_eq_right hen, ite_eq_right fun h ↦ hen (Nat.le_of_dvd hn h), sub_zero]
  · simp [he]

/-- The power series whose coefficients vanish outside the multiples of `f`. -/
def dvdSupportSubmonoid (f : ℕ) : Submonoid R⟦X⟧ where
  carrier := {G | ∀ n, ¬ f ∣ n → coeff n G = 0}
  mul_mem' {G H} hG hH n hn := by
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h₁ : f ∣ p.1
    · have h₂ : ¬ f ∣ p.2 := fun h₂ ↦ hn (hp ▸ dvd_add h₁ h₂)
      rw [hH _ h₂, mul_zero]
    · rw [hG _ h₁, zero_mul]
  one_mem' n hn := by
    rw [coeff_one, ite_eq_right]
    rintro rfl
    exact hn (dvd_zero f)

theorem mem_dvdSupportSubmonoid_iff {f : ℕ} {G : R⟦X⟧} :
    G ∈ dvdSupportSubmonoid f ↔ ∀ n, ¬ f ∣ n → coeff n G = 0 :=
  Iff.rfl

theorem inv_one_sub_X_pow_mem_dvdSupportSubmonoid {e f : ℕ} (he : e ≠ 0) (hfe : f ∣ e) :
    ((1 : R⟦X⟧) - X ^ e)⁻¹ ∈ dvdSupportSubmonoid f := by
  intro n hn
  rw [inv_one_sub_X_pow_eq_mk he, coeff_mk, ite_eq_right fun h ↦ hn (hfe.trans h)]

/-- A power series supported on the multiples of `f` is invariant under the rescaling `X ↦ ζ X`
by an `f`-th root of unity `ζ`. -/
theorem rescale_eq_self_of_mem_dvdSupportSubmonoid {f : ℕ} {G : R⟦X⟧}
    (hG : G ∈ dvdSupportSubmonoid f) {ζ : R} (hζ : ζ ^ f = 1) : rescale ζ G = G := by
  ext n
  rw [coeff_rescale]
  by_cases h : f ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [pow_mul, hζ, one_pow, one_mul]
  · rw [hG n h, mul_zero]

end PowerSeries

/-- The substitution `X ↦ ζ X` in a polynomial is the rescaling of the associated power
series. -/
theorem Polynomial.coe_comp_C_mul_X {R : Type*} [CommRing R] (P : Polynomial R) (ζ : R) :
    ((P.comp (C ζ * X) : Polynomial R) : PowerSeries R) = PowerSeries.rescale ζ P := by
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_rescale, Polynomial.coeff_coe,
    Polynomial.comp_C_mul_X_coeff, mul_comm]
