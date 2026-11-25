/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.BlowupChartData
public import WeilConjectures.RingTheory.BlowupChartQuotients
public import WeilConjectures.RingTheory.BlowupChartRegular
public import WeilConjectures.RingTheory.RegularLocalLocalization
public import WeilConjectures.RingTheory.RegularRingOfQuotientAway
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.RingTheory.Polynomial.LocalizationAway
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Regularity of the separating chart of the blow-up

Let `D : BlowupChartData f g h x₀ y₀ c` be the separating chart of the blow-up of a regular local
ring `R`, `Z = Spec (R[T]/(xT - y))[1/f']` with `x = x₀ + c i y₀`, and `h'` the equation of the
strict transform of `H` on `Z`. We show:

* `AlgebraicGeometry.BlowupChartData.isRegularRing_localization`: `Z` is regular;
* `AlgebraicGeometry.BlowupChartData.not_isField_quotient_x`: the exceptional divisor
  `Y = V(x) ⊆ Z` is not a point, if the residue field of `R` is infinite;
* `AlgebraicGeometry.BlowupChartData.isWeaklyRegular`: `(x, h')` is a regular sequence on `Z`.
-/

@[expose] public section

universe u v

open IsLocalRing Polynomial Pointwise

namespace AlgebraicGeometry.BlowupChartData

variable {R : Type u} [CommRing R] {f g h x₀ y₀ : R} {K : Type v} {c : K → R}

/-- The chart `Z = Spec (R[T]/(xT - y))[1/f']` of the blow-up of a regular local ring is regular:
`Z - Y = Spec R[1/(xf)]` is regular and `Y = V(x)` is a regular Cartier divisor. -/
theorem isRegularRing_localization [IsRegularLocalRing R] (D : BlowupChartData f g h x₀ y₀ c) :
    IsRegularRing (Localization.Away D.f') := by
  have := (IsRegularLocalRing.localization_at_prime_and_isRegularRing (maximalIdeal R)).2
  have := D.isLocalization_x
  have := D.isRegularRing_quotient_x
  have : IsRegularRing (Localization.Away
      (algebraMap R (Localization.Away D.f') (x₀ + c D.i * y₀))) :=
    IsRegularRing.of_ringEquiv (IsLocalization.algEquiv
      (Submonoid.powers ((x₀ + c D.i * y₀) * f)) (Localization.Away ((x₀ + c D.i * y₀) * f))
      (Localization.Away (algebraMap R (Localization.Away D.f') (x₀ + c D.i * y₀)))).toRingEquiv
  exact IsRegularRing.of_quotient_of_away D.x_mem_nonZeroDivisors
    (Localization.Away (algebraMap R (Localization.Away D.f') (x₀ + c D.i * y₀)))

variable [IsLocalRing R]

/-- The exceptional divisor `Y = V(x)` of the chart `Z = Spec (R[T]/(xT - y))[1/f']` is not a
point when the residue field of `R` is infinite: `C[1/f']/(x) ≅ κ[T][1/f']`. -/
theorem not_isField_quotient_x [Infinite (ResidueField R)] (D : BlowupChartData f g h x₀ y₀ c)
    (hm : maximalIdeal R = Ideal.span {x₀ + c D.i * y₀, y₀}) :
    ¬ IsField (Localization.Away D.f' ⧸
      Ideal.span {algebraMap R (Localization.Away D.f') (x₀ + c D.i * y₀)}) := fun hF ↦
  Polynomial.not_isField_localization_away _
    (MulEquiv.isField hF (BlowupChart.quotientXEquiv hm D.f').symm.toMulEquiv)

/-- `(x, h')` is a regular sequence on the chart `Z = Spec (R[T]/(xT - y))[1/f']`: `x` is a
non-zero-divisor, and `h'` is nonzero on the integral scheme `Y = V(x)`, since `Y` is not a
point while `X ∩ Y` is. -/
theorem isWeaklyRegular [Infinite (ResidueField R)] (D : BlowupChartData f g h x₀ y₀ c)
    (hm : maximalIdeal R = Ideal.span {x₀ + c D.i * y₀, y₀}) :
    RingTheory.Sequence.IsWeaklyRegular (Localization.Away D.f')
      [algebraMap R (Localization.Away D.f') (x₀ + c D.i * y₀),
        algebraMap (blowupChart (x₀ + c D.i * y₀) y₀) (Localization.Away D.f') D.h'] := by
  have := D.isDomain_quotient_x
  set r := algebraMap R (Localization.Away D.f') (x₀ + c D.i * y₀)
  set s := algebraMap (blowupChart (x₀ + c D.i * y₀) y₀) (Localization.Away D.f') D.h'
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨Module.Flat.isSMulRegular_of_nonZeroDivisors D.x_mem_nonZeroDivisors, ?_⟩
  have hs : Ideal.Quotient.mk (Ideal.span {r}) s ≠ 0 := by
    intro hs
    have hspan : Ideal.span {r, s} = Ideal.span {r} := by
      rw [Ideal.span_insert, sup_eq_left, Ideal.span_singleton_le_iff_mem]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hs
    have hF := D.isField_quotient
    rw [hspan] at hF
    exact D.not_isField_quotient_x hm hF
  have hrs : r • (⊤ : Submodule (Localization.Away D.f') (Localization.Away D.f')) =
      Ideal.span {r} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [(Submodule.quotEquivOfEq _ _ hrs).isSMulRegular_congr,
    ← isSMulRegular_algebraMap_iff (Localization.Away D.f' ⧸ Ideal.span {r})]
  exact (IsRegular.of_ne_zero hs).left

end AlgebraicGeometry.BlowupChartData
