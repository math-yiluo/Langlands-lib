/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.EulerProduct

@[expose] public section

/-!
# Integrality of the zeta series of a scheme over a finite field

The zeta series `Z(X, t)` of a scheme `X` of finite type over a finite field is defined as
an exponential in `ℚ⟦t⟧`, but it has integer coefficients. This is the arithmetic input of
the rationality statement `AlgebraicGeometry.Scheme.zetaSeries_rational`, which asks for a
quotient of *integral* polynomials.

The reason is the Euler product expansion
`AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod`: each factor `(1 - t ^ deg x)⁻¹` is a
geometric series with coefficients `0` and `1`, the series in the range of
`PowerSeries.map (Int.castRingHom ℚ)` form a subring, and every coefficient of the infinite
product already appears in a finite subproduct.

## Main statements

- `PowerSeries.inv_one_sub_X_pow_mem_range_map`: the geometric series `(1 - X ^ d)⁻¹` in
  `ℚ⟦X⟧` is the image of a power series over `ℤ`.
- `AlgebraicGeometry.Scheme.Hom.coeff_zetaSeries_mem_range`: every coefficient of the zeta
  series is an integer.
- `AlgebraicGeometry.Scheme.Hom.exists_int_zetaSeries`: the zeta series is the image of a
  power series over `ℤ` under `PowerSeries.map (Int.castRingHom ℚ)`.
- `AlgebraicGeometry.Scheme.Hom.constantCoeff_of_map_eq_zetaSeries`: any such integral lift
  has constant coefficient `1`.
-/

universe u

open CategoryTheory

namespace PowerSeries

/-- The geometric series `(1 - X ^ d)⁻¹ ∈ ℚ⟦X⟧` is the image of a power series over `ℤ`. -/
theorem inv_one_sub_X_pow_mem_range_map {d : ℕ} (hd : d ≠ 0) :
    ((1 - X ^ d)⁻¹ : ℚ⟦X⟧) ∈
      (PowerSeries.map (Int.castRingHom ℚ)).range := by
  classical
  refine ⟨mk fun n ↦ if d ∣ n then 1 else 0, ?_⟩
  rw [inv_one_sub_X_pow_eq_mk hd]
  ext n
  rw [coeff_map, coeff_mk, coeff_mk]
  split <;> simp

end PowerSeries

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k] [Finite k] (f : X ⟶ Spec (.of k))
  [QuasiCompact f] [LocallyOfFiniteType f]

open scoped PowerSeries.WithPiTopology in
/-- Every coefficient of the zeta series of a scheme of finite type over a finite field is
an integer. -/
theorem Hom.coeff_zetaSeries_mem_range (n : ℕ) :
    PowerSeries.coeff n f.zetaSeries ∈ (Int.castRingHom ℚ).range := by
  classical
  have hd : ∀ x : X.finitePoints, f.degreeOver x.1 ≠ 0 := fun x ↦ f.degreeOver_ne_zero x.2
  have hfin : ∀ n, {x : X.finitePoints | f.degreeOver x.1 ≤ n}.Finite :=
    f.finite_setOf_degreeOver_le
  set T : Finset X.finitePoints := (hfin n).toFinset with hT_def
  have hT : ∀ x : X.finitePoints, f.degreeOver x.1 ≤ n → x ∈ T := fun x hx ↦ by
    simpa [hT_def] using hx
  rw [f.zetaSeries_eq_tprod, PowerSeries.coeff_tprod_inv_one_sub_X_pow hd hfin n hT]
  obtain ⟨Z, hZ⟩ := Subring.prod_mem _ fun x (_ : x ∈ T) ↦
    PowerSeries.inv_one_sub_X_pow_mem_range_map (hd x)
  exact ⟨PowerSeries.coeff n Z, by rw [← hZ, PowerSeries.coeff_map]⟩

/-- **The zeta series has integer coefficients**: the zeta series of a scheme of finite
type over a finite field is the image of a power series over `ℤ`. -/
theorem Hom.exists_int_zetaSeries :
    ∃ Z : PowerSeries ℤ, PowerSeries.map (Int.castRingHom ℚ) Z = f.zetaSeries := by
  have h : ∀ n, ∃ m : ℤ, (m : ℚ) = PowerSeries.coeff n f.zetaSeries := fun n ↦ by
    obtain ⟨m, hm⟩ := f.coeff_zetaSeries_mem_range n
    exact ⟨m, by simpa using hm⟩
  choose m hm using h
  refine ⟨PowerSeries.mk m, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  simpa using hm n

omit [Finite k] [QuasiCompact f] [LocallyOfFiniteType f] in
/-- Any integral lift of the zeta series has constant coefficient `1`. -/
theorem Hom.constantCoeff_of_map_eq_zetaSeries {Z : PowerSeries ℤ}
    (hZ : PowerSeries.map (Int.castRingHom ℚ) Z = f.zetaSeries) :
    PowerSeries.constantCoeff Z = 1 := by
  have h : ((PowerSeries.constantCoeff Z : ℤ) : ℚ) = 1 := by
    have hc := congrArg (PowerSeries.coeff 0) hZ
    rw [PowerSeries.coeff_map] at hc
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, f.constantCoeff_zetaSeries] using hc
  exact_mod_cast h

end AlgebraicGeometry.Scheme
