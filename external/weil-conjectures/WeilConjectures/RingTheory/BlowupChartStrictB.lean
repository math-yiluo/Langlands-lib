/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.BlowupChartExpansion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.RingTheory.BlowupChartLocalization
public import WeilConjectures.RingTheory.BlowupChartAlgClosed
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# The strict transform of a curve on a blow-up chart

Let `R` be a local ring, `B = V(g)` with `A = R/(g)`, and `x, y ∈ R`. The strict transform of `B`
on the chart `T = y/x` of the blow-up is `Spec A'` for the subalgebra `A' = A[ȳ/x̄]` of `A[1/x]`
(`BlowupChart.strictTransform`). If `g = ∑_{j ≤ e} q_j x ^ (e - j) y ^ j` with `q_e` a unit (the
line `x = 0` is not tangent to `B`), then `ȳ/x̄` is integral over `A`, so `A'` is finite over `A`,
`A'[1/x] = A[1/x]`, and all closed points of `A'` lie over the closed point of `Spec R`.
If moreover the residue field is algebraically closed and `p, q` have no common root modulo `𝔪`,
then `p(ȳ/x̄)` is a unit of `A'`: the strict transforms of `V(g)` and of the curve with
dehomogenized equation `p` do not meet.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

namespace BlowupChart

variable {R : Type u} [CommRing R] (g x y : R)

/-- The slope `ȳ/x̄ ∈ (R/(g))[1/x]`. -/
noncomputable def slope : Localization.Away (Ideal.Quotient.mk (Ideal.span {g}) x) :=
  algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {g}) y) *
    IsLocalization.Away.invSelf (Ideal.Quotient.mk (Ideal.span {g}) x)

/-- `x̄ (ȳ/x̄) = ȳ`. -/
theorem algebraMap_mul_slope :
    algebraMap (R ⧸ Ideal.span {g}) (Localization.Away (Ideal.Quotient.mk (Ideal.span {g}) x))
      (Ideal.Quotient.mk (Ideal.span {g}) x) * slope g x y =
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {g}) y) := by
  rw [slope, mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]

/-- The coordinate ring `A' = A[ȳ/x̄] ⊆ A[1/x]` of the strict transform of `V(g)` on the chart
`T = y/x`. -/
noncomputable def strictTransform :
    Subalgebra (R ⧸ Ideal.span {g}) (Localization.Away (Ideal.Quotient.mk (Ideal.span {g}) x)) :=
  Algebra.adjoin _ {slope g x y}

/-- The slope as an element of `A'`. -/
noncomputable def slope' : strictTransform g x y :=
  ⟨slope g x y, Algebra.subset_adjoin rfl⟩

/-- The map `R → A'`. -/
noncomputable def toStrict : R →+* strictTransform g x y :=
  (algebraMap (R ⧸ Ideal.span {g}) (strictTransform g x y)).comp (Ideal.Quotient.mk _)

/-- `x T = y` in `A'`. -/
theorem toStrict_mul_slope' : toStrict g x y x * slope' g x y = toStrict g x y y :=
  Subtype.ext (algebraMap_mul_slope g x y)

/-- The composition `R → A' → A[1/x]`. -/
theorem val_comp_toStrict :
    (strictTransform g x y).val.toRingHom.comp (toStrict g x y) =
      (algebraMap (R ⧸ Ideal.span {g}) _).comp (Ideal.Quotient.mk _) := rfl

/-- The map from the chart `C = R[T]/(xT - y)` to `A'`, `T ↦ ȳ/x̄`. -/
noncomputable def chartToStrict :
    R[X] ⧸ Ideal.span {C x * X - C y} →+* strictTransform g x y :=
  Ideal.Quotient.lift _ (eval₂RingHom (toStrict g x y) (slope' g x y)) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_C,
      toStrict_mul_slope', sub_self, mul_zero]

/-- The map `C → A'` on classes of polynomials. -/
theorem chartToStrict_mk (p : R[X]) :
    chartToStrict g x y (Ideal.Quotient.mk _ p) = p.eval₂ (toStrict g x y) (slope' g x y) := rfl


/-- The map `C → A'` restricts to `R → A'`. -/
theorem chartToStrict_algebraMap (r : R) :
    chartToStrict g x y (algebraMap R _ r) = toStrict g x y r := eval₂_C _ _

variable {g x y} {e : ℕ} {q : R[X]}

/-- If `g = ∑_{j ≤ e} q_j x ^ (e - j) y ^ j`, then `q(ȳ/x̄) = 0` in `A[1/x]`. -/
theorem eval₂_slope_eq_zero (hq : q.natDegree ≤ e)
    (hg : g = ∑ j ∈ Finset.range (e + 1), q.coeff j * x ^ (e - j) * y ^ j) :
    q.eval₂ ((algebraMap (R ⧸ Ideal.span {g}) _).comp (Ideal.Quotient.mk _)) (slope g x y) = 0 := by
  set φ := (algebraMap (R ⧸ Ideal.span {g})
    (Localization.Away (Ideal.Quotient.mk (Ideal.span {g}) x))).comp (Ideal.Quotient.mk _)
  have h := RingHom.map_sum_eq_pow_mul_eval₂ φ (algebraMap_mul_slope g x y).symm q hq
  rw [← hg] at h
  have hφg : φ g = 0 := by
    simp [φ, Ideal.Quotient.mk_singleton_self]
  rw [hφg, eq_comm] at h
  have hx : IsUnit (φ x) :=
    IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk (Ideal.span {g}) x)
  exact (hx.pow e).mul_right_eq_zero.mp h

/-- If `g = ∑_{j ≤ e} q_j x ^ (e - j) y ^ j`, then `q(T) = 0` in `A'`. -/
theorem eval₂_slope'_eq_zero (hq : q.natDegree ≤ e)
    (hg : g = ∑ j ∈ Finset.range (e + 1), q.coeff j * x ^ (e - j) * y ^ j) :
    q.eval₂ (toStrict g x y) (slope' g x y) = 0 := by
  apply Subtype.val_injective
  have := Polynomial.hom_eval₂ q (toStrict g x y)
    (strictTransform g x y).val.toRingHom (slope' g x y)
  rw [val_comp_toStrict] at this
  exact this.trans (eval₂_slope_eq_zero hq hg)

/-- If `g = ∑_{j ≤ e} q_j x ^ (e - j) y ^ j` with `q_e` a unit, the slope `ȳ/x̄` is integral over
`A = R/(g)`. -/
theorem isIntegral_slope (hq : q.natDegree ≤ e)
    (hg : g = ∑ j ∈ Finset.range (e + 1), q.coeff j * x ^ (e - j) * y ^ j)
    (hu : IsUnit (q.coeff e)) : IsIntegral (R ⧸ Ideal.span {g}) (slope g x y) := by
  refine ⟨(C (↑hu.unit⁻¹ : R) * q).map (Ideal.Quotient.mk _), ?_, ?_⟩
  · refine monic_of_natDegree_le_of_coeff_eq_one e
      (natDegree_map_le.trans (natDegree_C_mul_le _ _ |>.trans hq)) ?_
    rw [coeff_map, coeff_C_mul, hu.val_inv_mul, map_one]
  · rw [eval₂_map, eval₂_mul, eval₂_C, eval₂_slope_eq_zero hq hg, mul_zero]

/-- If `g = ∑_{j ≤ e} q_j x ^ (e - j) y ^ j` with `q_e` a unit, then `A'` is a finite
`R/(g)`-module. -/
theorem finite_strictTransform (hq : q.natDegree ≤ e)
    (hg : g = ∑ j ∈ Finset.range (e + 1), q.coeff j * x ^ (e - j) * y ^ j)
    (hu : IsUnit (q.coeff e)) :
    Module.Finite (R ⧸ Ideal.span {g}) (strictTransform g x y) :=
  .of_fg (isIntegral_slope hq hg hu).fg_adjoin_singleton

/-- `A'[1/x] = A[1/x]`: the strict transform of `B` minus the exceptional divisor is `B - t`. -/
theorem isLocalization_strictTransform :
    IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {g}) x)
      (Localization.Away (algebraMap (R ⧸ Ideal.span {g}) (strictTransform g x y)
        (Ideal.Quotient.mk _ x))) :=
  isLocalization_away_of_subalgebra _ (strictTransform g x y) _

variable [IsLocalRing R]

/-- If `A'` is finite over `R/(g)`, every maximal ideal of `A'` contains the image of `𝔪`. -/
theorem toStrict_mem_of_isMaximal [Module.Finite (R ⧸ Ideal.span {g}) (strictTransform g x y)]
    (N : Ideal (strictTransform g x y)) [N.IsMaximal] {r : R} (hr : r ∈ maximalIdeal R) :
    toStrict g x y r ∈ N := by
  have h1 := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R ⧸ Ideal.span {g}) N
  have h2 : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {g}))
      (N.comap (algebraMap (R ⧸ Ideal.span {g}) (strictTransform g x y)))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have h3 := IsLocalRing.eq_maximalIdeal h2
  rw [← h3] at hr
  exact hr

/-- If `A'` is finite over `R/(g)`, then `x` lies in the Jacobson radical of `A'`: the closed
points of the strict transform lie on the exceptional divisor. -/
theorem mem_jacobson_strictTransform
    [Module.Finite (R ⧸ Ideal.span {g}) (strictTransform g x y)] (hx : x ∈ maximalIdeal R) :
    algebraMap (R ⧸ Ideal.span {g}) (strictTransform g x y) (Ideal.Quotient.mk _ x) ∈
      Ideal.jacobson (⊥ : Ideal (strictTransform g x y)) :=
  Ideal.mem_sInf.mpr fun N ⟨_, _⟩ => toStrict_mem_of_isMaximal N hx

/-- **The strict transforms are disjoint.** Let `g = ∑_{j ≤ e} q_j x ^ (e - j) y ^ j` with `q_e`
a unit, and let `p` be a polynomial such that `p` and `q` have no common root modulo `𝔪`. If the
residue field is algebraically closed, then `p(ȳ/x̄)` is a unit of `A'`. -/
theorem isUnit_eval₂_slope' [IsAlgClosed (ResidueField R)] (hq : q.natDegree ≤ e)
    (hg : g = ∑ j ∈ Finset.range (e + 1), q.coeff j * x ^ (e - j) * y ^ j)
    (hu : IsUnit (q.coeff e)) (p : R[X])
    (hpq : ∀ τ : R, p.eval τ ∈ maximalIdeal R → q.eval τ ∈ maximalIdeal R → False) :
    IsUnit (p.eval₂ (toStrict g x y) (slope' g x y)) := by
  have := finite_strictTransform hq hg hu
  by_contra hnu
  obtain ⟨N, hN, hpN⟩ := Ideal.exists_le_maximal
    (Ideal.span {p.eval₂ (toStrict g x y) (slope' g x y)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  rw [Ideal.span_le, Set.singleton_subset_iff] at hpN
  let F := strictTransform g x y ⧸ N
  let : Field F := Ideal.Quotient.field N
  let ι : R →+* F := (Ideal.Quotient.mk N).comp (toStrict g x y)
  have hι : ∀ r ∈ maximalIdeal R, ι r = 0 := fun r hr =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (toStrict_mem_of_isMaximal N hr)
  have hmon : (C (↑hu.unit⁻¹ : R) * q).Monic := by
    refine monic_of_natDegree_le_of_coeff_eq_one e (natDegree_C_mul_le _ _ |>.trans hq) ?_
    rw [coeff_C_mul, hu.val_inv_mul]
  have hev : ∀ s : R[X], s.eval₂ ι (Ideal.Quotient.mk N (slope' g x y)) =
      Ideal.Quotient.mk N (s.eval₂ (toStrict g x y) (slope' g x y)) := fun s =>
    (Polynomial.hom_eval₂ s _ _ _).symm
  obtain ⟨τ, hτ⟩ := exists_eq_of_monic_eval₂_eq_zero ι hι hmon (t := Ideal.Quotient.mk N
    (slope' g x y)) (by rw [hev, eval₂_mul, eval₂_C, eval₂_slope'_eq_zero hq hg, mul_zero,
      map_zero])
  have hmem : ∀ s : R[X], Ideal.Quotient.mk N (s.eval₂ (toStrict g x y) (slope' g x y)) = 0 →
      s.eval τ ∈ maximalIdeal R := by
    intro s hs
    by_contra hns
    have h1 : ι (s.eval τ) = 0 := by rw [← eval₂_at_apply, hτ, hev, hs]
    exact ((((mem_maximalIdeal _).not.mp hns) |> not_not.mp).map ι).ne_zero h1
  refine hpq τ (hmem p (Ideal.Quotient.eq_zero_iff_mem.mpr hpN)) (hmem q ?_)
  rw [eval₂_slope'_eq_zero hq hg, map_zero]

end BlowupChart
