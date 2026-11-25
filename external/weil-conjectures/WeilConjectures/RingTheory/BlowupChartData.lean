/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TangentConeInitialForms
import WeilConjectures.RingTheory.BlowupChartTangent
import WeilConjectures.RingTheory.BlowupChartQuotients
import WeilConjectures.RingTheory.BlowupChartStrictB
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A chart of the blow-up of a regular local surface separating two curves

Let `R` be a henselian regular local ring of dimension `2` with algebraically closed residue field
`κ`, and let `D = V(f)`, `B = V(g)` be curves and `H = V(h)` a regular curve through the closed
point `t` such that the tangent cones satisfy `C_t D ∩ C_t B = {0}` and `C_t D ∩ T_t H = {0}`.
Blowing up `t` separates `D` from `B` and from `H` (blueprint
`lemma-vanishing-restrictions-after-blowing-up--1`,
`lemma-vanishing-restrictions-after-blowing-up--1`). After a generic choice of the regular system of
parameters `(x, y)`, all the points of the exceptional divisor that matter lie on the single affine
chart `R[T]/(xT - y)` of the blow-up (`blowupChart x y`). This file records what is used of this
chart, `AlgebraicGeometry.BlowupChartData`; with `f = x^d f'`, `h = x h'` on the chart,
`Z = Spec (R[T]/(xT - y))[1/f']` is the open part of the chart off the strict transform `D'`,
`Y = V(x) ⊆ Z` is the exceptional divisor and `X = V(h') ⊆ Z` the strict transform of `H`:

* `Z - Y = Spec R[1/(xf)]` and `Z - (X ∪ Y) = Spec R[1/(xfh)]`;
* `Y` and `X` are regular divisors, `Y` is connected and `X ∩ Y` is a reduced point;
* the strict transform of `B` is `Spec A'` for a finite `R/(g)`-algebra `A'`, all of whose closed
  points lie on `Y`, with `A'[1/x] = (R/g)[1/x]`;
* `B ∩ V(x) = {t}`.

## Main definitions

- `AlgebraicGeometry.BlowupChartData f g h x₀ y₀ c`: the chart data, for the parameters
  `x = x₀ + c i y₀`
  and `y = y₀`, `i` an index of the family of constants `c`.

## Main results

- `AlgebraicGeometry.nonempty_blowupChartData`: the chart data exist.
-/

@[expose] public section

universe u v

open IsLocalRing Polynomial

namespace AlgebraicGeometry

section Data

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The data of a chart `R[T]/(xT - y)` of the blow-up of `Spec R` at its closed point which
separates the strict transforms of the curves `D = V(f)` and `B = V(g)` and meets the strict
transform of the regular curve `H = V(h)` transversally away from `D` (blueprint
`lemma-vanishing-restrictions-after-blowing-up--1` and
`lemma-vanishing-restrictions-after-blowing-up--1`, in the chart containing all the relevant points
of the exceptional divisor). The regular system of parameters is `x = x₀ + c i y₀`, `y = y₀` for an
index `i` of the family of constants `c`. -/
structure BlowupChartData (f g h x₀ y₀ : R) {K : Type v} (c : K → R) where
  /-- the index of the constant in `x = x₀ + c i y₀` -/
  i : K
  /-- the order of `f` -/
  d : ℕ
  /-- the strict transform equation of `D` on the chart: `f = x^d f'` -/
  f' : blowupChart (x₀ + c i * y₀) y₀
  /-- the strict transform equation of `H` on the chart: `h = x h'` -/
  h' : blowupChart (x₀ + c i * y₀) y₀
  algebraMap_f : algebraMap R (blowupChart (x₀ + c i * y₀) y₀) f =
    algebraMap R _ (x₀ + c i * y₀) ^ d * f'
  algebraMap_h : algebraMap R (blowupChart (x₀ + c i * y₀) y₀) h =
    algebraMap R _ (x₀ + c i * y₀) * h'
  /-- `Z - Y = Spec R[1/(xf)]`: inverting `x` on `Z = Spec (R[T]/(xT - y))[1/f']` is inverting
  `xf` on `R`. -/
  isLocalization_x : IsLocalization.Away ((x₀ + c i * y₀) * f)
    (Localization.Away (algebraMap R (Localization.Away f') (x₀ + c i * y₀)))
  /-- `Z - (X ∪ Y) = Spec R[1/(xfh)]`. -/
  isLocalization_xh : IsLocalization.Away ((x₀ + c i * y₀) * f * h)
    (Localization.Away (algebraMap R (Localization.Away f') (x₀ + c i * y₀) *
      algebraMap _ (Localization.Away f') h'))
  /-- `x` is a non-zero-divisor on `Z`, so `Y = V(x)` is an effective Cartier divisor. -/
  x_mem_nonZeroDivisors : algebraMap R (Localization.Away f') (x₀ + c i * y₀) ∈
    nonZeroDivisors (Localization.Away f')
  /-- `h'` is a non-zero-divisor on `Z`, so `X = V(h')` is an effective Cartier divisor. -/
  h'_mem_nonZeroDivisors : algebraMap _ (Localization.Away f') h' ∈
    nonZeroDivisors (Localization.Away f')
  /-- `Y = V(x)` is integral (in particular connected). -/
  isDomain_quotient_x : IsDomain (Localization.Away f' ⧸
    Ideal.span {algebraMap R (Localization.Away f') (x₀ + c i * y₀)})
  /-- `Y = V(x)` is regular. -/
  isRegularRing_quotient_x : IsRegularRing (Localization.Away f' ⧸
    Ideal.span {algebraMap R (Localization.Away f') (x₀ + c i * y₀)})
  /-- `X = V(h')` is regular. -/
  isRegularRing_quotient_h' : IsRegularRing (Localization.Away f' ⧸
    Ideal.span {algebraMap _ (Localization.Away f') h'})
  /-- `X ∩ Y` is a reduced point. -/
  isField_quotient : IsField (Localization.Away f' ⧸
    Ideal.span {algebraMap R (Localization.Away f') (x₀ + c i * y₀),
      algebraMap _ (Localization.Away f') h'})
  /-- `B ∩ V(x) = {t}`. -/
  maximalIdeal_le_radical : maximalIdeal R ≤ (Ideal.span {x₀ + c i * y₀, g}).radical
  /-- the coordinate ring of the strict transform `B'` of `B` on the chart -/
  A' : Type u
  [commRing : CommRing A']
  [algebra : Algebra (R ⧸ Ideal.span {g}) A']
  [finite : Module.Finite (R ⧸ Ideal.span {g}) A']
  /-- `B' ⊆ Z`: the strict transform of `B` misses `D'`. -/
  toA' : Localization.Away f' →+* A'
  toA'_algebraMap (r : R) : toA' (algebraMap R _ r) =
    algebraMap (R ⧸ Ideal.span {g}) A' (Ideal.Quotient.mk _ r)
  /-- `B' - V(x) = B - t`. -/
  isLocalization_A' : IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {g}) (x₀ + c i * y₀))
    (Localization.Away (algebraMap (R ⧸ Ideal.span {g}) A'
      (Ideal.Quotient.mk _ (x₀ + c i * y₀))))
  /-- the closed points of `B'` lie on `Y = V(x)` -/
  mem_jacobson : algebraMap (R ⧸ Ideal.span {g}) A' (Ideal.Quotient.mk _ (x₀ + c i * y₀)) ∈
    Ideal.jacobson (⊥ : Ideal A')

attribute [instance] BlowupChartData.commRing BlowupChartData.algebra BlowupChartData.finite

end Data

variable {R : Type u} [CommRing R]

/-- The order of an element at the closed point is unique. -/
theorem _root_.IsLocalRing.HasOrder.unique {R : Type u} [CommRing R] [IsLocalRing R] {f : R}
    {d d' : ℕ} (h : HasOrder f d) (h' : HasOrder f d') : d = d' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h.2 (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hlt) h'.1)
  · exact h'.2 (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hlt) h.1)

/-- **The separating chart of the blow-up exists** (blueprint
`lemma-vanishing-restrictions-after-blowing-up--1` and
`lemma-vanishing-restrictions-after-blowing-up--1`, in a chart). Let `R` be a henselian regular
local ring of dimension `2` with algebraically closed residue field, `(x₀, y₀)` a regular system of
parameters, and `c` an infinite family of elements of `R` with distinct residues. Let `f, g` and `h`
be such that `h ∈ 𝔪 ∖ 𝔪²` and the tangent cones satisfy `C_t V(f) ∩ C_t V(g) = {0}` and
`C_t V(f) ∩ T_t V(h) = {0}`. Then for some index `i`, the chart `R[T]/(xT - y)` of the blow-up for
`x = x₀ + c i y₀`, `y = y₀` carries the data `BlowupChartData`. -/
theorem nonempty_blowupChartData [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]
    {x₀ y₀ : R} (hm : maximalIdeal R = Ideal.span {x₀, y₀}) {K : Type v} [Infinite K]
    (c : K → R) (hc : Function.Injective (residue R ∘ c)) {f g h : R}
    (hDB : InitialFormsSpanHighDegree f g) (hDH : InitialFormsSpanHighDegree f h)
    (hh : HasOrder h 1) :
    Nonempty (BlowupChartData f g h x₀ y₀ c) := by
  classical
  obtain ⟨d, e, hfd, hge, hT⟩ := hDB
  obtain ⟨d', e', hfd', hhe', hT'⟩ := hDH
  obtain rfl := hfd.unique hfd'
  obtain rfl := hhe'.unique hh
  have hx₀ : x₀ ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have hy₀ : y₀ ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  -- the generic direction
  have hm₀ : maximalIdeal R = Ideal.span {y₀, x₀} := by rw [hm, Set.pair_comm]
  obtain ⟨pg, hpg, hgexp⟩ := Ideal.exists_eq_sum_of_mem_span_pair_pow (hm₀ ▸ hge.1)
  obtain ⟨ph, hph, hhexp⟩ := Ideal.exists_eq_sum_of_mem_span_pair_pow (hm₀ ▸ hh.1)
  have hpg0 := map_residue_ne_zero_of_not_mem_pow hy₀ hx₀ hgexp hge.2
  have hph0 := map_residue_ne_zero_of_not_mem_pow hy₀ hx₀ hhexp hh.2
  obtain ⟨i, hi⟩ := BlowupChart.exists_eval_neg_residue_ne_zero hc (mul_ne_zero hpg0 hph0)
  rw [eval_mul] at hi
  have hgdir := BlowupChart.not_mem_span_sup_pow_of_eval_ne_zero hdim hm hpg hgexp (c i)
    (left_ne_zero_of_mul hi)
  have hhdir := BlowupChart.not_mem_span_sup_pow_of_eval_ne_zero hdim hm hph hhexp (c i)
    (right_ne_zero_of_mul hi)
  -- the chart
  set x := x₀ + c i * y₀ with hxdef
  have hmx : maximalIdeal R = Ideal.span {x, y₀} := by
    rw [hm, BlowupChart.span_pair_add_mul]
  have hx : x ∈ maximalIdeal R := hmx ▸ Ideal.subset_span (by simp)
  obtain ⟨p, hp, hfexp⟩ := Ideal.exists_eq_sum_of_mem_span_pair_pow (hmx ▸ hfd.1)
  obtain ⟨q, hq, hgexp'⟩ := Ideal.exists_eq_sum_of_mem_span_pair_pow (hmx ▸ hge.1)
  obtain ⟨r, hr, hhexp'⟩ := Ideal.exists_eq_sum_of_mem_span_pair_pow (hmx ▸ hh.1)
  have hqu := isUnit_coeff_of_not_mem_span_sup_pow hy₀ hgexp' hgdir
  have hru := isUnit_coeff_of_not_mem_span_sup_pow hy₀ hhexp' hhdir
  have hp0 := map_residue_ne_zero_of_not_mem_pow hx hy₀ hfexp hfd.2
  have hr0 := map_residue_ne_zero_of_not_mem_pow hx hy₀ hhexp' hh.2
  obtain ⟨-, hreg⟩ := BlowupChart.isDomain_quotient_and_mul_eq_zero hdim hmx
  have hx0 : x ≠ 0 := fun h0 => BlowupChart.maximalIdeal_ne_span_singleton hdim y₀ (by
    rw [hmx, h0, Ideal.span_insert_zero])
  have hr' : r = C (r.coeff 1) * X + C (r.coeff 0) := eq_X_add_C_of_natDegree_le_one hr
  have hreval : ∀ t : R, r.eval t = r.coeff 0 + r.coeff 1 * t := fun t => by
    conv_lhs => rw [hr']
    simp only [eval_add, eval_mul, eval_C, eval_X]
    ring
  have hhlin : h = r.coeff 0 * x + r.coeff 1 * y₀ := by
    rw [hhexp']
    simp [Finset.sum_range_succ]
  have hh'eq : (Ideal.Quotient.mk (Ideal.span {C x * X - C y₀}) r) =
      BlowupChart.strictEquation (r.coeff 0) x y₀ (q₁ := r.coeff 1) := by
    rw [BlowupChart.strictEquation]
    congr 1
    conv_lhs => rw [hr']
    ring
  -- tangent directions
  have hpq : ∀ τ : R, p.eval τ ∈ maximalIdeal R → q.eval τ ∈ maximalIdeal R → False :=
    fun τ h1 h2 => BlowupChart.not_eval_mem_and_eval_mem hdim hmx hp hfexp hq hgexp' hT τ h1 h2
  have hpt : p.eval (BlowupChart.root hru (r.coeff 0)) ∉ maximalIdeal R := fun h1 =>
    BlowupChart.not_eval_mem_and_eval_mem hdim hmx hp hfexp hr hhexp' hT' _ h1 (by
      rw [hreval, BlowupChart.add_mul_root]
      exact zero_mem _)
  -- the equations on the chart
  set f' : blowupChart x y₀ := Ideal.Quotient.mk _ p
  set h' : blowupChart x y₀ := Ideal.Quotient.mk _ r
  have hf'eq : algebraMap R (blowupChart x y₀) f = algebraMap R _ x ^ d * f' := by
    rw [hfexp]
    exact BlowupChart.algebraMap_sum_eq_pow_mul x y₀ p hp
  have hh'eq2 : algebraMap R (blowupChart x y₀) h = algebraMap R _ x * h' := by
    rw [hhexp']
    simpa using BlowupChart.algebraMap_sum_eq_pow_mul x y₀ r hr
  have hf'0 : f' ≠ 0 := fun h0 => hp0 (by
    have := congrArg (BlowupChart.toResidue hx hy₀) h0
    rwa [BlowupChart.toResidue_mk, map_zero] at this)
  have hh'0 : h' ≠ 0 := fun h0 => hr0 (by
    have := congrArg (BlowupChart.toResidue hx hy₀) h0
    rwa [BlowupChart.toResidue_mk, map_zero] at this)
  have hfin := BlowupChart.finite_strictTransform hq hgexp' hqu
  have hunit : IsUnit (BlowupChart.chartToStrict g x y₀ f') :=
    BlowupChart.isUnit_eval₂_slope' hq hgexp' hqu p hpq
  have hhreg : IsRegularRing (R ⧸ Ideal.span {r.coeff 0 * x + r.coeff 1 * y₀}) := by
    rw [← hhlin]
    exact BlowupChart.isRegularRing_quotient hdim (by simpa using hh.1) hh.2
  refine ⟨{
    i := i
    d := d
    f' := f'
    h' := h'
    algebraMap_f := hf'eq
    algebraMap_h := hh'eq2
    isLocalization_x := BlowupChart.isLocalization_x hx0 hreg hf'0 hf'eq
    isLocalization_xh := BlowupChart.isLocalization_xh hx0 hreg hf'0 hf'eq hh'0 hh'eq2
    x_mem_nonZeroDivisors := BlowupChart.algebraMap_mem_nonZeroDivisors hx0 hreg hf'0
    h'_mem_nonZeroDivisors := BlowupChart.algebraMap_mem_nonZeroDivisors' hx0 hreg hf'0 hh'0
    isDomain_quotient_x := BlowupChart.isDomain_quotient_x hmx p hp0
    isRegularRing_quotient_x := BlowupChart.isRegularRing_quotient_x hmx f'
    isRegularRing_quotient_h' := by
      rw [hh'eq]
      exact BlowupChart.isRegularRing_quotient_h' hru (r.coeff 0) hhreg f'
    isField_quotient := by
      rw [hh'eq]
      exact BlowupChart.isField_quotient hru (r.coeff 0) hmx p hpt
    maximalIdeal_le_radical := by
      rw [hmx, Ideal.span_le]
      rintro _ (rfl | rfl)
      · exact Ideal.le_radical (Ideal.subset_span (Set.mem_insert _ _))
      · exact ⟨e, pow_mem_span_pair_of_isUnit_coeff hgexp' hqu⟩
    A' := BlowupChart.strictTransform g x y₀
    finite := hfin
    toA' := IsLocalization.Away.lift f' hunit
    toA'_algebraMap := fun s => by
      rw [IsScalarTower.algebraMap_apply R (blowupChart x y₀) (Localization.Away f'),
        IsLocalization.Away.lift_eq, BlowupChart.chartToStrict_algebraMap]
      rfl
    isLocalization_A' := BlowupChart.isLocalization_strictTransform
    mem_jacobson := BlowupChart.mem_jacobson_strictTransform hx }⟩

end AlgebraicGeometry
