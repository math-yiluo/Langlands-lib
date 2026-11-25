/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.BlowupChartBasic
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Div

/-!
# The strict transform of a regular curve on a blow-up chart

Let `C = R[T]/(xT - y)` and `h = q₀ x + q₁ y` with `q₁` a unit, so that the line `h = 0` is not
`x = 0`. On `C`, `h = x h'` with `h' = q₀ + q₁ T`, and the strict transform `V(h') ⊆ Spec C` of
`V(h)` is the section `T = t₀ := -q₀/q₁`. We construct

* the isomorphism `C/(h') ≅ R/(h)`, `T ↦ t₀`, as a surjection `BlowupChart.toQuotient` with
  kernel `(h')` (`BlowupChart.ker_toQuotient`);
* for `R` local with maximal ideal `(x, y)`, the surjection `BlowupChart.toResidueField` of `C`
  onto the residue field at the point `T = t₀` of the exceptional divisor, with kernel `(x, h')`
  (`BlowupChart.ker_toResidueField`).
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

namespace BlowupChart

variable {R : Type u} [CommRing R] {q₁ : R} (hq₁ : IsUnit q₁) (q₀ : R)

/-- The root `t₀ = -q₀/q₁` of `q₀ + q₁ T`. -/
noncomputable def root : R := -q₀ * ↑hq₁.unit⁻¹

/-- `q₀ + q₁ t₀ = 0`. -/
theorem add_mul_root : q₀ + q₁ * root hq₁ q₀ = 0 := by
  have := hq₁.mul_val_inv
  rw [root]
  linear_combination (-q₀) * this

/-- `x t₀ - y = -(q₀ x + q₁ y)/q₁`. -/
theorem mul_root_sub (x y : R) :
    x * root hq₁ q₀ - y = -(↑hq₁.unit⁻¹ * (q₀ * x + q₁ * y)) := by
  have := hq₁.mul_val_inv
  rw [root]
  linear_combination y * this

/-- `T - t₀ = (q₀ + q₁ T)/q₁`. -/
theorem X_sub_C_root :
    X - C (root hq₁ q₀) = C (↑hq₁.unit⁻¹ : R) * (C q₀ + C q₁ * X) := by
  have := congrArg C hq₁.mul_val_inv
  rw [C_mul, C_1] at this
  rw [root, C_mul, C_neg]
  linear_combination (-X) * this

variable (x y : R)

/-- The equation `h' = q₀ + q₁ T` of the strict transform of `V(q₀ x + q₁ y)`. -/
noncomputable abbrev strictEquation : R[X] ⧸ Ideal.span {C x * X - C y} :=
  Ideal.Quotient.mk _ (C q₀ + C q₁ * X)

/-- On the chart, `q₀ x + q₁ y = x h'`. -/
theorem algebraMap_eq_mul_strictEquation :
    algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y}) (q₀ * x + q₁ * y) =
      algebraMap R _ x * strictEquation q₀ x y (q₁ := q₁) := by
  simp only [strictEquation, map_add, map_mul, mk_C]
  rw [← algebraMap_mul_mk_X x y]
  ring

include hq₁ in
/-- Every element of the chart is congruent to an element of `R` modulo `h'`. -/
theorem exists_sub_mem_span_strictEquation (c : R[X] ⧸ Ideal.span {C x * X - C y}) :
    ∃ r : R, c - algebraMap R _ r ∈ Ideal.span {strictEquation q₀ x y (q₁ := q₁)} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨s, hs⟩ := X_sub_C_dvd_sub_C_eval (a := root hq₁ q₀) (p := p)
  refine ⟨p.eval (root hq₁ q₀), Ideal.mem_span_singleton'.mpr
    ⟨Ideal.Quotient.mk _ (C (↑hq₁.unit⁻¹ : R) * s), ?_⟩⟩
  rw [← mk_C, ← map_sub, hs, X_sub_C_root, strictEquation, ← map_mul]
  congr 1
  ring

/-- The map `C → R/(q₀ x + q₁ y)`, `T ↦ t₀`; it identifies `C/(h')` with `R/(h)`. -/
noncomputable def toQuotient :
    R[X] ⧸ Ideal.span {C x * X - C y} →+* R ⧸ Ideal.span {q₀ * x + q₁ * y} :=
  Ideal.Quotient.lift _ (eval₂RingHom (Ideal.Quotient.mk _)
    (Ideal.Quotient.mk _ (root hq₁ q₀))) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have h0 : eval₂RingHom (Ideal.Quotient.mk (Ideal.span {q₀ * x + q₁ * y}))
        (Ideal.Quotient.mk _ (root hq₁ q₀)) (C x * X - C y) = 0 := by
      simp only [coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]
      rw [← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, mul_root_sub]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    rw [map_mul, h0, mul_zero]

/-- The map `C → R/(h)` on classes of polynomials is evaluation at `t₀`. -/
theorem toQuotient_mk (p : R[X]) :
    toQuotient hq₁ q₀ x y (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (p.eval (root hq₁ q₀)) :=
  eval₂_at_apply _ _

/-- The map `C → R/(h)` is the quotient map on `R`. -/
theorem toQuotient_algebraMap (r : R) :
    toQuotient hq₁ q₀ x y (algebraMap R _ r) = Ideal.Quotient.mk _ r := by
  rw [← mk_C, toQuotient_mk, eval_C]

/-- The map `C → R/(h)` is surjective. -/
theorem toQuotient_surjective : Function.Surjective (toQuotient hq₁ q₀ x y) := by
  intro a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨_, toQuotient_algebraMap hq₁ q₀ x y r⟩

/-- The kernel of `C → R/(h)` is `(h')`: the strict transform of `V(h)` is `V(h')`. -/
theorem ker_toQuotient :
    RingHom.ker (toQuotient hq₁ q₀ x y) = Ideal.span {strictEquation q₀ x y (q₁ := q₁)} := by
  have hh' : toQuotient hq₁ q₀ x y (strictEquation q₀ x y (q₁ := q₁)) = 0 := by
    rw [strictEquation, toQuotient_mk]
    simp [add_mul_root]
  refine le_antisymm (fun c hc => ?_) ?_
  · obtain ⟨r, hr⟩ := exists_sub_mem_span_strictEquation hq₁ q₀ x y c
    have h1 : toQuotient hq₁ q₀ x y (c - algebraMap R _ r) = 0 := by
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hr
      rw [← hw, map_mul, hh', mul_zero]
    rw [map_sub, RingHom.mem_ker.mp hc, zero_sub, neg_eq_zero, toQuotient_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨s, rfl⟩ := h1
    rw [← sub_add_cancel c (algebraMap R _ (s * (q₀ * x + q₁ * y)))]
    refine Ideal.add_mem _ hr ?_
    rw [map_mul, algebraMap_eq_mul_strictEquation]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hh'

variable [IsLocalRing R]

/-- The map `C → κ`, `T ↦ t₀`, onto the residue field at the point `T = t₀` of the exceptional
divisor, for `x, y ∈ 𝔪`. -/
noncomputable def toResidueField (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) :
    R[X] ⧸ Ideal.span {C x * X - C y} →+* ResidueField R :=
  Ideal.Quotient.lift _ (eval₂RingHom (residue R) (residue R (root hq₁ q₀))) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [(residue_eq_zero_iff x).mpr hx, (residue_eq_zero_iff y).mpr hy]

/-- The map `C → κ` on classes of polynomials is evaluation at `t₀` followed by reduction. -/
theorem toResidueField_mk (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) (p : R[X]) :
    toResidueField hq₁ q₀ x y hx hy (Ideal.Quotient.mk _ p) = residue R (p.eval (root hq₁ q₀)) :=
  eval₂_at_apply _ _

/-- The map `C → κ` is the residue map on `R`. -/
theorem toResidueField_algebraMap (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) (r : R) :
    toResidueField hq₁ q₀ x y hx hy (algebraMap R _ r) = residue R r := by
  rw [← mk_C, toResidueField_mk, eval_C]

/-- The map `C → κ` is surjective. -/
theorem toResidueField_surjective (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) :
    Function.Surjective (toResidueField hq₁ q₀ x y hx hy) := by
  intro a
  obtain ⟨r, rfl⟩ := residue_surjective a
  exact ⟨_, toResidueField_algebraMap hq₁ q₀ x y hx hy r⟩

/-- If `𝔪 = (x, y)`, the kernel of `C → κ` is `(x, h')`: the strict transform of `V(h)` meets
the exceptional divisor in the reduced point `T = t₀`. -/
theorem ker_toResidueField (hm : maximalIdeal R = Ideal.span {x, y}) :
    RingHom.ker (toResidueField hq₁ q₀ x y (hm ▸ Ideal.subset_span (by simp))
      (hm ▸ Ideal.subset_span (by simp))) =
      Ideal.span {algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y}) x,
        strictEquation q₀ x y (q₁ := q₁)} := by
  have hx : x ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have hy : y ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have hh' : toResidueField hq₁ q₀ x y hx hy (strictEquation q₀ x y (q₁ := q₁)) = 0 := by
    rw [strictEquation, toResidueField_mk]
    simp [add_mul_root]
  refine le_antisymm (fun c hc => ?_) ?_
  · obtain ⟨r, hr⟩ := exists_sub_mem_span_strictEquation hq₁ q₀ x y c
    have h1 : toResidueField hq₁ q₀ x y hx hy (c - algebraMap R _ r) = 0 := by
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hr
      rw [← hw, map_mul, hh', mul_zero]
    rw [map_sub, RingHom.mem_ker.mp hc, zero_sub, neg_eq_zero, toResidueField_algebraMap,
      residue_eq_zero_iff, hm, Ideal.mem_span_pair] at h1
    obtain ⟨a, b, rfl⟩ := h1
    rw [← sub_add_cancel c (algebraMap R _ (a * x + b * y))]
    refine Ideal.add_mem _ (Ideal.span_mono (by simp) hr) ?_
    rw [Ideal.mem_span_pair]
    refine ⟨algebraMap R _ a + algebraMap R _ b * Ideal.Quotient.mk _ X, 0, ?_⟩
    rw [map_add, map_mul, map_mul, ← algebraMap_mul_mk_X x y]
    ring
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, hh'⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, toResidueField_algebraMap, residue_eq_zero_iff]
    exact hx

end BlowupChart
