/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.RingTheory.Ideal.BigOperators

/-!
# Coefficient reduction of power series modulo a finitely generated ideal

Source: Stacks Project, Tag 0EYB, the power-series closed-fibre calculation.
(blueprint: lem-sbc-mv-power-series-quotient-kernel)
-/

@[expose] public section

namespace MvPowerSeries

/-- Reduction of all coefficients has kernel the extension of a finitely generated ideal.

Source: Stacks Project, Tag 0EYB, the calculation underlying the extended maximal ideal.
(blueprint: lem-sbc-mv-power-series-quotient-kernel)

Proof: Constants from I reduce to zero, so their generated ideal lies in the kernel.
Conversely every coefficient of a series in the kernel belongs to I. Choose a finite
family of generators of I and express each coefficient as a linear combination of
these generators. For each generator assemble its coefficients in these expressions
into a power series. The original series is the finite sum of these power series
multiplied by the constant series of the generators, hence belongs to the extended
ideal. The empty generating family gives the zero series. The argument allows an
empty variable set and the unit ideal. -/
theorem ker_map_quotient_of_fg {R : Type*} [CommRing R] (σ : Type*)
    (I : Ideal R) (hI : I.FG) :
    RingHom.ker (map (σ := σ) (Ideal.Quotient.mk I)) = I.map C := by
  classical
  apply le_antisymm
  · intro f hf
    have hcoeff : ∀ d, coeff d f ∈ I := by
      intro d
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have h := congrArg (coeff d) (RingHom.mem_ker.mp hf)
      simpa only [coeff_map, map_zero] using h
    obtain ⟨s, hs⟩ := hI
    have hspan : Ideal.span (Set.range (fun i : s ↦ (i : R))) = I := by
      rw [show Set.range (fun i : s ↦ (i : R)) = (s : Set R) from
        by ext b; simp]
      exact hs
    have hex : ∀ d, ∃ a : s → R, ∑ i, a i * (i : R) = coeff d f := by
      intro d
      apply Ideal.mem_span_range_iff_exists_fun.mp
      rw [hspan]
      exact hcoeff d
    choose a ha using hex
    let g : s → MvPowerSeries σ R := fun i d ↦ a d i
    have heq : f = ∑ i : s, g i * C (i : R) := by
      apply MvPowerSeries.ext
      intro d
      rw [map_sum]
      simp only [coeff_mul_C]
      exact (ha d).symm
    rw [heq]
    apply Ideal.sum_mem
    intro i _
    apply Ideal.mul_mem_left
    apply Ideal.mem_map_of_mem
    rw [← hs]
    exact Submodule.subset_span i.2
  · apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change map (σ := σ) (Ideal.Quotient.mk I) (C b) = 0
    rw [map_C, (Ideal.Quotient.eq_zero_iff_mem).mpr hb, map_zero]

end MvPowerSeries
