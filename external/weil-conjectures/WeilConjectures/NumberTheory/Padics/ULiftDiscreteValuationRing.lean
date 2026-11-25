/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Universe lifts of the `p`-adic integers form a discrete valuation ring

The universe lift `ULift ℤ_[p]`, used as a coefficient ring for sheaves of modules in
`ModuleCat.{u + 1}`, is a domain (`ULift.isDomain_padicInt`) and a discrete valuation ring
(`ULift.isDiscreteValuationRing_padicInt`), in which `p` is a nonzero nonunit
(`ULift.natCast_ne_zero_padicInt`, `ULift.not_isUnit_natCast_padicInt`).
-/

@[expose] public section

universe v

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ULift ℤ_[p]` is a domain. -/
instance ULift.isDomain_padicInt : IsDomain (ULift.{v} ℤ_[p]) :=
  MulEquiv.isDomain ℤ_[p] (ULift.ringEquiv.toMulEquiv)

/-- `ULift ℤ_[p]` is a discrete valuation ring. -/
instance ULift.isDiscreteValuationRing_padicInt : IsDiscreteValuationRing (ULift.{v} ℤ_[p]) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (ULift.ringEquiv.symm : ℤ_[p] ≃+* ULift.{v} ℤ_[p])

/-- `p` is nonzero in `ULift ℤ_[p]`. -/
lemma ULift.natCast_ne_zero_padicInt : (p : ULift.{v} ℤ_[p]) ≠ 0 := by
  rw [Ne, ← (ULift.ringEquiv (R := ℤ_[p])).injective.eq_iff, map_natCast, map_zero,
    Nat.cast_eq_zero]
  exact hp.out.ne_zero

/-- `p` is not a unit in `ULift ℤ_[p]`. -/
lemma ULift.not_isUnit_natCast_padicInt : ¬IsUnit (p : ULift.{v} ℤ_[p]) := by
  intro h
  have := h.map (ULift.ringEquiv : ULift.{v} ℤ_[p] ≃+* ℤ_[p])
  rw [map_natCast] at this
  exact PadicInt.p_nonunit this
