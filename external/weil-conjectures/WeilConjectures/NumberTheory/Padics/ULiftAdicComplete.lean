/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Universe lifts of the `p`-adic integers as coefficient rings

The universe lift `ULift ℤ_[p]` (used as a coefficient ring for sheaves of modules in
`ModuleCat.{u + 1}`) is noetherian and `p`-adically precomplete
(`ULift.isPrecomplete_span_natCast_padicInt`).
-/

@[expose] public section

universe v

variable (p : ℕ) [Fact p.Prime]

/-- `ℤ_[p]` is `p`-adically precomplete. -/
instance PadicInt.isPrecomplete_span_natCast : IsPrecomplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

/-- `ULift ℤ_[p]` is `p`-adically precomplete. -/
instance ULift.isPrecomplete_span_natCast_padicInt :
    IsPrecomplete (Ideal.span {(p : ULift.{v} ℤ_[p])}) (ULift.{v} ℤ_[p]) := by
  have := IsPrecomplete.of_ringEquiv (ULift.ringEquiv.symm : ℤ_[p] ≃+* ULift.{v} ℤ_[p]) (p : ℤ_[p])
  rwa [map_natCast] at this

/-- `ULift ℤ_[p]` is noetherian. -/
instance ULift.isNoetherianRing_padicInt : IsNoetherianRing (ULift.{v} ℤ_[p]) :=
  isNoetherianRing_of_ringEquiv _ (ULift.ringEquiv.symm : ℤ_[p] ≃+* ULift.{v} ℤ_[p])
