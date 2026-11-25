/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FibreRingNoetherian

/-! Noetherianity of the generic formal fibre of a regular power-series model.
(blueprint: new-lem-weil-pbc-generic-formal-fibre-noetherian) -/

@[expose] public section

universe u

/-- The generic formal fibre in the regular power-series case is Noetherian.
Source: Stacks Project, More on Algebra, Proposition 07PS, first two paragraphs.
(blueprint: new-lem-weil-pbc-generic-formal-fibre-noetherian) -/
theorem isNoetherian_genericFormalFiber_of_regular_powerSeries
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    (hmodel :
      (∃ (k : Type u), ∃ h : Field k, ∃ d : ℕ,
        let _ := h
        Nonempty (A ≃+* MvPowerSeries (Fin d) k)) ∨
      (∃ (Λ : Type u), ∃ h : CommRing Λ, ∃ d : ℕ,
        let _ := h
        ∃ p : ℕ, IsCohenRing p Λ ∧
          Nonempty (A ≃+* MvPowerSeries (Fin d) Λ)))
    (P : Ideal A) [P.IsPrime] :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P)
    IsNoetherianRing ((⊥ : Ideal A).Fiber C) := by
  have _ := hmodel
  let R := Localization.AtPrime P
  let I := IsLocalRing.maximalIdeal R
  let C := AdicCompletion I R
  let : IsNoetherianRing R := inferInstance
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing I
  change IsNoetherianRing ((⊥ : Ideal A).Fiber C)
  exact Ideal.isNoetherianRing_fiber (B := C) (⊥ : Ideal A)

end
