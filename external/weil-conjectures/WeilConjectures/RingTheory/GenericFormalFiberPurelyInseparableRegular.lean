/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.GenericFormalFiberPurelyInseparableRegularAux
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! Regularity after purely inseparable base change for generic formal fibres.
(blueprint: new-lem-weil-pbc-generic-formal-fibre-purely-inseparable-regular) -/

@[expose] public section

universe u

set_option linter.style.haveILetI false in
/-- Every finite purely inseparable base change of the generic formal fibre is regular.
Source: Stacks Project, More on Algebra, Proposition 07PS, last two paragraphs.
(blueprint: new-lem-weil-pbc-generic-formal-fibre-purely-inseparable-regular) -/
theorem isRegular_genericFormalFiber_after_finite_purelyInseparable
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
    ∀ (k' : Type (max u u)) [Field k']
      [Algebra ((⊥ : Ideal A).ResidueField) k'] [Module.Finite ((⊥ : Ideal A).ResidueField) k']
      [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'],
      IsRegularRing
        (TensorProduct ((⊥ : Ideal A).ResidueField) k' ((⊥ : Ideal A).Fiber C)) := by
  dsimp
  intro k' instField instAlg instFinite instPI
  letI := instField
  letI := instAlg
  letI := instFinite
  letI := instPI
  rcases hmodel with h | h
  · rcases h with ⟨k, hk, d, e⟩
    letI := hk
    exact isRegular_genericFormalFiber_fieldModel A k d e P k'
  · rcases h with ⟨Λ, hΛ, d, p, hc, e⟩
    letI := hΛ
    exact isRegular_genericFormalFiber_cohenModel A Λ d p hc e P k' 

end
