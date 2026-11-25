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
import WeilConjectures.RingTheory.GenericFormalFiberNoetherian
import WeilConjectures.RingTheory.GenericFormalFiberPurelyInseparableRegular

/-!
# Generic formal fibres of regular power-series models

Source: Stacks Project, More on Algebra, Proposition 07PS, last two paragraphs
(blueprint: lem-weil-pbc-regular-power-series-generic-formal-fibre).
-/

@[expose] public section

universe u

/-- The generic formal fibre of a regular local domain presented as a finite-variable
power series ring over a field or a Cohen ring is geometrically regular.
Source: Stacks Project, More on Algebra, Proposition 07PS, last two paragraphs.
(blueprint: lem-weil-pbc-regular-power-series-generic-formal-fibre).

Proof: Localize the regular local ring A at P, using Algebra 0AFS. Its completion C is
regular local by More on Algebra 07NY, and hence regular by 0AFS applied at every prime.
The generic fibre is the localization of C at the images of the nonzero elements of A;
therefore it is Noetherian and regular. If the fraction field has characteristic zero,
every finite purely inseparable extension is trivial. Tensoring with such an extension
thus preserves this regular ring, proving geometric regularity. In positive characteristic
p, the Cohen-ring presentation is impossible: a Cohen ring is a domain with nonzero
prime-number uniformizer l. Characteristic l would kill this uniformizer, while a different
positive prime characteristic would make it a unit by Bezout's identity. Thus a Cohen ring
has characteristic zero, as do its power series ring and fraction field. Consequently A
is isomorphic to k[[X_1,...,X_d]] for a field k of characteristic p. Apply More on Algebra
07PR with no polynomial variables (m = 0). The power-series isomorphism and the isomorphism
from the polynomial ring in zero variables induce compatible isomorphisms of prime
localizations, maximal-ideal completions and fraction fields. Tensoring these isomorphisms
with finite purely inseparable extensions transports regularity to the displayed fibre.
The Noetherianity already obtained completes the geometric-regularity condition. -/
theorem isGeometricallyRegular_genericFormalFiber_of_regular_powerSeries
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
    Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber C) := by
  dsimp [Algebra.IsGeometricallyRegular]
  constructor
  · exact isNoetherian_genericFormalFiber_of_regular_powerSeries A hmodel P
  · exact isRegular_genericFormalFiber_after_finite_purelyInseparable A hmodel P
