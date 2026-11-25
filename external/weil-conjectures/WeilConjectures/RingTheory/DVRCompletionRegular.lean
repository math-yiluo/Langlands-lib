/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.DVRCompletionGenericFiber
import WeilConjectures.RingTheory.CompletionClosedFiber

/-!
# Regularity of completion maps for characteristic-zero discrete valuation rings

Source: Stacks Project, More on Algebra, Proposition Tag 07PX, proof of (3) and (4);
Algebra, Lemma Tag 00PD (blueprint: lem-weil-pbc-dvr-completion-regular).
-/

@[expose] public section

universe u v

namespace AdicCompletion

/-- The canonical maximal-ideal-adic completion map of a discrete valuation ring (a Noetherian
local domain of dimension one with principal maximal ideal, Stacks Algebra Tag 00PD; Mathlib's
`IsDiscreteValuationRing`) is regular if its fraction field has characteristic zero.
Source: Stacks Project, More on Algebra, Proposition Tag 07PX, proof of (3) and (4), using
Algebra, Lemma Tag 00PD (blueprint: lem-weil-pbc-dvr-completion-regular).

Proof:
1. The completion map is flat by Mathlib's Noetherian completion instance.
2. A nonzero prime of a DVR is maximal (the principal ideal domain theorem), hence
   equals its unique maximal ideal. Thus the primes are zero and the maximal ideal.
3. `isGeometricallyRegular_genericFiber_of_isDiscreteValuationRing_of_charZero`
   identifies the generic fibre with a field, using the completion-DVR theorem and
   the source library's fraction-field base-change lemma. Purely inseparable
   extensions in characteristic zero are trivial, so this fibre is geometrically regular.
4. `isGeometricallyRegular_closedFiber` identifies the closed fibre with the residue
   field as an algebra over itself, using the completion evaluation quotient and the
   quotient-tensor equivalence. Every field base change is again a field.
5. Combine flatness and the two fibres using the definition of a regular ring map. -/
theorem isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] :
    RingHom.IsRegular (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  classical
  rw [RingHom.IsRegular, toAlgebra_algebraMap]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, ?_⟩
  intro p hp
  by_cases h : p = ⊥
  · subst p
    exact isGeometricallyRegular_genericFiber_of_isDiscreteValuationRing_of_charZero A K
  · have : p.IsMaximal := IsPrime.to_maximal_ideal h
    have heq : p = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
    subst p
    exact isGeometricallyRegular_closedFiber A

end AdicCompletion
