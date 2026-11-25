/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionDimension

/-!
# Regularity and completion of Noetherian local rings

Source: Stacks Project, More on Algebra, Lemma Tag 07NY
(blueprint: lem-weil-pbc-completion-regular-local).
-/

@[expose] public section


universe u

namespace AdicCompletion

/-- A Noetherian local ring is regular if and only if its maximal-ideal-adic completion
is regular. Source: Stacks Project, More on Algebra, Lemma Tag 07NY
(blueprint: lem-weil-pbc-completion-regular-local).

Proof: install the Noetherian instance for the completion using
`lem-weil-pbc-adic-completion-noetherian`. Rewrite both predicates with Mathlib's
`isRegularLocalRing_iff`; rewrite the maximal-ideal span finrank using
`AdicCompletion.spanFinrank_maximalIdeal_eq`, and rewrite the completion dimension using
`lem-weil-pbc-completion-dimension`. The two sides then coincide. -/
theorem isRegularLocalRing_iff (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    IsRegularLocalRing A ↔ IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  set_option linter.style.haveILetI false in
    letI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    AdicCompletion.isNoetherianRing _
  rw [_root_.isRegularLocalRing_iff, _root_.isRegularLocalRing_iff]
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq]
  rw [RingTheory.completion_dimension A |>.1]

end AdicCompletion
