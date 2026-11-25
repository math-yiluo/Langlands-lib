/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Tactic.LinearCombination

/-!
# Idempotents determined modulo an ideal in the Jacobson radical

Source: Stacks Project, More on Algebra, Lemma 15.10.2 (Tag 09XF), with Definition
15.10.1 (Tag 0ELY) (blueprint: lem-weil-pbc-idempotents-determined-modulo-radical).
-/

@[expose] public section

universe u

namespace IsIdempotentElem

/-- Idempotents congruent modulo an ideal in the Jacobson radical are equal.
Source: Stacks Project, Tag 09XF, with Tag 0ELY
(blueprint: lem-weil-pbc-idempotents-determined-modulo-radical).

Proof: Put `d = e - e'`. Expanding with `e * e = e` and `e' * e' = e'`
gives `d * d * d = d`. Since `d` belongs to the Jacobson radical, so does `d * d`,
and hence `1 - d * d` is a unit by the Jacobson criterion
`Ideal.isUnit_of_sub_one_mem_jacobson_bot`. The cubic identity gives
`d * (1 - d * d) = 0`; cancelling this unit gives `d = 0`, hence `e = e'`.
This is a direct algebraic proof of the cited Stacks statement.
-/
theorem eq_of_sub_mem_of_le_jacobson {R : Type u} [CommRing R]
    (J : Ideal R) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal R))
    {e e' : R} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (hee' : e - e' ∈ J) : e = e' := by
  let d : R := e - e'
  have hd : d ∈ Ideal.jacobson (⊥ : Ideal R) := hJ hee'
  have hd2 : d * d ∈ Ideal.jacobson (⊥ : Ideal R) :=
    (Ideal.jacobson (⊥ : Ideal R)).mul_mem_left d hd
  have hu : IsUnit (1 - d * d) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    have hn : -(d * d) ∈ Ideal.jacobson (⊥ : Ideal R) :=
      (Ideal.jacobson (⊥ : Ideal R)).neg_mem hd2
    simpa [sub_eq_add_neg] using hn
  have hcube : d * d * d = d := by
    dsimp [d]
    have heq : e * e = e := he
    have heq' : e' * e' = e' := he'
    linear_combination (e + 1 - 3 * e') * heq + (3 * e - e' - 1) * heq'
  have hzero : d * (1 - d * d) = 0 := by
    calc
      d * (1 - d * d) = d - d * d * d := by ring
      _ = 0 := by rw [hcube, sub_self]
  have hcancel : d = 0 := hu.mul_right_cancel (by simpa using hzero)
  exact sub_eq_zero.mp hcancel

end IsIdempotentElem
