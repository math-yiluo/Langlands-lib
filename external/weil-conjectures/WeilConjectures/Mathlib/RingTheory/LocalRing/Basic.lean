/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Idempotents of local rings

- `IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem`: the only idempotents of a local ring are
  `0` and `1`.
-/

@[expose] public section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The only idempotents of a local ring are `0` and `1`: one of `e` and `1 - e` is a unit, and
an idempotent unit is `1`. (blueprint: `lem-weil-pbc-local-ring-idempotent-zero-one`) -/
theorem eq_zero_or_eq_one_of_isIdempotentElem {e : R} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  rcases isUnit_or_isUnit_one_sub_self e with h | h
  · exact .inr <| h.mul_left_cancel (by rw [he.eq, mul_one])
  · exact .inl <| h.mul_right_cancel (by rw [zero_mul, mul_sub, mul_one, he.eq, sub_self])

end IsLocalRing
