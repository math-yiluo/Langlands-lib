/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.Module

/-!
# Finitely generated flat modules over local rings

A finitely generated flat module over a local ring is free. This is mathlib's
`Module.free_of_flat_of_isLocalRing`, restated here as a blueprint node.

## Main statements

- `Module.free_of_finite_of_flat_of_isLocalRing`: a finitely generated flat module over a local
  ring is free.
-/

@[expose] public section

namespace Module

/-- A finitely generated flat module `P` over a local ring `R` is free.
(blueprint: `lem-weil-pbc-finite-flat-local-free`) -/
@[stacks 00NZ]
theorem free_of_finite_of_flat_of_isLocalRing (R P : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Flat R P] : Free R P :=
  free_of_flat_of_isLocalRing

end Module
