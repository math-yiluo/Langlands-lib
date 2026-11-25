/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# Depth of a finite module

Source: Stacks Project, Algebra, Definition 10.72.1 (Tag 00LI), Section 10.72
(Tag 00LE); regular sequences, Definition 10.68.1 (Tag 00LF)
(blueprint: def-weil-pbc-depth).

## Main definitions

- `Ideal.depth`: depth with respect to an ideal.
- `IsLocalRing.depth`: depth with respect to the maximal ideal of a local ring.
-/

@[expose] public section

universe v u

namespace Ideal

/-- The depth of a finite module with respect to `I` (Stacks, Tag 00LI;
(blueprint: def-weil-pbc-depth)). When `I M = M` it is infinity. Otherwise it is the
supremum of lengths of regular sequences in `I`, including the empty sequence. -/
noncomputable def depth {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] : ℕ∞ :=
  if (I • (⊤ : Submodule R M)) = ⊤ then ⊤ else
    sSup {n : ℕ∞ | ∃ rs : List R, RingTheory.Sequence.IsRegular M rs ∧
      (∀ x ∈ rs, x ∈ I) ∧ n = (rs.length : ℕ∞)}

end Ideal

namespace IsLocalRing

/-- The depth of a finite module over a local ring is its depth with respect to the
maximal ideal (Stacks, Tag 00LI; blueprint: def-weil-pbc-depth). In particular,
`depth R` is the depth of the local ring as a module over itself. 
(blueprint: def-weil-pbc-depth)
-/
noncomputable def depth {R : Type u} [CommRing R] [IsLocalRing R] (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] : ℕ∞ :=
  (maximalIdeal R).depth M

end IsLocalRing
