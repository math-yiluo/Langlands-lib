/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Depth

/-!
# The `I`-depth of a module

Basic facts about `Ideal.depth` (Stacks, Algebra, Definition 00LF).
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R]

lemma depth_eq_top_of_smul_eq_top (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (h : I • (⊤ : Submodule R M) = ⊤) : I.depth M = ⊤ := by
  simp [depth, h]

end Ideal
