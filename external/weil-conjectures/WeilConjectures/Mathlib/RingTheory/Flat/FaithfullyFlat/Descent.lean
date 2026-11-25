/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness descends along faithfully flat ring maps

We record `Module.Flat.of_flat_tensorProduct` in the language of
`RingHom.CodescendsAlong`: a ring map `R →+* S` is flat as soon as its base change along a
faithfully flat `R →+* R'` is.
-/

@[expose] public section

namespace RingHom

/-- Flatness of ring maps codescends along faithfully flat ring maps. -/
lemma Flat.codescendsAlong_faithfullyFlat : CodescendsAlong Flat FaithfullyFlat := by
  refine .mk _ Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [flat_algebraMap_iff] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_flat_tensorProduct R T S

end RingHom
