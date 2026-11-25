/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Trivial square-zero extensions of local rings

The projection `R ⊕ M → R` of a trivial square-zero extension reflects units, so the trivial
square-zero extension of a local ring (in particular the ring of dual numbers `R[ε]` over a local
ring `R`) is local.
-/

@[expose] public section

namespace TrivSqZeroExt

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]

instance isLocalHom_fstHom : IsLocalHom (fstHom R R M).toRingHom :=
  ⟨fun _ ↦ isUnit_iff_isUnit_fst.mpr⟩

instance [IsLocalRing R] : IsLocalRing (TrivSqZeroExt R M) :=
  RingHom.domain_isLocalRing (fstHom R R M).toRingHom

end TrivSqZeroExt
