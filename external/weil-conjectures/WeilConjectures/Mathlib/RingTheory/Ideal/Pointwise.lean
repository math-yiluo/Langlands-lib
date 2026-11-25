/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# The decomposition group normalises the inertia group
-/

@[expose] public section

open scoped Pointwise

namespace Ideal

variable {M R : Type*} [Group M] [Ring R] [MulSemiringAction M R] {P : Ideal R}

/-- An element of the decomposition group of `P` conjugates the inertia group of `P` into
itself. -/
lemma conj_mem_inertia {σ h : M} (hσ : σ ∈ MulAction.stabilizer M P) (hh : h ∈ P.inertia M) :
    σ * h * σ⁻¹ ∈ P.inertia M :=
  AddSubgroup.coe_mem_inertia.2 (Subgroup.Normal.conj_mem inferInstance
    ⟨h, inertia_le_stabilizer P hh⟩ (AddSubgroup.coe_mem_inertia.1 hh) ⟨σ, hσ⟩)

end Ideal
