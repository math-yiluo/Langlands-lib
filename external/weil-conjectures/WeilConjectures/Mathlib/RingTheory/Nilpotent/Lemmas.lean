/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# The nilradical is stable under ring isomorphisms

- `nilradical_eq_map_ringEquiv`: a ring isomorphism maps the nilradical onto the nilradical.
-/

@[expose] public section

/-- A ring automorphism maps the nilradical onto itself. -/
lemma nilradical_eq_map_ringEquiv {B : Type*} [CommRing B] (σ : B ≃+* B) :
    nilradical B = (nilradical B).map (σ : B →+* B) := by
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.map_le_iff_le_comap.2 fun x hx ↦ ?_)
  · have : σ (σ.symm x) = x := σ.apply_symm_apply x
    rw [← this]
    exact Ideal.mem_map_of_mem _ (mem_nilradical.2 ((mem_nilradical.1 hx).map σ.symm))
  · exact mem_nilradical.2 ((mem_nilradical.1 hx).map σ)
