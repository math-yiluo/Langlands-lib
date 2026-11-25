/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sober

/-!
# Finite `T₀` spaces are sober

Every irreducible closed subset of a finite `T₀` space has a unique generic point.
-/

@[expose] public section

open Set

variable {Y : Type*} [TopologicalSpace Y]

/-- In a finite `T₀` space, every irreducible closed subset `Z` has exactly one point `η` whose
closure is `Z`. (blueprint: `lem-weil-pbc-finite-t0-space-sober`) -/
theorem existsUnique_isGenericPoint_of_finite [Finite Y] [T0Space Y] {Z : Set Y}
    (hZ : IsIrreducible Z) (hZc : IsClosed Z) : ∃! η, η ∈ Z ∧ closure {η} = Z := by
  obtain ⟨W, hW, hZW⟩ := (isIrreducible_iff_sUnion_isClosed.1 hZ)
    (Z.toFinite.toFinset.image fun z ↦ closure ({z} : Set Y)) (by
      intro W hW
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hW
      exact isClosed_closure) (by
      intro z hz
      refine mem_sUnion.2 ⟨closure {z}, ?_, subset_closure rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨z, (Z.toFinite.mem_toFinset).2 hz, rfl⟩))
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.1 hW
  have hηZ : η ∈ Z := (Z.toFinite.mem_toFinset).1 hη
  have hcl : closure {η} = Z :=
    le_antisymm ((closure_minimal (singleton_subset_iff.2 hηZ)) hZc) hZW
  refine ⟨η, ⟨hηZ, hcl⟩, fun η' ⟨_, h'⟩ ↦ ?_⟩
  exact (inseparable_iff_closure_eq.2 (h'.trans hcl.symm)).eq
