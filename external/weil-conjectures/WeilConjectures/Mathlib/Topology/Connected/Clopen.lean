/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Connected locally irreducible spaces are irreducible

## Main statements

- `irreducibleSpace_of_forall_exists_isPreirreducible`: a connected space in which every point
  has a preirreducible open neighbourhood is irreducible.
-/

@[expose] public section

open Set

variable {X : Type*} [TopologicalSpace X]

/-- A connected space in which every point has a preirreducible open neighbourhood is
irreducible: the irreducible component of any point is then open as well as closed. -/
theorem irreducibleSpace_of_forall_exists_isPreirreducible [ConnectedSpace X]
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPreirreducible U) : IrreducibleSpace X := by
  obtain ⟨x₀⟩ := ‹ConnectedSpace X›.toNonempty
  set C := irreducibleComponent x₀
  have hC : IsClopen C := by
    refine ⟨isClosed_irreducibleComponent, isOpen_iff_forall_mem_open.mpr fun y hy ↦ ?_⟩
    obtain ⟨U, hU, hyU, hUirr⟩ := h y
    have hCU : C ⊆ closure U := (subset_closure_inter_of_isPreirreducible_of_isOpen
      isIrreducible_irreducibleComponent.isPreirreducible hU ⟨y, hy, hyU⟩).trans
        (closure_mono inter_subset_right)
    have : closure U = C := eq_irreducibleComponent hUirr.closure hCU
    exact ⟨U, this ▸ subset_closure, hU, hyU⟩
  have hCuniv : C = univ := IsClopen.eq_univ hC ⟨x₀, mem_irreducibleComponent⟩
  exact (irreducibleSpace_def X).mpr (by
    rw [Set.top_eq_univ, ← hCuniv]; exact isIrreducible_irreducibleComponent)
