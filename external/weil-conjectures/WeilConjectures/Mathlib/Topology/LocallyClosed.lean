/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Closures of locally closed subsets of noetherian quasi-sober spaces

In a noetherian quasi-sober space every point of the closure of a locally closed subset `N` is
a specialization of a point of `N`.
-/

@[expose] public section

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- In a noetherian quasi-sober space, every point of the closure of a locally closed subset
`N = U ∩ Z` is a specialization of a point of `N`: writing `Z` as a finite union of irreducible
closed subsets `t`, the point lies in the closure of some `U ∩ t`, which is then nonempty, so
that the open `U` contains the generic point of `t`. -/
theorem IsLocallyClosed.closure_subset_iUnion_closure_singleton [NoetherianSpace X]
    [QuasiSober X] {N : Set X} (hN : IsLocallyClosed N) :
    closure N ⊆ ⋃ y ∈ N, closure {y} := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hN
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  intro x hx
  rw [Set.sUnion_eq_biUnion, Set.inter_iUnion₂, hSf.closure_biUnion] at hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨g, hg⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  obtain ⟨z, hzU, hzt⟩ : (U ∩ t).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hxt
    exact hxt
  refine Set.mem_iUnion₂.2 ⟨g, ⟨(hg.specializes hzt).mem_open hU hzU,
    Set.mem_sUnion_of_mem hg.mem ht⟩, ?_⟩
  rw [hg.def]
  exact closure_minimal Set.inter_subset_right (hSc t ht) hxt
