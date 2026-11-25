/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Compactness.Compact

/-!
# Partitions of a compact space into opens

A compact space partitioned into pairwise disjoint nonempty open sets has only finitely many
pieces.
-/

@[expose] public section

namespace TopologicalSpace.Opens

/-- A compact space covered by pairwise disjoint nonempty open sets is covered by finitely many
of them, so the index type is finite. -/
theorem finite_of_compactSpace_of_pairwiseDisjoint
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}
    (U : ι → Opens X) (hne : ∀ i, (U i : Set X).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : (⨆ i, U i) = ⊤) : Finite ι := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i ↦ (U i : Set X))
    (fun i ↦ (U i).isOpen) (by simp [← coe_iSup, hcov])
  refine Set.finite_univ_iff.mp (t.finite_toSet.subset fun i _ ↦ ?_)
  obtain ⟨y, hy⟩ := hne i
  obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  by_contra hi
  have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
  exact (hdisj i j hij).le_bot ⟨hy, hyj⟩

end TopologicalSpace.Opens
