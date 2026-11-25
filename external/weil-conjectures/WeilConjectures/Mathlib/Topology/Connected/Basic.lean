/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Connected components in a closed subset

## Main statements

- `IsClosed.isClosed_connectedComponentIn`: the connected components of a closed subset are
  closed.
- `Topology.IsInducing.image_connectedComponent`: an inducing map sends a connected component
  onto a connected component of its range.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- The connected components of a closed subset `F` are closed: the closure of the connected
component of `x` in `F` is preconnected and contained in `F`. -/
theorem IsClosed.isClosed_connectedComponentIn {F : Set X} (hF : IsClosed F) (x : X) :
    IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine closure_subset_iff_isClosed.1 ?_
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset F x) hF)
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

open Set Topology in
/-- An inducing map sends the connected component of `x` onto the connected component of `f x` in
the range of `f`. -/
theorem Topology.IsInducing.image_connectedComponent {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hf : IsInducing f) (x : X) :
    f '' connectedComponent x = connectedComponentIn (range f) (f x) := by
  refine subset_antisymm ((isPreconnected_connectedComponent.image _
    hf.continuous.continuousOn).subset_connectedComponentIn ⟨x, mem_connectedComponent, rfl⟩
    (image_subset_range _ _)) ?_
  have hsub : connectedComponentIn (range f) (f x) ⊆ range f := connectedComponentIn_subset _ _
  rw [← image_preimage_eq_of_subset hsub]
  refine image_mono (IsPreconnected.subset_connectedComponent ?_ ?_)
  · rw [← hf.isPreconnected_image, image_preimage_eq_of_subset hsub]
    exact isPreconnected_connectedComponentIn
  · exact mem_connectedComponentIn (mem_range_self x)
