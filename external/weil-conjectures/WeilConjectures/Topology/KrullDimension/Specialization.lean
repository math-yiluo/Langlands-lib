/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension of a closed subset covered by closures of points

In a quasi-sober `T₀` space, a closed subset contained in the union of the closures of the
points of a set `S` has dimension at most any common bound on the dimensions of these closures.
-/

@[expose] public section

open Topology Order

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

attribute [local instance] specializationOrder in
/-- In a quasi-sober `T₀` space, a closed subset `T` contained in the union of the closures of
the points of `S` has dimension at most `N` if each of these closures does: every point of `T`
is a specialization of a point of `S`, so its height is at most the height of that point. -/
theorem topologicalKrullDim_le_of_subset_iUnion_closure_singleton {T S : Set X}
    (hT : IsClosed T) (hTS : T ⊆ ⋃ y ∈ S, closure {y}) {N : WithBot ℕ∞}
    (h : ∀ y ∈ S, topologicalKrullDim (closure {y} : Set X) ≤ N) :
    topologicalKrullDim T ≤ N := by
  have := hT.isClosedEmbedding_subtypeVal.quasiSober
  let o := specializationOrder T
  rw [topologicalKrullDim_eq_krullDim_specializationOrder,
    @krullDim_eq_iSup_height T o.toPreorder]
  refine iSup_le fun t ↦ ?_
  obtain ⟨y, hy, hty⟩ := Set.mem_iUnion₂.1 (hTS t.2)
  have hmono : @StrictMono T X o.toPreorder _ Subtype.val :=
    @strictMono_of_le_iff_le T X o.toPreorder _ _ fun a b ↦
      (IsInducing.subtypeVal.specializes_iff (x := b) (y := a)).symm
  refine le_trans ?_ ((topologicalKrullDim_closure_singleton y).symm.trans_le (h y hy))
  exact_mod_cast (@height_le_height_apply_of_strictMono T X o.toPreorder _ _ hmono t).trans
    (height_mono (specializes_iff_mem_closure.2 hty))
