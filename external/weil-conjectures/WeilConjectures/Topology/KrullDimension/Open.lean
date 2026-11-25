/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension of closures of points and open subsets

In a quasi-sober `T₀` space:

- `Order.height_head_add_length_le_height_last`: along a chain, the height grows at least by the
  length of the chain.
- `Topology.IsOpenEmbedding.topologicalKrullDim_closure_singleton_inter_range`: along an open
  embedding `e`, the closure of `e y` meets the range of `e` in a set of the dimension of the
  closure of `y`.
- `topologicalKrullDim_le_of_forall_exists_isOpen`: the dimension of a closed subset is bounded
  by a common bound on the dimensions of its traces on the members of an open cover.
-/

@[expose] public section

open Topology Order

/-- Along a chain `p`, the height grows at least by the length of `p`: a chain ending at the
head of `p` extends by `p`. -/
lemma Order.height_head_add_length_le_height_last {α : Type*} [Preorder α] (p : LTSeries α) :
    height p.head + p.length ≤ height p.last := by
  cases h : height p.head with
  | top =>
    have : height p.head ≤ height p.last := height_mono p.head_le_last
    simp_all
  | coe n =>
    obtain ⟨q, hq, hlen⟩ := exists_series_of_le_height p.head (le_of_eq h.symm)
    have := length_le_height_last (p := q.smash p hq)
    simpa [hlen] using this

variable {X : Type*} [TopologicalSpace X]

/-- Along an open embedding `e : Y → X`, the trace on the range of `e` of the closure of `e y`
has the dimension of the closure of `y`: it is the image of the latter. -/
theorem Topology.IsOpenEmbedding.topologicalKrullDim_closure_singleton_inter_range
    {Y : Type*} [TopologicalSpace Y] {e : Y → X} (he : IsOpenEmbedding e) (y : Y) :
    topologicalKrullDim (closure {e y} ∩ Set.range e : Set X) =
      topologicalKrullDim (closure {y} : Set Y) := by
  have h : e '' closure {y} = closure {e y} ∩ Set.range e := by
    rw [he.isInducing.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range,
      Set.image_singleton]
  rw [← h, (he.isEmbedding.comp IsEmbedding.subtypeVal).topologicalKrullDim_eq_range,
    Set.range_comp, Subtype.range_coe]

variable [QuasiSober X] [T0Space X]

/-- The dimension of a closed subset `Z` of a quasi-sober `T₀` space is at most `n` as soon as
every point of `Z` has an open neighbourhood `V` with `dim (Z ∩ V) ≤ n`. -/
theorem topologicalKrullDim_le_of_forall_exists_isOpen {Z : Set X} (hZ : IsClosed Z)
    {n : WithBot ℕ∞}
    (h : ∀ z ∈ Z, ∃ V : Set X, IsOpen V ∧ z ∈ V ∧ topologicalKrullDim (Z ∩ V : Set X) ≤ n) :
    topologicalKrullDim Z ≤ n := by
  have := hZ.isClosedEmbedding_subtypeVal.quasiSober
  choose V hV hzV hd using h
  let U (z : Z) : TopologicalSpace.Opens Z :=
    ⟨Subtype.val ⁻¹' V z.1 z.2, (hV _ _).preimage continuous_subtype_val⟩
  refine topologicalKrullDim_le_of_iSup_eq_top U ?_ n fun z ↦ ?_
  · exact eq_top_iff.2 fun z _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨z, hzV z.1 z.2⟩
  · have hr : Set.range ((Subtype.val : Z → X) ∘ (Subtype.val : U z → Z)) = Z ∩ V z.1 z.2 := by
      ext x
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨w.1.2, w.2⟩
      · rintro ⟨hxZ, hxV⟩
        exact ⟨⟨⟨x, hxZ⟩, hxV⟩, rfl⟩
    rw [(IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).topologicalKrullDim_eq_range, hr]
    exact hd z.1 z.2

omit [QuasiSober X] [T0Space X] in
/-- A nonempty space has nonnegative dimension: the closure of a point is an irreducible closed
subset. -/
theorem topologicalKrullDim_nonneg [Nonempty X] : 0 ≤ topologicalKrullDim X :=
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {Classical.arbitrary X}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  krullDim_nonneg

omit [QuasiSober X] [T0Space X] in
/-- A nonempty space of dimension at most `N : ℕ` has dimension a natural number. -/
theorem exists_topologicalKrullDim_eq_natCast [Nonempty X] {N : ℕ}
    (h : topologicalKrullDim X ≤ N) : ∃ n : ℕ, n ≤ N ∧ topologicalKrullDim X = n := by
  have h₀ := topologicalKrullDim_nonneg (X := X)
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot => simp [hd] at h₀
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      rw [hd] at h
      exact absurd h (not_le.2 (by exact_mod_cast ENat.natCast_lt_top N))
    | coe m =>
      rw [hd] at h
      exact ⟨m, by exact_mod_cast h, rfl⟩
