/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Topology.SpectralSpace.Constructible

/-!
# Extending clopen subsets from a closed subset of a spectral space

Let `T` be a spectral space and `T₀ ⊆ T` a closed subset such that every irreducible closed
subset `C ⊆ T` meets `T₀` in a nonempty connected set. Then every subset `A ⊆ T₀` which is open
and closed in `T₀` is the trace on `T₀` of an open and closed subset of `T`.

The clopen subset is `U = {y | closure {y} ∩ (T₀ \ A) = ∅}`. Since `closure {y} ∩ T₀` is
connected, every point lies in `U` or in the analogous set `V` for `T₀ \ A`, and not in both.
Both sets are stable under specialization and open in the constructible topology, so they are
complementary closed sets.

## Main statements

- `exists_isClopen_inter_eq_of_isConnected_inter`: the extension.
-/

@[expose] public section

open Topology

variable {T : Type*} [TopologicalSpace T] [SpectralSpace T]

/-- The points `y` with `closure {y}` disjoint from a closed set `B` form a set which is open in
the constructible topology: around such a `y` it contains the complement of a compact open
neighbourhood of `B` avoiding `y`. -/
lemma isOpen_constructibleTopology_setOf_disjoint_closure {B : Set T} (hB : IsClosed B) :
    IsOpen[constructibleTopology T] {y : T | Disjoint (closure {y}) B} := by
  refine @isOpen_iff_forall_mem_open T (constructibleTopology T) _ |>.2 fun y hy ↦ ?_
  obtain ⟨W, hWc, hWo, hBW, hWy⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    hB.isCompact isClosed_closure.isOpen_compl hy.subset_compl_left
  refine ⟨Wᶜ, fun y' hy' ↦ ?_, IsCompact.isOpen_constructibleTopology_of_isClosed
    (by rwa [compl_compl]) hWo.isClosed_compl, fun hyW ↦ hWy hyW (subset_closure rfl)⟩
  exact Set.disjoint_of_subset_left
    (closure_minimal (Set.singleton_subset_iff.2 hy') hWo.isClosed_compl)
    (Set.disjoint_compl_left_iff_subset.2 hBW)

omit [SpectralSpace T] in
/-- The points `y` with `closure {y}` disjoint from a set `B` form a set stable under
specialization. -/
lemma stableUnderSpecialization_setOf_disjoint_closure (B : Set T) :
    StableUnderSpecialization {y : T | Disjoint (closure {y}) B} :=
  fun _ _ h hy ↦ Set.disjoint_of_subset_left (specializes_iff_closure_subset.1 h) hy

/-- **Extending clopen subsets.** Let `T` be a spectral space and `T₀ ⊆ T` a closed subset such
that every irreducible closed subset of `T` meets `T₀` in a nonempty connected set. If `A ⊆ T₀`
is closed and `T₀ \ A` is closed, then `A = U ∩ T₀` for an open and closed `U ⊆ T`. -/
theorem exists_isClopen_inter_eq_of_isConnected_inter {T₀ : Set T}
    (hC : ∀ C : Set T, IsClosed C → IsIrreducible C → IsConnected (C ∩ T₀))
    {A : Set T} (hAT : A ⊆ T₀) (hA : IsClosed A) (hB : IsClosed (T₀ \ A)) :
    ∃ U : Set T, IsClopen U ∧ U ∩ T₀ = A := by
  set B := T₀ \ A
  let U := {y : T | Disjoint (closure {y}) B}
  let V := {y : T | Disjoint (closure {y}) A}
  have hUV : Uᶜ = V := by
    ext y
    have hy := hC _ isClosed_closure (isIrreducible_singleton (x := y)).closure
    have hcov : closure {y} ∩ T₀ ⊆ A ∪ B := fun z hz ↦ by
      by_cases hzA : z ∈ A
      · exact Or.inl hzA
      · exact Or.inr ⟨hz.2, hzA⟩
    change ¬ Disjoint (closure {y}) B ↔ Disjoint (closure {y}) A
    rw [Set.not_disjoint_iff]
    constructor
    · rintro ⟨b, hby, hbB⟩
      rw [Set.disjoint_left]
      intro a hay haA
      obtain ⟨z, hz, hzA, hzB⟩ := isPreconnected_closed_iff.1 hy.isPreconnected A B hA hB hcov
        ⟨a, ⟨hay, hAT haA⟩, haA⟩ ⟨b, ⟨hby, hbB.1⟩, hbB⟩
      exact hzB.2 hzA
    · intro hd
      obtain ⟨z, hzy, hzT⟩ := hy.nonempty
      rcases hcov ⟨hzy, hzT⟩ with hzA | hzB
      · exact absurd hzA (Set.disjoint_left.1 hd hzy)
      · exact ⟨z, hzy, hzB⟩
  have hU : IsClosed U := by
    refine IsClosed.of_isClosed_constructibleTopology ?_
      (stableUnderSpecialization_setOf_disjoint_closure B)
    refine (@isOpen_compl_iff T _ (constructibleTopology T)).1 ?_
    rw [hUV]
    exact isOpen_constructibleTopology_setOf_disjoint_closure hA
  have hV : IsClosed V := by
    refine IsClosed.of_isClosed_constructibleTopology ?_
      (stableUnderSpecialization_setOf_disjoint_closure A)
    refine (@isOpen_compl_iff T _ (constructibleTopology T)).1 ?_
    rw [← hUV, compl_compl]
    exact isOpen_constructibleTopology_setOf_disjoint_closure hB
  refine ⟨U, ⟨hU, by rw [← isClosed_compl_iff, hUV]; exact hV⟩, ?_⟩
  ext y
  refine ⟨fun ⟨hyU, hyT⟩ ↦ ?_, fun hyA ↦ ⟨?_, hAT hyA⟩⟩
  · by_contra hyA
    exact Set.disjoint_left.1 hyU (subset_closure rfl) ⟨hyT, hyA⟩
  · by_contra hyU
    have : y ∈ V := hUV ▸ hyU
    exact Set.disjoint_left.1 this (subset_closure rfl) hyA
