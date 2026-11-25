/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Constructible
import WeilConjectures.Topology.ConstructibleIntersection
import WeilConjectures.Topology.ConstructibleIsRetrocompact

/-!
# Constructible subsets of constructible subspaces

Source: Stacks Project, Topology, Lemma 5.15.12, Tag 09YJ
(blueprint: lem-weil-pbc-constructible-in-retrocompact-open).
-/

@[expose] public section

universe u

namespace Topology

open Set TopologicalSpace in
private theorem compactOpenBasis_subtype {X : Type u} [TopologicalSpace X]
    (hBasis : IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U})
    {E : Set X} (hE : IsRetrocompact E) :
    IsTopologicalBasis {U : Set E | IsOpen U ∧ IsCompact U} := by
  refine (isTopologicalBasis_subtype hBasis (· ∈ E)).of_isOpen_of_subset
    (fun U hU ↦ hU.1) ?_
  rintro _ ⟨U, ⟨hUo, hUc⟩, rfl⟩
  refine ⟨hUo.preimage continuous_subtype_val, ?_⟩
  rw [IsEmbedding.subtypeVal.isCompact_iff]
  simpa [Subtype.image_preimage_coe, inter_comm] using hE hUc hUo

open Set TopologicalSpace in
private theorem constructible_preimage_embedding {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (hBasis : IsTopologicalBasis {U : Set Y | IsOpen U ∧ IsCompact U})
    {f : X → Y} (hf : IsEmbedding f) (hr : IsConstructible (range f))
    {S : Set Y} (hS : IsConstructible S) : IsConstructible (f ⁻¹' S) := by
  have h := isConstructible_inter_subtype hBasis hr hS
  have h' := h.preimage_of_isOpenEmbedding hf.toHomeomorph.isOpenEmbedding
  simpa only [preimage_preimage, Function.comp_def, IsEmbedding.toHomeomorph_apply_coe]
    using h'

/-- In a space with a basis of quasi-compact opens, a subset constructible in a constructible
subspace is constructible in the ambient space. Source: Stacks Project, Topology,
Lemma 5.15.12, Tag 09YJ (blueprint: lem-weil-pbc-constructible-in-retrocompact-open).

Proof outline:
1. A retrocompact subspace inherits a basis of quasi-compact opens by intersecting the ambient
basis with it. Constructible sets are retrocompact by Tag 09YH
(`lem-weil-pbc-constructible-is-retrocompact`), so this applies to `E`.
2. Write `E` as a finite union of differences `Uᵢ \ Vᵢ` of retrocompact opens, using
`def-weil-constructible-subset`. Tag 09YI
(`lem-weil-pbc-constructible-intersection-in-constructible`) first in `X`, then in `E`,
shows that `F ∩ (Uᵢ \ Vᵢ)` is constructible in `Uᵢ \ Vᵢ`. Finite unions reduce the claim
to `E = U \ V`.
3. Factor the inclusion through `U`. The subspace `E` is closed in `U` with retrocompact
complement `U ∩ V`. Tag 09YG
(`lem-weil-pbc-constructible-image-closed-retrocompact-complement`) makes `F` constructible
in `U`. Tag 09YD (`lem-weil-pbc-constructible-image-retrocompact-open`) then makes it
constructible in `X`, since `U` is open and retrocompact. -/
theorem isConstructible_of_isConstructible_subspace {X : Type u} [TopologicalSpace X]
    (hBasis : TopologicalSpace.IsTopologicalBasis
      {U : Set X | IsOpen U ∧ IsCompact U})
    {E F : Set X} (hE : IsConstructible E) (hFE : F ⊆ E)
    (hF : IsConstructible ((Subtype.val : E → X) ⁻¹' F)) : IsConstructible F :=
    open Set TopologicalSpace in by
  classical
  have hL : IsSublattice {U : Set X | IsOpen U ∧ IsRetrocompact U} :=
    ⟨fun U hU V hV ↦ ⟨hU.1.union hV.1, hU.2.union hV.2⟩,
      fun U hU V hV ↦ ⟨hU.1.inter hV.1, hU.2.inter_isOpen hV.2 hV.1⟩⟩
  induction E, hE using BooleanSubalgebra.closure_sdiff_sup_induction hL
      ⟨isOpen_empty, .empty⟩ ⟨isOpen_univ, .univ⟩ generalizing F with
  | sdiff U hU V hV =>
    change IsOpen U ∧ IsRetrocompact U at hU
    change IsOpen V ∧ IsRetrocompact V at hV
    let i : ↥(U \ V) → U := inclusion sdiff_subset
    have hr : range i = (Subtype.val ⁻¹' V : Set U)ᶜ := by
      ext x
      simp [i, range_inclusion]
    have hi : IsClosedEmbedding i :=
      ⟨IsEmbedding.inclusion sdiff_subset, hr ▸
        (hV.1.preimage continuous_subtype_val).isClosed_compl⟩
    have hc : IsRetrocompact (range i)ᶜ := by
      rw [hr, compl_compl]
      exact hV.2.preimage_of_isOpenEmbedding hU.1.isOpenEmbedding_subtypeVal
    have hFU := hF.image_of_isClosedEmbedding hi hc
    have hFX := hFU.image_of_isOpenEmbedding hU.1.isOpenEmbedding_subtypeVal
      (by simpa using hU.2)
    have hEq : (Subtype.val : U → X) '' (i '' ((Subtype.val : ↥(U \ V) → X) ⁻¹' F)) =
        F := by
      rw [image_image]
      change Subtype.val '' ((Subtype.val : ↥(U \ V) → X) ⁻¹' F) = F
      exact image_preimage_eq_of_subset fun x hx ↦ ⟨⟨x, hFE hx⟩, rfl⟩
    rwa [hEq] at hFX
  | sup A hA B hB ihA ihB =>
    change F ⊆ A ∪ B at hFE
    change IsConstructible A at hA
    change IsConstructible B at hB
    have hBasisAB := compactOpenBasis_subtype hBasis (hA.union hB).isRetrocompact
    have hFA : IsConstructible ((Subtype.val : A → X) ⁻¹' (F ∩ A)) := by
      have hr : IsConstructible (range (inclusion (subset_union_left : A ⊆ A ∪ B))) := by
        rw [range_inclusion]
        exact isConstructible_inter_subtype hBasis (hA.union hB) hA
      simpa only [preimage_inter, Subtype.coe_preimage_self, inter_univ, preimage_preimage,
        Function.comp_def, inclusion, Subtype.coe_mk] using
        constructible_preimage_embedding hBasisAB (IsEmbedding.inclusion subset_union_left) hr hF
    have hFB : IsConstructible ((Subtype.val : B → X) ⁻¹' (F ∩ B)) := by
      have hr : IsConstructible (range (inclusion (subset_union_right : B ⊆ A ∪ B))) := by
        rw [range_inclusion]
        exact isConstructible_inter_subtype hBasis (hA.union hB) hB
      simpa only [preimage_inter, Subtype.coe_preimage_self, inter_univ, preimage_preimage,
        Function.comp_def, inclusion, Subtype.coe_mk] using
        constructible_preimage_embedding hBasisAB (IsEmbedding.inclusion subset_union_right) hr hF
    have hEq : F = (F ∩ A) ∪ (F ∩ B) := by
      ext x
      have := @hFE x
      simp only [mem_union, mem_inter_iff] at *
      tauto
    rw [hEq]
    exact (ihA inter_subset_right hFA).union (ihB inter_subset_right hFB)

end Topology
