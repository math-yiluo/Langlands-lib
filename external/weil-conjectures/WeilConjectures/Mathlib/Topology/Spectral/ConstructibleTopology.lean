/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import WeilConjectures.Mathlib.Topology.Spectral.Basic

/-!
# Intersections of constructible sets of spectral spaces are quasi-compact

In a quasi-compact, quasi-separated, quasi-sober prespectral space `X` (for instance a spectral
space), every intersection of constructible sets is quasi-compact.
Indeed, constructible sets are closed in the constructible topology, which is
quasi-compact (`compactSpace_withConstructibleTopology`) and finer than the topology of `X`.

## Main statements

- `constructibleTopology_le`: the constructible topology of a prespectral space is finer than
  its topology.
- `isCompact_iInter_of_isConstructible`: intersections of constructible sets are quasi-compact.
- `IsClosed.isClosed_constructibleTopology`: closed sets are closed in the constructible topology.
- `IsCompact.isClosed_constructibleTopology_generalizationHull`: the generalizations of a
  quasi-compact subset of a spectral space form a closed set of the constructible topology.
-/

@[expose] public section

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- The constructible topology of a prespectral space is finer than its topology: an open set is
a union of quasi-compact open sets, which are open in the constructible topology. -/
lemma constructibleTopology_le [PrespectralSpace X] :
    constructibleTopology X ≤ ‹TopologicalSpace X› := by
  intro U hU
  rw [PrespectralSpace.isTopologicalBasis.open_eq_sUnion' hU]
  refine @isOpen_sUnion X (constructibleTopology X) _ fun V hV ↦ ?_
  exact hV.1.2.isOpen_constructibleTopology_of_isOpen hV.1.1

/-- A constructible set is clopen in the constructible topology, in a quasi-compact space. -/
lemma Topology.IsConstructible.isClopen_constructibleTopology [CompactSpace X] {s : Set X}
    (hs : IsConstructible s) : @IsClopen X (constructibleTopology X) s := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU hU' =>
    refine ⟨?_, hU'.isCompact.isOpen_constructibleTopology_of_isOpen hU⟩
    refine (@isOpen_compl_iff X U (constructibleTopology X)).mp ?_
    exact (by rw [compl_compl]; exact hU'.isCompact : IsCompact Uᶜᶜ
      ).isOpen_constructibleTopology_of_isClosed hU.isClosed_compl
  | union s _ t _ hs ht => exact @IsClopen.union X (constructibleTopology X) _ _ hs ht
  | compl s _ hs => exact @IsClopen.compl X (constructibleTopology X) _ hs

/-- **Intersections of constructible sets are quasi-compact** in a quasi-compact,
quasi-separated, quasi-sober prespectral space: they are closed in the constructible topology,
which is quasi-compact and finer than the topology of `X`. -/
lemma isCompact_iInter_of_isConstructible [CompactSpace X] [QuasiSober X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] {ι : Sort*} {s : ι → Set X} (hs : ∀ i, IsConstructible (s i)) :
    IsCompact (⋂ i, s i) := by
  let φ : WithConstructibleTopology X → X := WithTopology.ofTopology
  have hφ : Continuous φ := by
    refine continuous_def.mpr fun U hU ↦ ?_
    rw [WithConstructibleTopology.isOpen_iff]
    exact constructibleTopology_le U hU
  have hK : IsClosed (φ ⁻¹' ⋂ i, s i) := by
    rw [Set.preimage_iInter]
    refine isClosed_iInter fun i ↦ ?_
    rw [WithConstructibleTopology.isClosed_iff]
    exact (hs i).isClopen_constructibleTopology.1
  have := hK.isCompact.image hφ
  rwa [Set.image_preimage_eq _ fun x ↦ ⟨WithTopology.toTopology _ x, rfl⟩] at this

/-- In a prespectral space, a closed set is closed in the constructible topology, which is finer
than the topology of the space. -/
lemma IsClosed.isClosed_constructibleTopology [PrespectralSpace X] {s : Set X} (hs : IsClosed s) :
    IsClosed[constructibleTopology X] s :=
  (@isOpen_compl_iff X s (constructibleTopology X)).mp (constructibleTopology_le _ hs.isOpen_compl)

/-- In a spectral space, the set of generalizations of a quasi-compact subset is closed in the
constructible topology: it is the intersection of the compact opens containing the subset. -/
lemma IsCompact.isClosed_constructibleTopology_generalizationHull [SpectralSpace X] {s : Set X}
    (hs : IsCompact s) : IsClosed[constructibleTopology X] (generalizationHull s) := by
  obtain ⟨S, hS, hS'⟩ := generalizationHull.eq_sInter_of_isCompact hs
  rw [hS']
  exact @isClosed_sInter X (constructibleTopology X) S fun U hU ↦
    (hS hU).2.isClosed_constructibleTopology_of_isOpen (hS hU).1
