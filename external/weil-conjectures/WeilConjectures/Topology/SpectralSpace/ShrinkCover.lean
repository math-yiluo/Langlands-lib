/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Spectral.Basic
public import WeilConjectures.Topology.SpectralSpace.Constructible

/-!
# Shrinking a cover of a closed subset of a spectral space

Let `T` be a spectral space and `T₀ ⊆ T` a closed subset such that every irreducible closed
subset `C ⊆ T` meets `T₀` in a nonempty connected set. Suppose `T₀` is covered by finitely many
quasi-compact opens `Uᵢ`, and that we are given open "agreement loci" `Agree i j ⊆ Uᵢ ∩ Uⱼ`
forming a partial equivalence relation at every point, which contain `Uᵢ ∩ Uⱼ ∩ T₀`. Then the
`Uᵢ` can be shrunk to opens `Wᵢ ⊆ Uᵢ` which cover all of `T`, still contain `Uᵢ ∩ T₀`, and
such that `Wᵢ ∩ Wⱼ ⊆ Agree i j`.

This is the topological core of the Zariski restriction criterion
`TopCat.Sheaf.bijective_unit_app_top`: applied with `Agree i j` the locus where two local
sections have the same germ, it glues local sections defined near `T₀` and agreeing along `T₀`
to a global section. Stating it without sheaves allows to apply it to sheaves on the small étale
site, whose values live in a larger universe than the points of `T`.

## Main statements

- `SpectralSpace.exists_shrink_of_isConnected_inter`: the shrinking.

## References

- Stacks Project, Lemma 59.82.4, <https://stacks.math.columbia.edu/tag/09ZG>
-/

@[expose] public section

open Topology

namespace SpectralSpace

variable {T : Type*} [TopologicalSpace T] [SpectralSpace T] {T₀ : Set T}

/-- **Shrinking a cover of a closed subset of a spectral space.** Let `T` be a spectral space
and `T₀ ⊆ T` a closed subset such that every irreducible closed subset of `T` meets `T₀` in a
nonempty connected set. Let `Uᵢ` be finitely many quasi-compact opens covering `T₀`, and let
`Agree i j` be opens which are reflexive, symmetric and transitive pointwise and
contain `Uᵢ ∩ Uⱼ ∩ T₀`. Then there are opens `Wᵢ ⊆ Uᵢ` covering `T`, with `Uᵢ ∩ T₀ ⊆ Wᵢ` and
`Wᵢ ∩ Wⱼ ⊆ Agree i j`. -/
theorem exists_shrink_of_isConnected_inter (hT₀ : IsClosed T₀)
    (hC : ∀ C : Set T, IsClosed C → IsIrreducible C → IsConnected (C ∩ T₀))
    {I : Type*} [Finite I] (U : I → Set T) (hUo : ∀ i, IsOpen (U i))
    (hUc : ∀ i, IsCompact (U i)) (hcov : T₀ ⊆ ⋃ i, U i) (Agree : I → I → Set T)
    (hAo : ∀ i j, IsOpen (Agree i j))
    (hrefl : ∀ i, U i ⊆ Agree i i) (hsymm : ∀ i j, Agree i j ⊆ Agree j i)
    (htrans : ∀ i j k, Agree i j ∩ Agree j k ⊆ Agree i k)
    (hT₀A : ∀ i j, U i ∩ U j ∩ T₀ ⊆ Agree i j) :
    ∃ W : I → Set T, (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ U i) ∧ (∀ y, ∃ i, y ∈ W i) ∧
      (∀ i j, W i ∩ W j ⊆ Agree i j) ∧ (∀ i, U i ∩ T₀ ⊆ W i) := by
  -- Every point of `T` specializes to a point of `T₀`.
  have hspec : ∀ y : T, ∃ z ∈ T₀, y ⤳ z := fun y ↦ by
    obtain ⟨z, hz, hz₀⟩ := (hC _ isClosed_closure isIrreducible_singleton.closure).nonempty
    exact ⟨z, hz₀, specializes_iff_mem_closure.mpr hz⟩
  have hcov' : ∀ z ∈ T₀, ∃ i, z ∈ U i := fun z hz ↦ Set.mem_iUnion.mp (hcov hz)
  have agree_gen : ∀ {k l y w}, y ⤳ w → w ∈ Agree k l → y ∈ Agree k l :=
    fun h hw ↦ h.mem_open (hAo _ _) hw
  -- The connectedness argument: two opens of the cover containing specializations of `y` lying
  -- in `T₀` agree at `y`.
  have key : ∀ y k l, (∃ w ∈ U k ∩ T₀, y ⤳ w) → (∃ w ∈ U l ∩ T₀, y ⤳ w) → y ∈ Agree k l := by
    intro y k l ⟨wk, ⟨hwk, hwk₀⟩, hyk⟩ ⟨wl, ⟨hwl, hwl₀⟩, hyl⟩
    have hconn :=
      (hC _ isClosed_closure (isIrreducible_singleton (x := y)).closure).isPreconnected
    by_contra hkl
    obtain ⟨w, ⟨hwc, hw₀⟩, hwu, hwv⟩ := hconn (⋃ m, ⋃ (_ : y ∈ Agree k m), U m)
      (⋃ m, ⋃ (_ : y ∉ Agree k m), U m)
      (isOpen_iUnion fun m ↦ isOpen_iUnion fun _ ↦ hUo m)
      (isOpen_iUnion fun m ↦ isOpen_iUnion fun _ ↦ hUo m)
      (fun w ⟨_, hw₀⟩ ↦ by
        obtain ⟨m, hm⟩ := hcov' w hw₀
        by_cases h : y ∈ Agree k m
        · exact Or.inl (Set.mem_iUnion₂.mpr ⟨m, h, hm⟩)
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨m, h, hm⟩))
      ⟨wk, ⟨specializes_iff_mem_closure.mp hyk, hwk₀⟩, Set.mem_iUnion₂.mpr
        ⟨k, hrefl k (hyk.mem_open (hUo k) hwk), hwk⟩⟩
      ⟨wl, ⟨specializes_iff_mem_closure.mp hyl, hwl₀⟩, Set.mem_iUnion₂.mpr ⟨l, hkl, hwl⟩⟩
    obtain ⟨m₁, h₁, hw₁⟩ := Set.mem_iUnion₂.mp hwu
    obtain ⟨m₂, h₂, hw₂⟩ := Set.mem_iUnion₂.mp hwv
    exact h₂ (htrans k m₁ m₂ ⟨h₁, agree_gen (specializes_iff_mem_closure.mpr hwc)
      (hT₀A m₁ m₂ ⟨⟨hw₁, hw₂⟩, hw₀⟩)⟩)
  -- The points of `U i` where `U i` may fail to agree with another `U j`.
  let K : I → Set T := fun m ↦ U m ∩ T₀
  have hK : ∀ m, IsCompact (K m) := fun m ↦ (hUc m).inter_right hT₀
  let Bd : I → Set T := fun i ↦ U i ∩ ⋃ j, (generalizationHull (K j) ∩ (Agree i j)ᶜ)
  have hBd : ∀ i, IsClosed[constructibleTopology T] (Bd i) := fun i ↦
    @IsClosed.inter T _ _ (constructibleTopology T)
      ((hUc i).isClosed_constructibleTopology_of_isOpen (hUo i))
      (@isClosed_iUnion_of_finite T I (constructibleTopology T) _ _ fun j ↦
        @IsClosed.inter T _ _ (constructibleTopology T)
          (hK j).isClosed_constructibleTopology_generalizationHull
          (isClosed_compl_iff.mpr (hAo i j)).isClosed_constructibleTopology)
  have claim₁ : ∀ i y, (∃ z ∈ K i, y ⤳ z) → y ∉ closure (Bd i) := by
    intro i y ⟨z, hz, hyz⟩ hy
    obtain ⟨y', ⟨_, hy'⟩, hy'y⟩ :=
      exists_specializes_of_isClosed_constructibleTopology_of_mem_closure (hBd i) hy
    obtain ⟨j, hjgen, hjnot⟩ := Set.mem_iUnion.mp hy'
    obtain ⟨w, hw, hy'w⟩ := mem_generalizationHull_iff.mp hjgen
    exact hjnot (key y' i j ⟨z, hz, hy'y.trans hyz⟩ ⟨w, hw, hy'w⟩)
  -- The shrunk opens.
  refine ⟨fun i ↦ U i \ closure (Bd i), fun i ↦ (hUo i).sdiff isClosed_closure,
    fun i y hy ↦ hy.1, fun y ↦ ?_, fun i j y ⟨hyi, hyj⟩ ↦ ?_,
    fun i z hz ↦ ⟨hz.1, claim₁ i z ⟨z, hz, specializes_rfl⟩⟩⟩
  · obtain ⟨z, hz₀, hyz⟩ := hspec y
    obtain ⟨i, hzi⟩ := hcov' z hz₀
    exact ⟨i, hyz.mem_open (hUo i) hzi, claim₁ i y ⟨z, ⟨hzi, hz₀⟩, hyz⟩⟩
  · obtain ⟨z, hz₀, hyz⟩ := hspec y
    obtain ⟨k, hzk⟩ := hcov' z hz₀
    have hgen : y ∈ generalizationHull (K k) :=
      mem_generalizationHull_iff.mpr ⟨z, ⟨hzk, hz₀⟩, hyz⟩
    have hik : y ∈ Agree i k := by
      by_contra h
      exact hyi.2 (subset_closure ⟨hyi.1, Set.mem_iUnion.mpr ⟨k, hgen, h⟩⟩)
    have hjk : y ∈ Agree j k := by
      by_contra h
      exact hyj.2 (subset_closure ⟨hyj.1, Set.mem_iUnion.mpr ⟨k, hgen, h⟩⟩)
    exact htrans i k j ⟨hik, hsymm j k hjk⟩

end SpectralSpace
