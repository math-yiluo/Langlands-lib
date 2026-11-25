/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Sober

/-!
# Connected components of a noetherian space

A noetherian topological space has finitely many irreducible components, and every irreducible
component lies in a single connected component. Hence it has finitely many connected
components, and each of them is open, being the complement of the finitely many other ones.

Likewise a point lying in a unique irreducible component has a preirreducible open
neighbourhood (`TopologicalSpace.NoetherianSpace.exists_isOpen_isPreirreducible`), and if the
irreducible components are pairwise disjoint, they are the connected components
(`TopologicalSpace.NoetherianSpace.connectedComponent_eq_irreducibleComponent`).

The same argument applied to the open subspaces shows that a noetherian space is locally
connected (`TopologicalSpace.NoetherianSpace.locallyConnectedSpace`). Consequently, the preimage
of a connected component of a noetherian subspace under a continuous map landing in it is open and
closed (`TopologicalSpace.NoetherianSpace.isClopen_preimage_connectedComponentIn`).
-/

@[expose] public section

open Topology

variable {α : Type*} [TopologicalSpace α]

/-- A homeomorphism of `X` permutes the irreducible components of `X`. -/
theorem Homeomorph.image_mem_irreducibleComponents (φ : α ≃ₜ α) {Z : Set α}
    (hZ : Z ∈ irreducibleComponents α) : φ '' Z ∈ irreducibleComponents α := by
  rw [← φ.preimage_symm]
  refine preimage_mem_irreducibleComponents hZ φ.symm.isOpenEmbedding ?_
  obtain ⟨z, hz⟩ := hZ.1.nonempty
  exact ⟨z, hz, φ.symm.surjective z⟩

namespace TopologicalSpace.NoetherianSpace

variable [NoetherianSpace α]

/-- A noetherian space has finitely many connected components. -/
instance finite_connectedComponents : Finite (ConnectedComponents α) := by
  have : Finite (irreducibleComponents α) := finite_irreducibleComponents.to_subtype
  refine Finite.of_surjective (fun Z : irreducibleComponents α ↦
    (ConnectedComponents.mk (Z.2.1.nonempty.some) : ConnectedComponents α)) fun c ↦ ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  refine ConnectedComponents.coe_eq_coe'.mpr ?_
  exact (irreducibleComponent_property x).1.isPreconnected.subset_connectedComponent
    mem_irreducibleComponent (isIrreducible_irreducibleComponent (x := x)).nonempty.some_mem

/-- Every connected component of a noetherian space is open. -/
theorem isOpen_connectedComponent (x : α) : IsOpen (connectedComponent x) :=
  ConnectedComponents.discreteTopology_iff.mp inferInstance x

/-- In a noetherian space, a point `x` lying in a unique irreducible component has a
preirreducible open neighbourhood, namely the complement of the (finitely many) other
irreducible components. -/
theorem exists_isOpen_isPreirreducible (x : α)
    (h : ∀ Z₁ ∈ irreducibleComponents α, ∀ Z₂ ∈ irreducibleComponents α, x ∈ Z₁ → x ∈ Z₂ →
      Z₁ = Z₂) :
    ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ IsPreirreducible U := by
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  have hopen : IsOpen (⋃ W ∈ irreducibleComponents α \ {irreducibleComponent x}, W)ᶜ :=
    (finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1).isOpen_compl
  refine ⟨_, hopen, ?_, ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun W hW hxW ↦ hW.2 (h W hW.1 _ hZ hxW mem_irreducibleComponent)
  · refine (isIrreducible_irreducibleComponent (x := x)).isPreirreducible.open_subset hopen
      fun y hy ↦ ?_
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy
    by_contra hyZ
    refine hy _ ⟨irreducibleComponent_mem_irreducibleComponents y, fun h ↦ hyZ ?_⟩
      mem_irreducibleComponent
    rw [← Set.mem_singleton_iff.mp h]
    exact mem_irreducibleComponent

/-- A nonempty noetherian space has a nonempty open subset all of whose points lie in a single
irreducible component: the complement of all irreducible components but one. -/
theorem exists_isOpen_nonempty_forall_eq [Nonempty α] :
    ∃ U : Set α, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, ∀ Z₁ ∈ irreducibleComponents α,
      ∀ Z₂ ∈ irreducibleComponents α, x ∈ Z₁ → x ∈ Z₂ → Z₁ = Z₂ := by
  obtain ⟨x⟩ := ‹Nonempty α›
  set Z := irreducibleComponent x
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  set W := ⋃ W ∈ irreducibleComponents α \ {Z}, W
  have hW : IsClosed W := finite_irreducibleComponents.sdiff.isClosed_biUnion
    fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have hU : (Wᶜ).Nonempty := by
    by_contra hU
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hU
    obtain ⟨W', hW', hZW'⟩ := (isIrreducible_iff_sUnion_isClosed.1 hZ.1)
      (finite_irreducibleComponents.sdiff (t := {Z})).toFinset
      (fun W hW ↦ isClosed_of_mem_irreducibleComponents W
        ((Set.Finite.mem_toFinset _).1 hW).1)
      (by
        rw [Set.Finite.coe_toFinset, Set.sUnion_eq_biUnion]
        exact fun x _ ↦ (hU ▸ Set.mem_univ x : x ∈ W))
    rw [Set.Finite.mem_toFinset] at hW'
    exact hW'.2 (le_antisymm (hZ.2 hW'.1.1 hZW') hZW')
  refine ⟨Wᶜ, hW.isOpen_compl, hU, fun y hy Z₁ hZ₁ Z₂ hZ₂ h₁ h₂ ↦ ?_⟩
  have key (V : Set α) (hV : V ∈ irreducibleComponents α) (hyV : y ∈ V) : V = Z := by
    by_contra hVZ
    exact hy (Set.mem_biUnion (x := V) ⟨hV, hVZ⟩ hyV)
  rw [key Z₁ hZ₁ h₁, key Z₂ hZ₂ h₂]

/-- In a noetherian space with pairwise disjoint irreducible components, the connected component
of a point is its irreducible component. -/
theorem connectedComponent_eq_irreducibleComponent
    (h : (irreducibleComponents α).Pairwise Disjoint) (x : α) :
    connectedComponent x = irreducibleComponent x := by
  set Z := irreducibleComponent x
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  have hcompl : Zᶜ = ⋃ W ∈ irreducibleComponents α \ {Z}, W := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff,
      exists_prop]
    refine ⟨fun hy ↦ ⟨_, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
      mem_irreducibleComponent⟩, ?_⟩
    · rintro hyZ
      exact hy (hyZ ▸ mem_irreducibleComponent)
    · rintro ⟨W, ⟨hW, hWZ⟩, hyW⟩ hyZ
      exact Set.disjoint_left.1 (h hW hZ hWZ) hyW hyZ
  have hclopen : IsClopen Z := by
    refine ⟨isClosed_irreducibleComponent, ?_⟩
    rw [← isClosed_compl_iff, hcompl]
    exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  exact (hclopen.connectedComponent_subset mem_irreducibleComponent).antisymm
    (isIrreducible_irreducibleComponent.isPreirreducible.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent)

/-- A noetherian space is locally connected: the connected components of its open subsets, which
are again noetherian, are open. -/
instance (priority := 100) locallyConnectedSpace : LocallyConnectedSpace α := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF x hx
  rw [connectedComponentIn_eq_image hx]
  exact hF.isOpenMap_subtype_val _ (isOpen_connectedComponent _)

/-- **Isolating a point of a closed set.** In a noetherian quasi-sober space, a closed point `y`
of a closed set `Z` which has no other generisation in `Z` has an open neighbourhood meeting `Z`
only in `y`: the irreducible components of `Z` containing `y` are the closures of points
generalising `y`, hence equal to `{y}`, and the finitely many other ones are closed and avoid
`y`. -/
theorem exists_isOpen_inter_eq_singleton [QuasiSober α] {Z : Set α} (hZ : IsClosed Z) {y : α}
    (hy : y ∈ Z) (hyc : IsClosed {y}) (h : ∀ z ∈ Z, z ⤳ y → z = y) :
    ∃ W : Set α, IsOpen W ∧ y ∈ W ∧ W ∩ Z = {y} := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := exists_finite_set_isClosed_irreducible hZ
  have hfin : Set.Finite {t | t ∈ S ∧ y ∉ t} := hSf.subset fun _ ht ↦ ht.1
  have hcl : IsClosed (⋃₀ {t | t ∈ S ∧ y ∉ t}) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht ↦ hSc t ht.1
  refine ⟨(⋃₀ {t | t ∈ S ∧ y ∉ t})ᶜ, hcl.isOpen_compl, fun hy' ↦ ?_, ?_⟩
  · obtain ⟨t, ht, hyt⟩ := hy'
    exact ht.2 hyt
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨fun hy' ↦ ?_, hy⟩, ?_⟩
  · obtain ⟨t, ht, hyt⟩ := hy'
    exact ht.2 hyt
  rintro z ⟨hzW, t, ht, hzt⟩
  have hyt : y ∈ t := by
    by_contra hyt
    exact hzW ⟨t, ⟨ht, hyt⟩, hzt⟩
  obtain ⟨g, hg⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  have hgy : g = y := h g ⟨t, ht, hg.mem⟩ (hg.specializes hyt)
  subst hgy
  have : t = {g} := by rw [← hg.def, hyc.closure_eq]
  rw [this] at hzt
  exact hzt

/-- Let `F` be a noetherian subspace of `X` and `f : Y → X` a continuous map landing in `F`. Then
the preimage under `f` of a connected component of `F` is open and closed. -/
theorem isClopen_preimage_connectedComponentIn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {F : Set X} [TopologicalSpace.NoetherianSpace F] {f : Y → X}
    (hf : Continuous f) (hfF : ∀ y, f y ∈ F) (x : X) :
    IsClopen (f ⁻¹' connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · have : f ⁻¹' connectedComponentIn F x =
        (fun y ↦ (⟨f y, hfF y⟩ : F)) ⁻¹' connectedComponent ⟨x, hx⟩ := by
      ext y
      simp [connectedComponentIn_eq_image hx, hfF]
    rw [this]
    exact ⟨isClosed_connectedComponent.preimage (hf.subtype_mk hfF),
      (isOpen_connectedComponent _).preimage (hf.subtype_mk hfF)⟩
  · rw [connectedComponentIn_eq_empty hx, Set.preimage_empty]
    exact isClopen_empty

/-- **Generisations in a closed set near a point.** In a noetherian quasi-sober space, a point `y`
has an open neighbourhood `W` such that every point of a given closed set `Z` lying in `W` is a
specialisation of a point of `Z` which generalises `y`: remove from the space the finitely many
irreducible components of `Z` which do not contain `y`. -/
theorem exists_isOpen_forall_exists_specializes [QuasiSober α] {Z : Set α} (hZ : IsClosed Z)
    (y : α) : ∃ W : Set α, IsOpen W ∧ y ∈ W ∧ ∀ z ∈ W, z ∈ Z → ∃ g ∈ Z, g ⤳ z ∧ g ⤳ y := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := exists_finite_set_isClosed_irreducible hZ
  have hfin : Set.Finite {t | t ∈ S ∧ y ∉ t} := hSf.subset fun _ ht ↦ ht.1
  have hcl : IsClosed (⋃₀ {t | t ∈ S ∧ y ∉ t}) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht ↦ hSc t ht.1
  refine ⟨(⋃₀ {t | t ∈ S ∧ y ∉ t})ᶜ, hcl.isOpen_compl, fun hy' ↦ ?_, ?_⟩
  · obtain ⟨t, ht, hyt⟩ := hy'
    exact ht.2 hyt
  rintro z hzW ⟨t, ht, hzt⟩
  have hyt : y ∈ t := by
    by_contra hyt
    exact hzW ⟨t, ⟨ht, hyt⟩, hzt⟩
  obtain ⟨g, hg⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  exact ⟨g, ⟨t, ht, hg.mem⟩, hg.specializes hzt, hg.specializes hyt⟩

/-- **Points of a closed set with no proper generisation but one.** In a noetherian quasi-sober
space, let `Z` be a closed set not containing a point `ξ`. Then there are only finitely many
points of `Z` whose only generisations are themselves and `ξ`: each of them is the generic point
of an irreducible component of `Z`. -/
theorem finite_setOf_forall_specializes [QuasiSober α] {Z : Set α} (hZ : IsClosed Z) {ξ : α}
    (hξ : ξ ∉ Z) : {z | z ∈ Z ∧ ∀ c, c ⤳ z → c = z ∨ c = ξ}.Finite := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := exists_finite_set_isClosed_irreducible hZ
  refine (hSf.biUnion' (t := fun t ht ↦ {(hSi t ht).genericPoint})
    fun _ _ ↦ Set.finite_singleton _).subset ?_
  rintro z ⟨⟨t, ht, hzt⟩, hz⟩
  have hg := (hSi t ht).isGenericPoint_genericPoint_closure
  rw [(hSc t ht).closure_eq] at hg
  rcases hz _ (hg.specializes hzt) with h | h
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨t, ht, h.symm⟩
  · exact absurd ⟨t, ht, h ▸ hg.mem⟩ hξ

/-- **Functions constant along specialisations are locally constant** on a noetherian
quasi-sober space: near a point `y` every point is a specialisation of a generalisation of `y`
(`TopologicalSpace.NoetherianSpace.exists_isOpen_forall_exists_specializes`). -/
theorem isLocallyConstant_of_specializes [QuasiSober α] {β : Type*} {f : α → β}
    (hf : ∀ ⦃x y : α⦄, x ⤳ y → f x = f y) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_exists_open f).2 fun y ↦ ?_
  obtain ⟨W, hW, hyW, h⟩ := exists_isOpen_forall_exists_specializes isClosed_univ y
  refine ⟨W, hW, hyW, fun z hz ↦ ?_⟩
  obtain ⟨g, -, hgz, hgy⟩ := h z hz trivial
  exact (hf hgz).symm.trans (hf hgy)

/-- In a noetherian quasi-sober space, a point in the closure of an open set `S` is a
specialisation of a point of `S`. -/
theorem exists_specializes_of_mem_closure [QuasiSober α] {S : Set α} (hS : IsOpen S) {z : α}
    (hz : z ∈ closure S) : ∃ s ∈ S, s ⤳ z := by
  obtain ⟨W, hW, hzW, h⟩ := exists_isOpen_forall_exists_specializes isClosed_closure z
  obtain ⟨z', hz'W, hz'S⟩ := mem_closure_iff.1 hz W hW hzW
  obtain ⟨g, -, hgz', hgz⟩ := h z' hz'W (subset_closure hz'S)
  exact ⟨g, hgz'.mem_open hS hz'S, hgz⟩

end TopologicalSpace.NoetherianSpace
