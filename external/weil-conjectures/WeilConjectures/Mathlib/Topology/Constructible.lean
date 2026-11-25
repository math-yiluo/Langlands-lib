/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace

/-!
# Dense constructible sets contain a dense open

A constructible set dense in an irreducible closed set `t` contains a nonempty open subset of `t`.
In a Noetherian space, every nonempty constructible set contains a nonempty open subset of its
closure.

The other affine-geometric facts of the blueprint subsection are in Mathlib: the spectrum of a
finitely generated algebra over a field is Noetherian (`Algebra.FiniteType.isNoetherianRing` and
`PrimeSpectrum.instNoetherianSpace`), a Noetherian space has finitely many irreducible components
(`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`), and the image of a constructible
set under a morphism of finite presentation is constructible (Chevalley,
`PrimeSpectrum.isConstructible_comap_image`).

## Main results

- `Topology.IsConstructible.exists_isOpen_inter_subset_or`: over an irreducible set, a
  constructible set generically contains it or misses it.
- `exists_isOpen_inter_subset_of_isConstructible`
- `exists_isOpen_inter_closure_subset_of_isConstructible`

## Blueprint

- `det-i-geometry`: dense constructible sets.
- `lem-wf-affine-constructible-open`, clause (2): open pieces of constructible sets.
-/

@[expose] public section

open Topology

/-- Over an irreducible set `t`, a constructible set `s` is generically either everything or
nothing: some open set meeting `t` has its trace on `t` contained in `s` or in `sᶜ`. -/
theorem Topology.IsConstructible.exists_isOpen_inter_subset_or {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsConstructible s) (hirr : IsIrreducible t) :
    (∃ u : Set X, IsOpen u ∧ (u ∩ t).Nonempty ∧ u ∩ t ⊆ s) ∨
      ∃ u : Set X, IsOpen u ∧ (u ∩ t).Nonempty ∧ u ∩ t ⊆ sᶜ := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases hUt : (U ∩ t).Nonempty
    · exact .inl ⟨U, hU, hUt, Set.inter_subset_left⟩
    · refine .inr ⟨Set.univ, isOpen_univ, by simpa using hirr.nonempty, fun x hx hxU ↦ ?_⟩
      exact hUt ⟨x, hxU, hx.2⟩
  | union s _ s' _ h h' =>
    rcases h with ⟨u, hu, hut, hus⟩ | ⟨u, hu, hut, hus⟩
    · exact .inl ⟨u, hu, hut, hus.trans Set.subset_union_left⟩
    rcases h' with ⟨u', hu', hut', hus'⟩ | ⟨u', hu', hut', hus'⟩
    · exact .inl ⟨u', hu', hut', hus'.trans Set.subset_union_right⟩
    obtain ⟨x, hxt, hxu, hxu'⟩ := hirr.2 u u' hu hu' (by rwa [Set.inter_comm])
      (by rwa [Set.inter_comm])
    refine .inr ⟨u ∩ u', hu.inter hu', ⟨x, ⟨hxu, hxu'⟩, hxt⟩, ?_⟩
    rintro y ⟨⟨hyu, hyu'⟩, hyt⟩ (hy | hy)
    exacts [hus ⟨hyu, hyt⟩ hy, hus' ⟨hyu', hyt⟩ hy]
  | compl s _ h => simpa only [compl_compl, or_comm] using h

/-- A constructible set `s` dense in an irreducible closed set `t` contains a nonempty open subset
of `t`. (blueprint: `det-i-geometry`)

The Noetherian hypothesis is not needed for the proof. -/
theorem exists_isOpen_inter_subset_of_isConstructible {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {s t : Set X} (hs : IsConstructible s) (_ht : IsClosed t)
    (hirr : IsIrreducible t) (hst : closure s = t) :
    ∃ u : Set X, IsOpen u ∧ (u ∩ t).Nonempty ∧ u ∩ t ⊆ s := by
  refine (hs.exists_isOpen_inter_subset_or hirr).resolve_right ?_
  rintro ⟨u, hu, ⟨x, hxu, hxt⟩, hus⟩
  have hsu : s ⊆ uᶜ := fun y hys hyu ↦ hus ⟨hyu, hst ▸ subset_closure hys⟩ hys
  exact (closure_minimal hsu hu.isClosed_compl) (hst ▸ hxt) hxu

/-- Blueprint `lem-wf-affine-constructible-open`, clause (2): in a Noetherian space, a nonempty
constructible set `s` contains a nonempty open subset of its closure.

Write `closure s` as a finite union of irreducible closed sets and pick a maximal one `C`. The
complement `Ω` of the members not containing `C` is open, and `Ω ∩ closure s` is a nonempty open
subset of `C`. Then `s ∩ Ω` is a constructible set dense in `C`, and
`IsConstructible.exists_isOpen_inter_subset_or` gives the open set. -/
theorem exists_isOpen_inter_closure_subset_of_isConstructible {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {s : Set X} (hs : IsConstructible s)
    (hne : s.Nonempty) :
    ∃ u : Set X, IsOpen u ∧ (u ∩ closure s).Nonempty ∧ u ∩ closure s ⊆ s := by
  obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure (s := s))
  obtain ⟨C, hC⟩ := hSf.exists_maximal (by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hne
    have := subset_closure hx
    simp [hS, h] at this)
  set T := {D ∈ S | ¬C ⊆ D}
  have hTf : T.Finite := hSf.subset fun _ h ↦ h.1
  have hΩ : IsOpen (⋃₀ T)ᶜ :=
    (Set.sUnion_eq_biUnion ▸ hTf.isClosed_biUnion fun D hD ↦ hSc D hD.1).isOpen_compl
  have hCΩ : ((⋃₀ T)ᶜ ∩ C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty,
      Set.disjoint_compl_left_iff_subset] at h
    obtain ⟨D, hD, hCD⟩ := (isIrreducible_iff_sUnion_isClosed.1 (hSi C hC.prop)) hTf.toFinset
      (by simpa using fun D hD ↦ hSc D hD.1) (by simpa using h)
    exact (hTf.mem_toFinset.1 hD).2 hCD
  have hΩZ : (⋃₀ T)ᶜ ∩ closure s ⊆ C := by
    rintro x ⟨hxT, hxZ⟩
    rw [hS] at hxZ
    obtain ⟨D, hD, hxD⟩ := hxZ
    by_cases hCD : C ⊆ D
    · exact (hC.eq_of_subset hD hCD).symm ▸ hxD
    · exact absurd ⟨D, ⟨hD, hCD⟩, hxD⟩ hxT
  have hCZ : C ⊆ closure s := hS ▸ Set.subset_sUnion_of_mem hC.prop
  have hdense : closure (s ∩ (⋃₀ T)ᶜ) = C := by
    refine subset_antisymm (closure_minimal (fun x hx ↦ hΩZ ⟨hx.2, subset_closure hx.1⟩)
      (hSc C hC.prop)) ?_
    have h1 : C ∩ (⋃₀ T)ᶜ ⊆ closure (s ∩ (⋃₀ T)ᶜ) := fun x hx ↦
      hΩ.closure_inter ⟨hCZ hx.1, hx.2⟩
    calc C ⊆ closure (C ∩ (⋃₀ T)ᶜ) :=
          subset_closure_inter_of_isPreirreducible_of_isOpen (hSi C hC.prop).2 hΩ
            (by rwa [Set.inter_comm])
      _ ⊆ _ := closure_minimal h1 isClosed_closure
  have hsΩ : IsConstructible (s ∩ (⋃₀ T)ᶜ) :=
    hs.inter ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible hΩ)
  obtain ⟨u, hu, hut, hus⟩ := exists_isOpen_inter_subset_of_isConstructible hsΩ (hSc C hC.prop)
    (hSi C hC.prop) hdense
  obtain ⟨x, hxu, hxC⟩ := hut
  refine ⟨u ∩ (⋃₀ T)ᶜ, hu.inter hΩ, ⟨x, ⟨hxu, (hus ⟨hxu, hxC⟩).2⟩, hCZ hxC⟩, ?_⟩
  rintro y ⟨⟨hyu, hyΩ⟩, hyZ⟩
  exact (hus ⟨hyu, hΩZ ⟨hyΩ, hyZ⟩⟩).1

section Noetherian

open Set TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- In a Noetherian space every set is retrocompact. -/
lemma TopologicalSpace.NoetherianSpace.isRetrocompact [NoetherianSpace X] (s : Set X) :
    IsRetrocompact s :=
  fun _ _ _ ↦ NoetherianSpace.isCompact _

/-- In a Noetherian space open sets are constructible. -/
lemma IsOpen.isConstructible_of_noetherianSpace [NoetherianSpace X] {s : Set X} (hs : IsOpen s) :
    IsConstructible s :=
  (NoetherianSpace.isRetrocompact s).isConstructible hs

/-- In a Noetherian space closed sets are constructible. -/
lemma IsClosed.isConstructible_of_noetherianSpace [NoetherianSpace X] {s : Set X}
    (hs : IsClosed s) : IsConstructible s :=
  isConstructible_compl.1 hs.isOpen_compl.isConstructible_of_noetherianSpace

/-- In a Noetherian space locally closed sets are constructible. -/
lemma IsLocallyClosed.isConstructible_of_noetherianSpace [NoetherianSpace X] {s : Set X}
    (hs : IsLocallyClosed s) : IsConstructible s := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  exact hU.isConstructible_of_noetherianSpace.inter hZ.isConstructible_of_noetherianSpace

/-- The image of a constructible set under an embedding with locally closed range into a
Noetherian space is constructible. -/
lemma Topology.IsConstructible.image_of_isEmbedding [NoetherianSpace Y] {f : X → Y}
    (hf : IsEmbedding f)
    (hr : IsLocallyClosed (range f)) {s : Set X} (hs : IsConstructible s) :
    IsConstructible (f '' s) := by
  obtain ⟨U, Z, hU, hZ, hUZ⟩ := hr
  have hfU (x : X) : f x ∈ U := (hUZ ▸ mem_range_self x : f x ∈ U ∩ Z).1
  let g : X → U := fun x ↦ ⟨f x, hfU x⟩
  have hg : IsClosedEmbedding g := by
    refine ⟨IsEmbedding.codRestrict hf _ _, ?_⟩
    have : range g = Subtype.val ⁻¹' Z := by
      ext ⟨y, hy⟩
      simp only [mem_range, mem_preimage, g]
      constructor
      · rintro ⟨x, hx⟩
        have := (hUZ ▸ mem_range_self x : f x ∈ U ∩ Z).2
        rwa [show f x = y from congrArg Subtype.val hx] at this
      · intro hyZ
        obtain ⟨x, rfl⟩ : y ∈ range f := hUZ ▸ ⟨hy, hyZ⟩
        exact ⟨x, rfl⟩
    rw [this]
    exact hZ.preimage continuous_subtype_val
  have h1 := hs.image_of_isClosedEmbedding hg (NoetherianSpace.isRetrocompact _)
  have h2 := h1.image_of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal
    (NoetherianSpace.isRetrocompact _)
  rwa [← image_comp] at h2

/-- In a Noetherian space, a constructible set containing the generic point `ξ` of an
irreducible component contains an open neighbourhood of `ξ`: it generically contains the
component, and the complement of the other, finitely many, components is an open neighbourhood
of `ξ` inside the component. -/
theorem Topology.IsConstructible.exists_isOpen_mem_subset [NoetherianSpace X] {s : Set X}
    (hs : IsConstructible s) {ξ : X} (hξ : closure {ξ} ∈ irreducibleComponents X)
    (hξs : ξ ∈ s) : ∃ u : Set X, IsOpen u ∧ ξ ∈ u ∧ u ⊆ s := by
  set T := closure ({ξ} : Set X)
  have hirr : IsIrreducible T := isIrreducible_singleton.closure
  -- an open set meeting `T` contains `ξ`
  have hmem : ∀ u : Set X, IsOpen u → (u ∩ T).Nonempty → ξ ∈ u := fun u hu ⟨x, hxu, hxT⟩ ↦
    (specializes_iff_mem_closure.2 hxT).mem_open hu hxu
  -- the complement `Ω` of the other components is an open neighbourhood of `ξ` inside `T`
  set C := {D ∈ irreducibleComponents X | D ≠ T}
  have hCf : C.Finite := NoetherianSpace.finite_irreducibleComponents.subset fun _ h ↦ h.1
  have hΩ : IsOpen (⋃₀ C)ᶜ := (Set.sUnion_eq_biUnion ▸ hCf.isClosed_biUnion fun D hD ↦
    isClosed_of_mem_irreducibleComponents D hD.1).isOpen_compl
  have hξΩ : ξ ∈ (⋃₀ C)ᶜ := by
    rintro ⟨D, ⟨hD, hDT⟩, hξD⟩
    have hTD : T ⊆ D := closure_minimal (Set.singleton_subset_iff.2 hξD)
      (isClosed_of_mem_irreducibleComponents D hD)
    exact hDT ((hξ.2 (hD.1) hTD).antisymm hTD)
  have hΩT : (⋃₀ C)ᶜ ⊆ T := by
    intro y hy
    obtain ⟨D, hD, hyD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
      isIrreducible_singleton
    by_cases hDT : D = T
    · exact hDT ▸ hyD (Set.mem_singleton y)
    · exact absurd ⟨D, ⟨hD, hDT⟩, hyD (Set.mem_singleton y)⟩ hy
  rcases hs.exists_isOpen_inter_subset_or hirr with ⟨u, hu, hut, hus⟩ | ⟨u, hu, hut, hus⟩
  · exact ⟨u ∩ (⋃₀ C)ᶜ, hu.inter hΩ, ⟨hmem u hu hut, hξΩ⟩,
      fun y hy ↦ hus ⟨hy.1, hΩT hy.2⟩⟩
  · exact absurd hξs (hus ⟨hmem u hu hut, subset_closure (Set.mem_singleton ξ)⟩)

end Noetherian
