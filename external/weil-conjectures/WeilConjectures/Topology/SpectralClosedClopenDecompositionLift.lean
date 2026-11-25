/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.Topology.ProconstructibleClosureSpecialization
import WeilConjectures.Topology.SpectralGeneralizations

/-! # Lifting clopen decompositions from a closed spectral subspace

Source: Stacks Project, Etale Cohomology, Tag 0CAM, `lemma-connected-topological`
(blueprint: lem-weil-pbc-spectral-closed-clopen-decomposition-lift).
-/

@[expose] public section

universe u

open Set TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Etale Cohomology, Tag 0CAM, `lemma-connected-topological`.
(blueprint: lem-weil-pbc-spectral-closed-clopen-decomposition-lift)

A closed decomposition of `Z` extends to the spectral space `X` when `Z` meets each point
closure in a nonempty connected set.

Proof:
1. The relatively closed pieces `Z₁` and `Z₂` are closed in `X` and quasi-compact, since `X`
   is spectral (`def-weil-spectral-space`).
2. Let `Wᵢ` consist of points whose closure meets `Zᵢ`. By
   `lem-weil-pbc-spectral-generalizations-of-quasi-compact`, each is an intersection of
   quasi-compact opens. These opens are retrocompact by quasi-separatedness, hence
   constructible (`def-weil-constructible-subset`). Thus `Wᵢ` is proconstructible.
3. The nonempty connected intersection of each point closure with `Z` meets exactly one
   piece (`def-weil-connected-scheme`), so `W₁` and `W₂` are disjoint and cover `X`.
4. For `x` in the closure of `W₁`,
   `lem-weil-pbc-spectral-proconstructible-closure-specialization` supplies `x₁ ∈ W₁`
   specializing to `x`. Choose a point of `Z` in the closure of `x`. It also lies in the
   closure of `x₁`, which cannot meet `Z₂` by step 3. The point therefore lies in `Z₁`,
   giving `x ∈ W₁`. Hence `W₁` is closed; symmetrically `W₂` is closed.
5. Set `Xᵢ = Wᵢ`. Each `Zᵢ` lies in `Wᵢ`, since a point lies in its own closure.
   Conversely, step 3 excludes points of the other piece from `Z ∩ Wᵢ`. Thus
   `Zᵢ = Z ∩ Xᵢ`, and the required closed decomposition follows. -/
theorem spectral_closed_clopen_decomposition_lift
    (X : TopCat.{u}) [SpectralSpace X]
    (Z : Set X) (hZ : IsClosed Z)
    (hconn : ∀ x : X, ConnectedSpace (↥(Z ∩ closure ({x} : Set X))))
    (Z₁ Z₂ : Set (↥Z))
    (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂)
    (hpart : Z₁ ∪ Z₂ = Set.univ) (hdisj : Disjoint Z₁ Z₂) :
    ∃ X₁ X₂ : Set X,
      IsClosed X₁ ∧ IsClosed X₂ ∧ Disjoint X₁ X₂ ∧ X₁ ∪ X₂ = Set.univ ∧
      (Subtype.val '' Z₁) = Z ∩ X₁ ∧ (Subtype.val '' Z₂) = Z ∩ X₂ := by
  classical
  let E₁ : Set X := Subtype.val '' Z₁
  let E₂ : Set X := Subtype.val '' Z₂
  have hE₁ : IsClosed E₁ := hZ.isClosedMap_subtype_val _ hZ₁
  have hE₂ : IsClosed E₂ := hZ.isClosedMap_subtype_val _ hZ₂
  have hEpart : E₁ ∪ E₂ = Z := by
    simp only [E₁, E₂, ← image_union, hpart, image_univ, Subtype.range_coe]
  have hEdisj : Disjoint E₁ E₂ := by
    exact hdisj.image Subtype.val_injective.injOn (subset_univ _) (subset_univ _)
  have hEsub₁ : E₁ ⊆ Z := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hEsub₂ : E₂ ⊆ Z := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  let W : Set X → Set X := fun E ↦ {x | (closure ({x} : Set X) ∩ E).Nonempty}
  have hWself (E : Set X) : E ⊆ W E := by
    intro x hx
    exact ⟨x, subset_closure (mem_singleton x), hx⟩
  have hC (x : X) : IsConnected (Z ∩ closure ({x} : Set X)) :=
    isConnected_iff_connectedSpace.mpr (hconn x)
  have hWpart : W E₁ ∪ W E₂ = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨z, hzZ, hzx⟩ := (hC x).nonempty
    have hz : z ∈ E₁ ∪ E₂ := hEpart.symm ▸ hzZ
    rcases hz with hz | hz
    · exact Or.inl ⟨z, hzx, hz⟩
    · exact Or.inr ⟨z, hzx, hz⟩
  have hWdisj : Disjoint (W E₁) (W E₂) := by
    apply Set.disjoint_left.mpr
    intro x hx₁ hx₂
    obtain ⟨z₁, hz₁x, hz₁⟩ := hx₁
    obtain ⟨z₂, hz₂x, hz₂⟩ := hx₂
    have hcover : Z ∩ closure ({x} : Set X) ⊆ E₁ ∪ E₂ := by
      intro z hz
      exact hEpart.symm ▸ hz.1
    obtain ⟨z, _, hz₁', hz₂'⟩ := isPreconnected_closed_iff.mp (hC x).isPreconnected
      E₁ E₂ hE₁ hE₂ hcover
      ⟨z₁, ⟨hEsub₁ hz₁, hz₁x⟩, hz₁⟩ ⟨z₂, ⟨hEsub₂ hz₂, hz₂x⟩, hz₂⟩
    exact Set.disjoint_left.mp hEdisj hz₁' hz₂'
  -- A compact piece has a proconstructible generalization set.
  have hWrep (E : Set X) (hE : IsCompact E) :
      W E = ⋂ U : {U : Set X | IsOpen U ∧ IsCompact U ∧ E ⊆ U}, (U : Set X) := by
    have h := (Topology.generalizations_isCompact_sInter_isCompactOpen X E hE).2
    simpa only [W, Set.nonempty_iff_ne_empty, Set.sInter_eq_iInter] using h
  -- Specialization preserves the chosen piece because the other piece is excluded.
  have hWclosed (E F : Set X) (hE : IsCompact E)
      (hpart' : E ∪ F = Z) (hdisj' : Disjoint (W E) (W F)) : IsClosed (W E) := by
    apply isClosed_of_closure_subset
    intro x hx
    let A := {U : Set X | IsOpen U ∧ IsCompact U ∧ E ⊆ U}
    have hrep := hWrep E hE
    have hx' : x ∈ closure (⋂ U : A, (U : Set X)) := by
      rw [hrep] at hx
      exact hx
    obtain ⟨e, he, hxe⟩ := Topology.exists_mem_iInter_closure_singleton
      (fun U : A ↦ (U : Set X)) (fun U ↦ U.property.2.1.isConstructible U.property.1) hx'
    have heW : e ∈ W E := by
      rwa [hrep]
    obtain ⟨z, hzZ, hzx⟩ := (hC x).nonempty
    have hze : z ∈ closure ({e} : Set X) :=
      (specializes_iff_mem_closure.mpr hxe).closure_subset hzx
    have hz : z ∈ E ∪ F := hpart'.symm ▸ hzZ
    rcases hz with hz | hz
    · exact ⟨z, hzx, hz⟩
    · exact False.elim (Set.disjoint_left.mp hdisj' heW ⟨z, hze, hz⟩)
  have hW₁ : IsClosed (W E₁) := hWclosed E₁ E₂ hE₁.isCompact hEpart hWdisj
  have hW₂ : IsClosed (W E₂) :=
    hWclosed E₂ E₁ hE₂.isCompact (union_comm E₂ E₁ ▸ hEpart) hWdisj.symm
  have hrestrict (E F : Set X) (hsub : E ⊆ Z) (hpart' : E ∪ F = Z)
      (hdisj' : Disjoint (W E) (W F)) : E = Z ∩ W E := by
    apply subset_antisymm
    · intro z hz
      exact ⟨hsub hz, hWself E hz⟩
    · intro z hz
      have hzpart : z ∈ E ∪ F := hpart'.symm ▸ hz.1
      rcases hzpart with hzE | hzF
      · exact hzE
      · exact False.elim (Set.disjoint_left.mp hdisj' hz.2 (hWself F hzF))
  exact ⟨W E₁, W E₂, hW₁, hW₂, hWdisj, hWpart,
    hrestrict E₁ E₂ hEsub₁ hEpart hWdisj,
    hrestrict E₂ E₁ hEsub₂ (union_comm E₂ E₁ ▸ hEpart) hWdisj.symm⟩

end TopCat
