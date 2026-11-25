/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Constructions

/-!
# Density in an open subspace

- `Dense.preimage_val`: a dense subset of a space restricts to a dense subset of any
  open subspace;
- `Dense.preimage_val_inter`: if a dense set is contained in two sets `U` and `V` whose
  union is open, then `U ∩ V` is dense in the subspace `U ∪ V` (blueprint:
  `lemma:nagata-partial-union-overlap-dense`).
-/

@[expose] public section

open Set

variable {X : Type*} [TopologicalSpace X]

/-- A dense subset of a space restricts to a dense subset of any open subspace. -/
protected theorem Dense.preimage_val {D A : Set X} (hD : Dense D) (hA : IsOpen A) :
    Dense ((↑) ⁻¹' D : Set A) :=
  hD.preimage hA.isOpenMap_subtype_val

/-- **Dense overlap of a partial union**: if a dense subset of `X` is contained in two
sets `U` and `V` whose union is open, then `U ∩ V` is dense in the subspace `U ∪ V`.
This is the induction invariant used to glue compactifications along a finite affine
cover with dense total intersection.
(Blueprint: `lemma:nagata-partial-union-overlap-dense`.) -/
theorem Dense.preimage_val_inter {D U V : Set X} (hD : Dense D) (hUV : IsOpen (U ∪ V))
    (hDU : D ⊆ U) (hDV : D ⊆ V) :
    Dense ((↑) ⁻¹' (U ∩ V) : Set ↥(U ∪ V)) :=
  (hD.preimage_val hUV).mono (preimage_mono (subset_inter hDU hDV))

/-- A set is closed as soon as its preimage under each member of a jointly surjective family
of open embeddings is closed. -/
lemma isClosed_of_isOpenEmbedding_cover {Q : Type*} [TopologicalSpace Q] {κ : Type*}
    {Z : κ → Type*} [∀ k, TopologicalSpace (Z k)] (q : ∀ k, Z k → Q)
    (hq : ∀ k, Topology.IsOpenEmbedding (q k)) (hcov : ∀ x : Q, ∃ k y, q k y = x)
    {s : Set Q} (hs : ∀ k, IsClosed (q k ⁻¹' s)) : IsClosed s := by
  rw [← isOpen_compl_iff]
  have hcompl : sᶜ = ⋃ k, q k '' ((q k ⁻¹' s)ᶜ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, y, rfl⟩ := hcov x
      exact Set.mem_iUnion.mpr ⟨k, y, hx, rfl⟩
    · rintro hx
      obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact hy
  rw [hcompl]
  exact isOpen_iUnion fun k ↦ (hq k).isOpenMap _ (hs k).isOpen_compl

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.Topology.Maps.Basic`) -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed map sends closed singletons to closed singletons. -/
lemma IsClosedMap.isClosed_singleton {f : X → Y} (hf : IsClosedMap f)
    {x : X} (hx : IsClosed {x}) :
    IsClosed {f x} := by
  rw [← Set.image_singleton]
  exact hf _ hx
