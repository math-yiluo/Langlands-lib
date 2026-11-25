/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Constructible
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import Mathlib.Topology.Spectral.Prespectral

/-!
# Constructible intersections in a constructible subspace

Source: literature/stacks-project/topology.tex, Topology, Lemma Tag 09YI
(Lemma 5.15.11, line 2750; proof combines Tags 09YF and 09YH)
(blueprint: lem-weil-pbc-constructible-intersection-in-constructible)
-/

@[expose] public section

universe u

open Set TopologicalSpace

namespace Topology

/--
Let `X` be a topological space with a basis of quasi-compact open subsets, and let
`E` and `E'` be constructible subsets of `X`.  Their intersection, regarded as a
subset of the subspace `E`, is constructible in `E` (Stacks, Tag 09YI).

Proof, following the four steps of the node:
1. By `lem-weil-pbc-constructible-is-retrocompact` (Tag 09YH), `E` is retrocompact:
   its intersection with every quasi-compact open of `X` is quasi-compact.
2. Every quasi-compact open `W` of `E` is `E ∩ W'` for a quasi-compact open `W'`
   of `X`: write `W = E ∩ O` with `O` open, cover `O` by quasi-compact basis opens,
   and take a finite subcover of `W`. Their finite union is the required `W'`.
   Compactness in the subspace agrees with compactness of its image in `X`.
3. If `V` is retrocompact open in `X`, then `V ∩ E` is retrocompact open in `E`:
   for `W = E ∩ W'` as in step 2, `V ∩ W'` is quasi-compact open in `X`, so
   `E ∩ (V ∩ W')` is quasi-compact by step 1. These are the details of Tag 09YF.
4. The inclusion `E → X` is continuous and pulls retrocompact opens back to
   retrocompact opens by step 3. Apply `lem-weil-pbc-constructible-preimage`,
   Mathlib's `IsConstructible.preimage` (Tag 005I), to `E'`. Its preimage is exactly
   the trace `E ∩ E'` in `E`.
(blueprint: lem-weil-pbc-constructible-intersection-in-constructible)
-/
theorem isConstructible_inter_subtype
    {X : Type u} [TopologicalSpace X]
    (hBasis : IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U})
    {E E' : Set X}
    (hE : IsConstructible E) (hE' : IsConstructible E') :
    IsConstructible ((Subtype.val : E → X) ⁻¹' E') := by
  let : PrespectralSpace X := ⟨hBasis⟩
  apply hE'.preimage continuous_subtype_val
  intro V hVo hVr W hWc hWo
  obtain ⟨O, hOo, hOW⟩ := IsEmbedding.subtypeVal.isInducing.isOpen_iff.mp hWo
  obtain ⟨U, hUc, hUo, hWU, hUO⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (hWc.image continuous_subtype_val) hOo (by
        rintro _ ⟨x, hx, rfl⟩
        change x ∈ Subtype.val ⁻¹' O
        rwa [hOW])
  have hUW : (Subtype.val : E → X) ⁻¹' U = W := by
    apply Subset.antisymm
    · intro x hx
      rw [← hOW]
      exact hUO hx
    · intro x hx
      exact hWU ⟨x, hx, rfl⟩
  rw [← hUW, ← preimage_inter, IsEmbedding.subtypeVal.isCompact_iff]
  simpa only [Subtype.image_preimage_coe, inter_comm] using
    hE.isRetrocompact (hVr hUc hUo) (hVo.inter hUo)

end Topology
