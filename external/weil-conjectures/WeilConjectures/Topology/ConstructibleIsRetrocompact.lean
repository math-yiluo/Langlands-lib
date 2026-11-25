/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Constructible

/-!
# Constructible subsets are retrocompact

Source: Stacks Project, Topology, Lemma 5.15.10 (Tag 09YH)
(blueprint: lem-weil-pbc-constructible-is-retrocompact).
-/

@[expose] public section

universe u

namespace Topology

/-- Every constructible subset of a topological space is retrocompact.
Source: Stacks Project, Topology, Lemma 5.15.10 (Tag 09YH)
(blueprint: lem-weil-pbc-constructible-is-retrocompact).

Proof: By `def-weil-constructible-subset`, write the constructible set as a finite union
of pieces `U ∩ Vᶜ`, where `U` and `V` are retrocompact open sets; the empty union is allowed.
For any quasi-compact open `W`, distribute intersection with `W` over this union.
For each piece, retrocompactness of `U` makes `U ∩ W` quasi-compact. Since `V` is open,
`(U ∩ W) ∩ Vᶜ` is closed in that quasi-compact subspace, hence quasi-compact by
`lem-weil-pbc-closed-in-quasi-compact` (Stacks Tag 005C). The induced topology agrees
with the topology induced directly from the ambient space. Finally, a finite union of
quasi-compact subsets is quasi-compact: choose a finite subcover for each piece and take
the union of these finitely many finite subcovers. For the empty union use the empty
subcover. Thus the intersection of the constructible set with every quasi-compact open
`W` is quasi-compact, which is retrocompactness. -/
theorem IsConstructible.isRetrocompact {X : Type u} [TopologicalSpace X] {E : Set X}
    (hE : IsConstructible E) : IsRetrocompact E := by
  induction E, hE using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, IsRetrocompact.empty⟩
  | top_mem => exact ⟨isOpen_univ, IsRetrocompact.univ⟩
  | sdiff U hU V hV =>
    intro W hWcomp hWopen
    simpa only [Set.sdiff_eq, Set.inter_right_comm] using (hU.2 hWcomp hWopen).diff hV.1
  | sup s _ t _ hs ht => exact hs.union ht

end Topology
