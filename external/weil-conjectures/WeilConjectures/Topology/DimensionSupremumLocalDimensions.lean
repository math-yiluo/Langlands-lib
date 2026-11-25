/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension as the supremum of local dimensions

Source: Stacks Project, Topology, Lemma Tag 0B7I
(blueprint: lem-weil-pbc-dimension-supremum-local-dimensions).
-/

@[expose] public section

universe u

/-- For every topological space, its Krull dimension is the supremum of its local dimensions.

Source: Stacks Project, Topology, Lemma Tag 0B7I.
Proof:
1. Taking the whole space as an open neighbourhood in the minimum defining local dimension
   (`def-kun-topological-dimension-at-point`) gives `dim_x X ≤ dim X`; taking the supremum
   gives the first inequality. The self-subspace is the original space
   (`def-kun-subspace-topology`).
2. For the converse, the empty space has dimension and empty supremum equal to bottom.
   Otherwise, global dimension is the supremum of lengths of strict chains of irreducible
   closed subsets (`def-kun-topological-krull-dimension`); it suffices to bound each length
   `n ≥ 0` by some local dimension.
3. For a chain `Z₀ ⊊ ... ⊊ Zₙ`, choose `x ∈ Z₀`, which is nonempty by irreducibility
   (`def-weil-irreducible-components`). Every open neighbourhood `U` of `x`, with its subspace
   topology (`def-kun-subspace-topology`), meets each `Zᵢ`. The open-subspace correspondence
   (`lem-weil-pbc-open-subspace-irreducible-closed-correspondence`) makes `Zᵢ ∩ U` irreducible
   closed in `U` and preserves strict inclusions: their closures in `X` are the original `Zᵢ`.
   Thus `dim U ≥ n` by `def-kun-topological-krull-dimension`.
4. Taking the minimum over these neighbourhoods (`def-kun-topological-dimension-at-point`)
   gives `dim_x X ≥ n`. Taking the supremum over chain lengths gives the reverse inequality,
   hence equality. (blueprint: lem-weil-pbc-dimension-supremum-local-dimensions)
-/
theorem topologicalKrullDim_eq_iSup_topologicalKrullDimAt
    (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt x := by
  classical
  apply le_antisymm
  · change Order.krullDim (TopologicalSpace.IrreducibleCloseds X) ≤ _
    unfold Order.krullDim
    refine iSup_le fun p ↦ ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    refine le_trans ?_ (le_iSup (fun x : X ↦ topologicalKrullDimAt x) x)
    unfold topologicalKrullDimAt
    refine le_iInf₂ fun U hxU ↦ ?_
    let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding
      (Subtype.val : U → X) U.isOpenEmbedding'
    let q : LTSeries
        {Z : TopologicalSpace.IrreducibleCloseds X |
          (Subtype.val ⁻¹' (Z : Set X) : Set U).Nonempty} :=
      LTSeries.mk p.length
        (fun i ↦ ⟨p i, ⟨⟨x, hxU⟩, p.head_le i hx⟩⟩)
        (fun i j hij ↦ p.strictMono hij)
    exact Order.LTSeries.length_le_krullDim (q.map e.symm e.symm.strictMono)
  · refine iSup_le fun x ↦ ?_
    exact (iInf₂_le ⊤ trivial).trans
      (topologicalKrullDim_subspace_le X Set.univ)
