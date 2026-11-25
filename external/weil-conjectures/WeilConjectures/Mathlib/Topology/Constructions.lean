/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Constructions

/-!
# Closedness against a closed set inside an open set

A subset of a topological space which is contained in a closed set lying inside an open set is
closed as soon as it is closed in that open set. This is the standard way of upgrading a
relatively closed graph to a closed graph.

## Main results

* `isClosed_of_isClosed_preimage_subtypeVal`
-/

@[expose] public section

/-- A subset of a closed set contained in an open set is closed as soon as it is closed in
that open set. -/
theorem _root_.isClosed_of_isClosed_preimage_subtypeVal {α : Type*} [TopologicalSpace α]
    {Ω : Set α} (hΩ : IsOpen Ω) {N T : Set α} (hN : IsClosed N) (hNΩ : N ⊆ Ω) (hTN : T ⊆ N)
    (hT : IsClosed (((↑) : Ω → α) ⁻¹' T)) : IsClosed T := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  have hxΩ : x ∈ Ω := hNΩ (hN.closure_subset (closure_mono hTN hx))
  have h1 : (⟨x, hxΩ⟩ : Ω) ∈ closure (((↑) : Ω → α) ⁻¹' T) :=
    hΩ.isOpenMap_subtype_val.preimage_closure_subset_closure_preimage
      (f := ((↑) : Ω → α)) hx
  rwa [hT.closure_eq] at h1

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.Topology.Constructions`) -/

-- after `Topology.isOpenEmbedding_sigmaMap`
variable {α β : Type*} [TopologicalSpace α] [b : TopologicalSpace β]
theorem Prod.continuous_toSigma [DiscreteTopology α] : Continuous (Prod.toSigma : α × β → _) := by
  refine ⟨fun U hU ↦ ?_⟩
  rw [isOpen_prod_iff]
  rw [isOpen_sigma_iff] at hU
  intro a b hab
  use {a}, ((Sigma.mk (β := fun _ ↦ β) a) ⁻¹' U)
  refine ⟨by simp, hU a, by simp, hab, fun t hT ↦ ?_⟩
  simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage] at hT
  simpa [Prod.toSigma, ← hT.1] using hT.2

