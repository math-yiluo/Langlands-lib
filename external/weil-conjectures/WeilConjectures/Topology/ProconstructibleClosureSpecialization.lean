/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Constructible
import WeilConjectures.Topology.SpectralSpace.Constructible

/-!
# Specializations in the closure of an intersection of constructible sets

Source: Stacks Project, Topology, Tag 0903, part (1)
(blueprint: lem-weil-pbc-spectral-proconstructible-closure-specialization).
-/

@[expose] public section

universe u v

namespace Topology

/-- In a spectral space, every point in the closure of an intersection of constructible sets
is a specialization of a point of that intersection. Source: Stacks Project, Topology,
Tag 0903, part (1)
(blueprint: lem-weil-pbc-spectral-proconstructible-closure-specialization).

Proof: Each `E a` is clopen in the constructible topology, so their intersection is
closed in that topology. Apply the existing Stacks 0903 (1) theorem
`exists_specializes_of_isClosed_constructibleTopology_of_mem_closure` to obtain a point
`e` of the intersection specializing to `x`. The equivalence
`specializes_iff_mem_closure` gives the required closure membership. -/
theorem exists_mem_iInter_closure_singleton {X : Type u} [TopologicalSpace X]
    [SpectralSpace X] {A : Type v} (E : A → Set X)
    (hE : ∀ a : A, IsConstructible (E a)) {x : X} (hx : x ∈ closure (⋂ a : A, E a)) :
    ∃ e : X, e ∈ (⋂ a : A, E a) ∧ x ∈ closure ({e} : Set X) := by
  have hclosed : IsClosed[constructibleTopology X] (⋂ a : A, E a) := by
    exact @isClosed_iInter X A (constructibleTopology X) E (fun a =>
      (hE a).isClopen_constructibleTopology.1)
  obtain ⟨e, he, hsp⟩ :=
    exists_specializes_of_isClosed_constructibleTopology_of_mem_closure hclosed hx
  exact ⟨e, he, specializes_iff_mem_closure.mp hsp⟩

end Topology
