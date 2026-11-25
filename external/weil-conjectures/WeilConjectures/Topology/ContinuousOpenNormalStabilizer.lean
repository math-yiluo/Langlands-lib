/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Open normal stabilizers of continuous functions on profinite groups

Source: Stacks Project, etale-cohomology.tex, Tag 04JP,
definition-G-module-continuous; the profinite compactness argument is supplied in the blueprint
(blueprint: lem-exc-coinduced-functions-open-stabilizer).
-/

@[expose] public section

universe u v

namespace ProfiniteGrp

/-- (blueprint: lem-exc-coinduced-functions-open-stabilizer) A continuous map from a profinite
group to a discrete space is invariant under right multiplication by some open normal subgroup.

Step 1: each fibre of `f` is open, and the fibres cover compact `G`. For every `x`, the
open-subgroup neighbourhood basis at one (from the finite discrete quotients of a profinite
group) gives an open subgroup `V x` with `x * V x` in the fibre of `f x`. A finite collection
of these cosets covers `G`; the intersection `V` of their subgroups is open and satisfies
`f (x * v) = f x` for all `x` and `v ∈ V`.

Step 2: an open subgroup of compact `G` has finite index. Intersecting the finitely many
conjugates of `V` over representatives of `G / V` gives an open normal subgroup `U ⊆ V`, and
the same right-invariance holds for `U`.

Source: Stacks Project, etale-cohomology.tex, Tag 04JP, with the group argument supplied in the
    blueprint.
-/
theorem exists_openNormalSubgroup_right_invariant
    (G : ProfiniteGrp.{u}) (S : Type v) [TopologicalSpace S] [DiscreteTopology S]
    (f : G → S) (hf : Continuous f) :
    ∃ U : OpenNormalSubgroup G, ∀ x : G, ∀ a : G, a ∈ U → f (x * a) = f x := by
  let W : G → Set G := fun x => {a | f (x * a) = f x}
  have hWopen : ∀ x : G, IsOpen (W x) := by
    intro x
    have hs : IsOpen ({f x} : Set S) := isOpen_discrete _
    have hp : IsOpen (f ⁻¹' ({f x} : Set S)) := hf.isOpen_preimage _ hs
    have hc : Continuous (fun a : G => x * a) := continuous_const_mul x
    simpa [W, Set.preimage, Set.mem_ofPred_eq] using hc.isOpen_preimage _ hp
  have hone : ∀ x : G, (1 : G) ∈ W x := by
    intro x
    simp [W]
  choose H hH using fun x =>
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hWopen x) (hone x)
  have hcover : (Set.univ : Set G) ⊆ ⋃ x : G, (fun a => x * a) '' (H x : Set G) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    refine ⟨1, (H x).one_mem, by simp⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : G => (fun a => x * a) '' (H x : Set G))
    (fun x => (Homeomorph.mulLeft x).isOpenMap _ (H x).isOpen) hcover
  have htne : t.Nonempty := by
    have h1 := ht (Set.mem_univ (1 : G))
    rcases Set.mem_iUnion₂.mp h1 with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  let V : OpenNormalSubgroup G := t.inf' htne H
  refine ⟨V, ?_⟩
  intro x a ha
  have hxa := ht (Set.mem_univ x)
  rcases Set.mem_iUnion₂.mp hxa with ⟨y, hy, hxy⟩
  rcases hxy with ⟨b, hb, rfl⟩
  have haH : a ∈ H y := by
    exact (Finset.inf'_le H hy) ha
  have hba : b * a ∈ H y := (H y).mul_mem hb haH
  have hfb : f (y * b) = f y := hH y hb
  have hfba : f (y * (b * a)) = f y := hH y hba
  simpa [mul_assoc] using hfba.trans hfb.symm

end ProfiniteGrp
