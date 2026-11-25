/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The module topology of a finite module over a compact ring

Over a compact topological ring `R`, a finite module is compact for its module topology, being a
continuous image of some `Rⁿ`. Hence any Hausdorff topology making a finite `R`-module `M` a
topological module is the module topology (`IsModuleTopology.of_compactSpace`): the identity from
the module topology is a continuous bijection from a compact space to a Hausdorff space.

For instance, the limit topology on `lim_n Mₙ` for a tower of finite `𝒪_E`-modules is the
`ℓ`-adic topology, as soon as `lim_n Mₙ` is a finite `𝒪_E`-module.
-/

@[expose] public section

namespace IsModuleTopology

variable {R M : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module over a compact ring is compact for its module topology. -/
lemma compactSpace_moduleTopology : @CompactSpace M (moduleTopology R M) := by
  let : TopologicalSpace M := moduleTopology R M
  have : IsModuleTopology R M := ⟨rfl⟩
  have := ModuleTopology.continuousAdd R M
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  refine ⟨?_⟩
  rw [← Set.image_univ_of_surjective hf]
  exact isCompact_univ.image (IsModuleTopology.continuous_of_linearMap f)

/-- **A Hausdorff module topology on a finite module over a compact ring is the module
topology.** -/
theorem of_compactSpace [τM : TopologicalSpace M] [T2Space M] [ContinuousAdd M]
    [ContinuousSMul R M] : IsModuleTopology R M := by
  have hc := compactSpace_moduleTopology (R := R) (M := M)
  have hid : @Continuous M M (moduleTopology R M) τM id :=
    continuous_id_iff_le.2 (moduleTopology_le R M)
  let h := @Continuous.homeoOfEquivCompactToT2 M M (moduleTopology R M) τM hc _
    (Equiv.refl M) hid
  have h2 : @Continuous M M τM (moduleTopology R M) id :=
    @Homeomorph.continuous_symm M M (moduleTopology R M) τM h
  exact ⟨le_antisymm (continuous_id_iff_le.1 h2) (moduleTopology_le R M)⟩

end IsModuleTopology
