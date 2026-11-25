/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Group.Pointwise
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible
public import WeilConjectures.RepresentationTheory.FiniteMatrixWitness

/-!
# Irreducibility of continuous representations restricted to large subgroups

Let `ρ` be an irreducible finite-dimensional representation of a topological group `G` over an
algebraically closed topological field `k`, with continuous matrix coefficients. By Burnside's
theorem the operators `ρ(g)` span `End_k(V)`, so `n²` of them, `ρ(g₁), …, ρ(g_{n²})`, have linearly
independent matrices; this is witnessed by a nonzero determinant, which stays nonzero for
`ρ(γ₁), …, ρ(γ_{n²})` with `γᵢ` close to `gᵢ`. Hence there is a neighbourhood `U` of `1` such
that every subgroup `Γ` meeting every left coset `g U` still acts irreducibly
(`Representation.exists_mem_nhds_one_forall_isIrreducible`). This is the topological form of the
finite matrix witness of `lemma-detecting-irreducibility-finite-quotient--1`, used for curve testing
(`corollary-curve-preserving-geometric-irreducibility--1`).

## Main statements

- `Representation.IsIrreducible.of_comp_range`: irreducibility transported along a group
  homomorphism and an equivariant linear isomorphism.
- `Representation.exists_mem_nhds_one_forall_isIrreducible`.
-/

@[expose] public section

open Topology

namespace Representation

section Irreducible

variable {k G H V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- **Transport of irreducibility.** Let `φ : H →* G` and let `e : V ≃ W` intertwine `ρ ∘ φ` with
`σ`. If the image of `φ` acts irreducibly through `ρ`, then `σ` is irreducible. -/
theorem IsIrreducible.of_comp_range [Group G] [Group H] {ρ : Representation k G V}
    {σ : Representation k H W} (φ : H →* G) (e : V ≃ₗ[k] W)
    (he : ∀ h v, e (ρ (φ h) v) = σ h (e v)) (hρ : IsIrreducible (ρ.comp φ.range.subtype)) :
    IsIrreducible σ := by
  rw [isIrreducible_iff] at hρ ⊢
  obtain ⟨hV, h⟩ := hρ
  refine ⟨e.symm.toEquiv.nontrivial, fun S hS ↦ ?_⟩
  have hinv : ∀ g, ∀ v ∈ S.comap e.toLinearMap,
      (ρ.comp φ.range.subtype) g v ∈ S.comap e.toLinearMap := by
    rintro ⟨_, h₀, rfl⟩ v hv
    rw [Submodule.mem_comap] at hv ⊢
    exact (he h₀ v).symm ▸ hS h₀ _ hv
  rcases h _ hinv with h' | h'
  · left
    rw [← Submodule.map_comap_eq_of_surjective e.surjective S, h', Submodule.map_bot]
  · right
    rw [← Submodule.map_comap_eq_of_surjective e.surjective S, h', Submodule.map_top,
      LinearEquiv.range]

end Irreducible

/-- **Irreducibility survives restriction to subgroups meeting every coset of a neighbourhood
of `1`.** Let `ρ` be an irreducible finite-dimensional representation of a topological group `G`
over an algebraically closed topological field `k`, with continuous matrix coefficients. There is
a neighbourhood `U` of `1` such that every subgroup `Γ` meeting every coset `g U` acts
irreducibly. By Burnside's theorem `ρ(g₁), …, ρ(g_{n²})` span `End_k(V)` for some `gᵢ`, as
witnessed by a nonzero determinant of their matrices; the determinant stays nonzero when the
`gᵢ` are replaced by nearby `γᵢ ∈ Γ`. -/
theorem exists_mem_nhds_one_forall_isIrreducible {k G V : Type*} [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T1Space k] [IsAlgClosed k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [IsIrreducible ρ]
    (hρ : ∀ (φ : Module.Dual k V) (v : V), Continuous fun g ↦ φ (ρ g v)) :
    ∃ U ∈ 𝓝 (1 : G), ∀ Γ : Subgroup G, (∀ g, ∃ γ ∈ Γ, g⁻¹ * γ ∈ U) →
      IsIrreducible (ρ.comp Γ.subtype) := by
  classical
  let b := Module.finBasis k V
  obtain ⟨s, hs⟩ := b.exists_det_ne_zero_of_span_range_eq_top ρ
    (span_range_eq_top_of_isIrreducible ρ)
  let n := Module.finrank k V
  let D : (Fin n × Fin n → G) → k := fun h ↦
    (Matrix.of fun q p ↦ LinearMap.toMatrix b b (ρ (s q * h q)) p.1 p.2).det
  have hD : Continuous D := by
    refine Continuous.matrix_det (continuous_matrix fun q p ↦ ?_)
    simp only [Matrix.of_apply, LinearMap.toMatrix_apply]
    exact (hρ (b.coord p.1) (b p.2)).comp (continuous_const.mul (continuous_apply q))
  have h1 : D 1 ≠ 0 := by simpa [D] using hs
  have hU : D ⁻¹' {0}ᶜ ∈ 𝓝 (1 : Fin n × Fin n → G) :=
    hD.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds h1)
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  refine ⟨⋂ q, t q, Filter.iInter_mem.2 fun q ↦ by simpa using ht q, fun Γ hΓ ↦ ?_⟩
  choose γ hγΓ hγU using fun q ↦ hΓ (s q)
  have hdet : (Matrix.of fun q p ↦ LinearMap.toMatrix b b (ρ (γ q)) p.1 p.2).det ≠ 0 := by
    have := hsub (a := fun q ↦ (s q)⁻¹ * γ q) fun q _ ↦ Set.mem_iInter.1 (hγU q) q
    simpa only [D, mul_inv_cancel_left, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff] using this
  have hspan := b.span_range_eq_top_of_det_ne_zero (fun q ↦ ρ (γ q)) hdet
  have : Nontrivial V := (isIrreducible_iff.1 (inferInstance : ρ.IsIrreducible)).1
  refine isIrreducible_of_span_range_eq_top _
    (eq_top_iff.2 (hspan.ge.trans (Submodule.span_mono ?_)))
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨γ q, hγΓ q⟩, rfl⟩

end Representation
