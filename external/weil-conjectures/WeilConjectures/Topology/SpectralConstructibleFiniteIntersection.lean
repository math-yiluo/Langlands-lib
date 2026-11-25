/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.Basic
import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Finite intersections of constructible subsets of a spectral space

Source: literature/stacks-project/topology.tex, Topology, Lemma 0901 and the
paragraph before it (blueprint: lem-weil-pbc-spectral-constructible-finite-intersection).

## Main statements

- `finite_subfamily_iInter_eq_empty_of_isConstructible`: a family of constructible
  subsets with empty intersection has a finite subfamily with empty intersection.
-/

@[expose] public section

universe u v

open Set Topology

/-- In a spectral space, a family of constructible subsets with empty intersection
has a finite subfamily with empty intersection.

Source: literature/stacks-project/topology.tex, Topology, Lemma 0901 and the
paragraph before it (blueprint: lem-weil-pbc-spectral-constructible-finite-intersection).
Proof: Put the constructible topology on the spectral space. Constructible sets
are closed there, and that topology is quasi-compact. The complements therefore
form an open cover, which has a finite subcover; taking complements gives the
finite subfamily. The empty space is handled by the empty finite subfamily.
-/
theorem finite_subfamily_iInter_eq_empty_of_isConstructible
    (T : Type u) [TopologicalSpace T] [SpectralSpace T]
    (A : Type v) (E : A → Set T)
    (hE : ∀ a, IsConstructible (E a))
    (hEmpty : (⋂ a, E a) = ∅) :
    ∃ A₀ : Finset A, (⋂ a ∈ A₀, E a) = ∅ := by
  let E' : A → Set (WithConstructibleTopology T) := fun a =>
    {x | WithTopology.ofTopology x ∈ E a}
  have hclosed : ∀ a, IsClosed (E' a) := fun a => by
    rw [WithConstructibleTopology.isClosed_iff]
    exact (@Topology.IsConstructible.isClopen_constructibleTopology T _ inferInstance _
      (hE a)).1
  have hcompact : IsCompact (Set.univ : Set (WithConstructibleTopology T)) := isCompact_univ
  have hEmpty' : (⋂ a, E' a) = ∅ := by
    ext x
    constructor
    · intro hx
      have hx' : x.ofTopology ∈ ⋂ a, E a := by
        refine Set.mem_iInter.mpr fun a => ?_
        exact (Set.mem_iInter.mp hx a)
      rw [hEmpty] at hx'
      exact hx'
    · intro hx
      exact hx.elim
  obtain ⟨A₀, hA₀⟩ :=
    hcompact.elim_finite_subfamily_closed E' hclosed (by simpa using hEmpty')
  refine ⟨A₀, ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let y : WithConstructibleTopology T := WithTopology.toTopology (constructibleTopology T) x
  have hy : y ∈ ⋂ a ∈ A₀, E' a := by
    simp only [Set.mem_iInter]
    intro a ha
    simpa [E', y] using Set.mem_iInter.mp (Set.mem_iInter.mp hx a) ha
  exact Set.disjoint_left.mp hA₀ (Set.mem_univ y) hy
