/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!

# Constructible sets avoiding the generic point of a curve

Let `X` be a topological space with a generic point `η`.

* A constructible subset `s` of `X` not containing `η` lies in a closed subset not containing `η`
  (`Topology.IsConstructible.exists_isClosed_superset_of_notMem`).
* If moreover `X` is a quasi-sober noetherian space all of whose points other than `η` are closed
  (e.g. an irreducible noetherian scheme of dimension one), then such a set is a finite set of
  closed points (`Topology.IsConstructible.exists_finset_of_notMem`).

This is used in the finite-support step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`): a constructible subset of a line which omits
the generic point is a finite set of closed points.

-/

@[expose] public section

open Set TopologicalSpace

namespace Topology

variable {X : Type*} [TopologicalSpace X] {η : X}

/-- A constructible set contains an open neighbourhood of the generic point if it contains the
generic point, and is contained in a closed set avoiding the generic point otherwise. -/
theorem IsConstructible.generic_dichotomy (hη : IsGenericPoint η univ) {s : Set X}
    (hs : IsConstructible s) :
    (η ∈ s → ∃ U, IsOpen U ∧ η ∈ U ∧ U ⊆ s) ∧
      (η ∉ s → ∃ Z, IsClosed Z ∧ η ∉ Z ∧ s ⊆ Z) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    refine ⟨fun h ↦ ⟨U, hU, h, subset_rfl⟩,
      fun h ↦ ⟨∅, isClosed_empty, notMem_empty η, ?_⟩⟩
    intro x hx
    exact h ((hη.mem_open_set_iff hU).2 ⟨x, mem_univ x, hx⟩)
  | union s _ t _ hs' ht' =>
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases h with h | h
      · obtain ⟨U, hU, hηU, hUs⟩ := hs'.1 h
        exact ⟨U, hU, hηU, hUs.trans subset_union_left⟩
      · obtain ⟨U, hU, hηU, hUt⟩ := ht'.1 h
        exact ⟨U, hU, hηU, hUt.trans subset_union_right⟩
    · obtain ⟨Z, hZ, hηZ, hsZ⟩ := hs'.2 fun h' ↦ h (Or.inl h')
      obtain ⟨Z', hZ', hηZ', htZ'⟩ := ht'.2 fun h' ↦ h (Or.inr h')
      exact ⟨Z ∪ Z', hZ.union hZ', fun h' ↦ h'.elim hηZ hηZ', union_subset_union hsZ htZ'⟩
  | compl s _ hs' =>
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨Z, hZ, hηZ, hsZ⟩ := hs'.2 h
      exact ⟨Zᶜ, hZ.isOpen_compl, hηZ, compl_subset_compl.2 hsZ⟩
    · obtain ⟨U, hU, hηU, hUs⟩ := hs'.1 (not_notMem.1 h)
      exact ⟨Uᶜ, hU.isClosed_compl, fun h' ↦ h' hηU, compl_subset_compl.2 hUs⟩

/-- A constructible set not containing the generic point is contained in a closed set not
containing the generic point. -/
theorem IsConstructible.exists_isClosed_superset_of_notMem (hη : IsGenericPoint η univ)
    {s : Set X} (hs : IsConstructible s) (hηs : η ∉ s) :
    ∃ Z, IsClosed Z ∧ η ∉ Z ∧ s ⊆ Z :=
  (hs.generic_dichotomy hη).2 hηs

/-- In a quasi-sober noetherian space all of whose points other than `η` are closed, a closed set
not containing `η` is finite. -/
theorem _root_.IsClosed.finite_of_notMem_of_forall_ne [NoetherianSpace X] [QuasiSober X]
    (hcl : ∀ x, x ≠ η → IsClosed {x}) {Z : Set X} (hZ : IsClosed Z) (hηZ : η ∉ Z) :
    Z.Finite := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSf.sUnion fun t ht ↦ ?_
  have hg := (hSi t ht).isGenericPoint_genericPoint_closure
  rw [(hSc t ht).closure_eq] at hg
  have hmem : (hSi t ht).genericPoint ∈ ⋃₀ S := ⟨t, ht, hg.mem⟩
  have hne : (hSi t ht).genericPoint ≠ η := fun h ↦ hηZ (h ▸ hmem)
  rw [← hg.def, (hcl _ hne).closure_eq]
  exact finite_singleton _

/-- **Constructible sets avoiding the generic point of a curve.** In a quasi-sober noetherian
space with generic point `η` all of whose other points are closed, a constructible set not
containing `η` is finite. -/
theorem IsConstructible.finite_of_notMem [NoetherianSpace X] [QuasiSober X]
    (hη : IsGenericPoint η univ) (hcl : ∀ x, x ≠ η → IsClosed {x}) {s : Set X}
    (hs : IsConstructible s) (hηs : η ∉ s) : s.Finite := by
  obtain ⟨Z, hZ, hηZ, hsZ⟩ := hs.exists_isClosed_superset_of_notMem hη hηs
  exact (hZ.finite_of_notMem_of_forall_ne hcl hηZ).subset hsZ

/-- **Constructible sets avoiding the generic point of a curve**, as a finite set of closed
points. In a quasi-sober noetherian space with generic point `η` all of whose other points are
closed, a constructible set not containing `η` is a finite set of closed points. -/
theorem IsConstructible.exists_finset_of_notMem [NoetherianSpace X] [QuasiSober X]
    (hη : IsGenericPoint η univ) (hcl : ∀ x, x ≠ η → IsClosed {x}) {s : Set X}
    (hs : IsConstructible s) (hηs : η ∉ s) :
    ∃ S : Finset X, (S : Set X) = s ∧ ∀ x ∈ S, IsClosed {x} := by
  refine ⟨(hs.finite_of_notMem hη hcl hηs).toFinset, by simp, fun x hx ↦ hcl x ?_⟩
  rintro rfl
  exact hηs (by simpa using hx)

end Topology
