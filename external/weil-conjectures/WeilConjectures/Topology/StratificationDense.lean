/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Topology.Stratification
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.GDelta.Basic

/-!
# The interiors of the strata of a stratification are dense

A locally closed subset with empty interior is nowhere dense
(`IsLocallyClosed.isNowhereDense_of_interior_eq_empty`), and a finite union of nowhere dense
subsets is nowhere dense (`isNowhereDense_iUnion`). Hence, for a finite stratification
`(Xᵢ)` of a topological space `X`, the union of the interiors of the strata is dense
(`Topology.Stratification.dense_iUnion_interior_stratum`): its complement lies in the union
of the nowhere dense sets `Xᵢ \ interior Xᵢ`. No Noetherian hypothesis is needed.

-/

@[expose] public section

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- A locally closed subset with empty interior is nowhere dense: writing
`s = coborder s ∩ closure s` with `coborder s` open, the open set `interior (closure s)` meets
`coborder s` inside `interior s = ∅`, and an open subset of `closure (coborder s)` disjoint
from `coborder s` is empty. -/
lemma IsLocallyClosed.isNowhereDense_of_interior_eq_empty {s : Set X} (hs : IsLocallyClosed s)
    (h : interior s = ∅) : IsNowhereDense s := by
  have hopen : IsOpen (coborder s) := hs.isOpen_coborder
  have h₁ : interior (closure s) ∩ coborder s = ∅ := by
    rw [← hopen.interior_eq, ← interior_inter, Set.inter_comm (closure s) (coborder s),
      coborder_inter_closure, h]
  have h₂ : interior (closure s) ⊆ closure (coborder s) :=
    interior_subset.trans (closure_mono subset_coborder)
  rw [IsNowhereDense]
  apply Set.eq_empty_of_subset_empty
  calc interior (closure s) = interior (closure s) ∩ closure (coborder s) :=
        (inter_eq_left.mpr h₂).symm
    _ ⊆ closure (interior (closure s) ∩ coborder s) := isOpen_interior.inter_closure
    _ = ∅ := by rw [h₁, closure_empty]

/-- A finite union of nowhere dense subsets is nowhere dense. -/
lemma isNowhereDense_biUnion_finset {ι : Type*} (s : Finset ι) {f : ι → Set X}
    (hf : ∀ i ∈ s, IsNowhereDense (f i)) : IsNowhereDense (⋃ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isNowhereDense_empty]
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (hf a (Finset.mem_insert_self a s)).union
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- A finite union of nowhere dense subsets is nowhere dense. -/
lemma isNowhereDense_iUnion {ι : Type*} [Finite ι] {f : ι → Set X}
    (hf : ∀ i, IsNowhereDense (f i)) : IsNowhereDense (⋃ i, f i) := by
  have := Fintype.ofFinite ι
  have := isNowhereDense_biUnion_finset (Finset.univ : Finset ι) (fun i _ ↦ hf i)
  simpa using this

namespace Topology.Stratification

variable (S : Stratification X)

/-- A stratum minus its interior is nowhere dense. -/
lemma isNowhereDense_stratum_diff_interior (i : Fin S.n) :
    IsNowhereDense (S.stratum i \ interior (S.stratum i)) := by
  refine ((S.isLocallyClosed_stratum i).inter
    isOpen_interior.isClosed_compl.isLocallyClosed).isNowhereDense_of_interior_eq_empty ?_
  apply Set.eq_empty_of_subset_empty
  calc interior (S.stratum i \ interior (S.stratum i))
      ⊆ interior (S.stratum i) ∩ (interior (S.stratum i))ᶜ :=
        fun x hx ↦ ⟨interior_mono sdiff_subset hx, (interior_subset hx).2⟩
    _ = ∅ := inter_compl_self _

/-- **The union of the interiors of the strata of a stratification is dense**: its complement
is contained in the union of the nowhere dense sets `Xᵢ \ interior Xᵢ`. -/
theorem dense_iUnion_interior_stratum : Dense (⋃ i, interior (S.stratum i)) := by
  have hN : IsNowhereDense (⋃ i, S.stratum i \ interior (S.stratum i)) :=
    isNowhereDense_iUnion S.isNowhereDense_stratum_diff_interior
  have hint : interior (⋃ i, S.stratum i \ interior (S.stratum i)) = ∅ :=
    Set.eq_empty_of_subset_empty ((interior_mono subset_closure).trans hN.le)
  refine (interior_eq_empty_iff_dense_compl.mp hint).mono fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  by_contra hxi
  exact hx (Set.mem_iUnion.mpr ⟨i, hi, hxi⟩)

end Topology.Stratification
