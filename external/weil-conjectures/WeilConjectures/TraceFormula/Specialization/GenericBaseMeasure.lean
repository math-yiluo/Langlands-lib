/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.ResidueFieldTrdegFiniteType

/-!
# A dimension measure for schemes over a field

For a scheme `X` over a field `F`, `AlgebraicGeometry.genericBaseMeasure X` is the maximum over
the points `x` of `X` of the transcendence degree of the residue field extension `κ(x) / F`
(`0` if these are unbounded, which does not happen for `X` of finite type over `F`). For `X` of
finite type over `F` this is the dimension of `X`.

* `AlgebraicGeometry.trdegAt_le_genericBaseMeasure`: for `X` of finite type over `F`, it bounds
  the transcendence degrees of all residue fields. Indeed `X` is noetherian, every point is a
  specialization of one of the finitely many generic points of the irreducible components, and the
  transcendence degree decreases along specializations.
* `AlgebraicGeometry.genericBaseMeasure_le_of_isOpenImmersion`: it does not increase when passing
  from a scheme to a dense open: the generic points of the irreducible components lie in the
  dense open, and open immersions preserve residue fields.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {F : Type u} [Field F]

/-- The *measure* of a scheme `X` over a field `F`: the maximum over the points `x` of `X` of
`trdeg_F κ(x)` (`0` if these are unbounded). For `X` of finite type over `F` this is its
dimension. -/
noncomputable def genericBaseMeasure (X : Over (Spec (.of F))) : ℕ :=
  ⨆ x : X.left, (X.hom.trdegAt x).toNat

/-- In a quasi-sober space every point is a specialization of a generic point of an irreducible
component. -/
lemma exists_mem_genericPoints_specializes {α : Type*} [TopologicalSpace α] [QuasiSober α]
    (x : α) : ∃ ξ ∈ genericPoints α, ξ ⤳ x := by
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := x)).closure
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  refine ⟨hC.1.genericPoint, ?_, ?_⟩
  · rw [genericPoints, Set.mem_ofPred_eq, hg.def]
    exact hC
  · rw [specializes_iff_mem_closure, hg.def]
    exact hxC (subset_closure rfl)

/-- In a noetherian space a dense open contains the generic points of the irreducible
components. -/
lemma genericPoints_subset_of_isOpen_of_dense_of_noetherianSpace {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] {U : Set α} (hU : IsOpen U) (hd : Dense U) : genericPoints α ⊆ U := by
  intro c hc
  obtain ⟨o, ho, hne, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hc
  obtain ⟨v, hvo, hvU⟩ := hd.inter_open_nonempty o ho hne
  exact (specializes_iff_mem_closure.2 (hoZ hvo)).mem_open hU hvU

/-- **The transcendence degrees of the residue fields of a scheme of finite type over a field are
bounded.** -/
lemma exists_trdegAt_le (X : Over (Spec (.of F))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : ∃ n : ℕ, ∀ x : X.left, X.hom.trdegAt x ≤ n := by
  have := isNoetherian_left X
  have hfin : (genericPoints X.left).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  obtain ⟨n, hn⟩ := (hfin.image fun ξ ↦ (X.hom.trdegAt ξ).toNat).bddAbove
  refine ⟨n, fun x ↦ ?_⟩
  obtain ⟨ξ, hξ, hξx⟩ := exists_mem_genericPoints_specializes x
  refine (X.hom.trdegAt_le_of_specializes hξx).trans ?_
  rw [← Cardinal.cast_toNat_of_lt_aleph0 (X.hom.trdegAt_lt_aleph0 ξ)]
  exact_mod_cast hn ⟨ξ, hξ, rfl⟩

/-- For a scheme of finite type over a field, the transcendence degree of every residue field is
at most the measure. -/
lemma trdegAt_le_genericBaseMeasure (X : Over (Spec (.of F))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : X.left) : X.hom.trdegAt x ≤ genericBaseMeasure X := by
  obtain ⟨n, hn⟩ := exists_trdegAt_le X
  rw [← Cardinal.cast_toNat_of_lt_aleph0 (X.hom.trdegAt_lt_aleph0 x)]
  refine Nat.cast_le.2 (le_ciSup (f := fun x : X.left ↦ (X.hom.trdegAt x).toNat) ⟨n, ?_⟩ x)
  rintro _ ⟨y, rfl⟩
  exact (Cardinal.toNat_le_toNat (hn y) (Cardinal.natCast_lt_aleph0 (n := n))).trans_eq
    (Cardinal.toNat_natCast n)

/-- **The measure does not increase on dense opens**: if `j : X₁ ⟶ Xc` is an open immersion with
dense range of schemes of finite type over a field, then `μ Xc ≤ μ X₁`. -/
theorem genericBaseMeasure_le_of_isOpenImmersion {X₁ Xc : Over (Spec (.of F))} (j : X₁ ⟶ Xc)
    [IsOpenImmersion j.left] (hj : DenseRange j.left) [LocallyOfFiniteType X₁.hom]
    [QuasiCompact X₁.hom] [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom] :
    genericBaseMeasure Xc ≤ genericBaseMeasure X₁ := by
  have := isNoetherian_left Xc
  refine ciSup_le' fun y ↦ ?_
  obtain ⟨ξ, hξ, hξy⟩ := exists_mem_genericPoints_specializes y
  obtain ⟨ξ', rfl⟩ := genericPoints_subset_of_isOpen_of_dense_of_noetherianSpace
    j.left.isOpenEmbedding.isOpen_range
    hj hξ
  refine (Cardinal.toNat_le_toNat (Xc.hom.trdegAt_le_of_specializes hξy)
    (Xc.hom.trdegAt_lt_aleph0 _)).trans ?_
  rw [← Scheme.Hom.trdegAt_comp_of_isPreimmersion j.left Xc.hom, Over.w j]
  exact_mod_cast (Cardinal.toNat_le_toNat (trdegAt_le_genericBaseMeasure X₁ ξ')
    Cardinal.natCast_lt_aleph0).trans_eq (Cardinal.toNat_natCast _)

end AlgebraicGeometry
