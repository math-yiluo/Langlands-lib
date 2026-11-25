/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod

@[expose] public section
set_option autoImplicit false
universe u w
attribute [local instance] ZMod.algebra
namespace RingTheory

/-- Spanning over the complementary p-basis subfield.
Source: Stacks Project, Tag 07P5, first proof paragraph, expanded by the
bounded-monomial argument of the parent node.
(blueprint: lem-weil-pbc-p-basis-complement-monomial-basis-spanning).

Proof: Put F = F_p(k^p). All elements of F lie in kJ since the latter contains
p-th powers and the prime field. Expand x in the given F-basis, with finitely
many nonzero coordinates. Split each bounded exponent function into its restriction
to J and to I minus J. The complementary monomial belongs to kJ, since each
of its generators lies there. Its product with the original F-coordinate is
therefore a kJ coefficient. Group the finitely many terms by their restriction
to J. This expresses x in the kJ-span of the displayed J monomials. For empty
J this also shows kJ = k, and the only displayed monomial is 1.
-/
theorem pBasisComplementMonomialBasis_spanning
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k ↦ x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e ↦ t i ^ e))
    (J : Finset I) (kJ : Subfield k)
    (hkJ : kJ = Subfield.closure
      (Set.range (fun x : k ↦ x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x})) :
    ⊤ ≤ Submodule.span kJ (Set.range (fun E : J → Fin p ↦ ∏ i : J, t i ^ (E i : ℕ))) := by
  classical
  let F := IntermediateField.adjoin (ZMod p) (Set.range (fun x : k ↦ x ^ p))
  have hF : F.toSubfield ≤ kJ := by
    change Subfield.closure _ ≤ kJ
    apply Subfield.closure_le.mpr
    rintro x (⟨a, rfl⟩ | hx)
    · rw [← ZMod.natCast_zmod_val a, map_natCast]
      exact natCast_mem kJ _
    · rw [hkJ]
      exact Subfield.subset_closure (Or.inl hx)
  let S := Submodule.span kJ
    (Set.range (fun E : J → Fin p ↦ ∏ i : J, t i ^ (E i : ℕ)))
  have hm (E : {E : I →₀ ℕ // ∀ i : I, E i < p}) :
      (E : I →₀ ℕ).prod (fun i e ↦ t i ^ e) ∈ S := by
    let e : J → Fin p := fun i ↦ ⟨E.val i, E.property i⟩
    let c := (E.val.filter (fun i ↦ i ∉ J)).prod (fun i n ↦ t i ^ n)
    have hc : c ∈ kJ := by
      apply kJ.prod_mem
      intro i hi
      rw [Finsupp.support_filter, Finset.mem_filter] at hi
      apply kJ.pow_mem
      rw [hkJ]
      exact Subfield.subset_closure (Or.inr ⟨i, hi.2, rfl⟩)
    have hsplit : E.val.prod (fun i n ↦ t i ^ n) =
        (∏ i : J, t i ^ (e i : ℕ)) * c := by
      rw [← Finsupp.prod_filter_mul_prod_filter_not (fun i ↦ i ∈ J)]
      congr 1
      rw [Finsupp.prod_of_support_subset _ (s := J)]
      · change (∏ i ∈ J, t i ^ (E.val.filter (fun i ↦ i ∈ J)) i) =
          ∏ i : J, t i ^ E.val i
        rw [Finset.prod_coe_sort J (fun i : I ↦ t i ^ E.val i)]
        apply Finset.prod_congr rfl
        intro i hi
        rw [Finsupp.filter_apply_pos _ _ hi]
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i hi
        exact pow_zero _
    rw [hsplit, mul_comm]
    exact S.smul_mem (⟨c, hc⟩ : kJ) (Submodule.subset_span ⟨e, rfl⟩)
  obtain ⟨b, hb⟩ := hpb
  intro x _
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  apply S.sum_mem
  intro E hE
  change (b.repr x E : k) * b E ∈ S
  rw [hb E]
  exact S.smul_mem (⟨(b.repr x E : k), hF (b.repr x E).property⟩ : kJ) (hm E)

end RingTheory
