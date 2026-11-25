/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod

import WeilConjectures.RingTheory.PBasisComplementMonomialSpan
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

@[expose] public section
set_option autoImplicit false
universe u w
attribute [local instance] ZMod.algebra
namespace RingTheory

private theorem independence_over_span
    (F : Type u) [Field F] (k : Type u) [Field k] [Algebra F k]
    (S : Subfield k) (ι : Type w) (κ : Type w) (v : ι → k) (w : κ → k)
    (hspan : ∀ a : S, (a : k) ∈ Submodule.span F (Set.range w))
    (hli : LinearIndependent F (fun q : ι × κ ↦ w q.2 * v q.1)) :
    LinearIndependent S v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  have hexp (i : ι) := Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan (a i))
  choose c hc using hexp
  let u := s.biUnion (fun i ↦ (c i).support)
  have hsub (i : ι) (hi : i ∈ s) : (c i).support ⊆ u :=
    Finset.subset_biUnion_of_mem (fun i ↦ (c i).support) hi
  have hsum (i : ι) (hi : i ∈ s) : ∑ j ∈ u, c i j • w j = (a i : k) := by
    rw [← Finsupp.sum_of_support_subset (c i) (hsub i hi) (fun j r ↦ r • w j)]
    · exact hc i
    · intro j _
      exact zero_smul _ _
  have hrel : ∑ q ∈ s ×ˢ u, c q.1 q.2 • (w q.2 * v q.1) = 0 := by
    rw [Finset.sum_product]
    calc
      ∑ i ∈ s, ∑ j ∈ u, c i j • (w j * v i) =
          ∑ i ∈ s, (a i : k) * v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hsum i hi, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        exact (smul_mul_assoc (c i j) (w j) (v i)).symm
      _ = 0 := ha
  have hz := linearIndependent_iff'.mp hli (s ×ˢ u)
    (fun q ↦ c q.1 q.2) hrel
  have hci : c i = 0 := by
    ext j
    by_cases hj : j ∈ u
    · exact hz (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)
    · exact Finsupp.notMem_support_iff.mp (fun hj' ↦ hj (hsub i hi hj'))
  apply Subtype.ext
  simpa [hci] using (hc i).symm

private theorem paired_monomials
    (F : Type u) [Field F] (k : Type u) [Field k] [Algebra F k]
    (p : ℕ) (I : Type w) (t : I → k) (J : Finset I)
    (hli : LinearIndependent F (fun E : {E : I →₀ ℕ // ∀ i, E i < p} ↦
      (E : I →₀ ℕ).prod (fun i e ↦ t i ^ e))) :
    LinearIndependent F
      (fun q : (J → Fin p) × {D : I →₀ ℕ // (∀ i, D i < p) ∧ ∀ i ∈ J, D i = 0} ↦
        (q.2 : I →₀ ℕ).prod (fun i e ↦ t i ^ e) * ∏ i : J, t i ^ (q.1 i : ℕ)) := by
  classical
  let d (E : J → Fin p) : I →₀ ℕ :=
    Finsupp.onFinset J (fun i ↦ if hi : i ∈ J then (E ⟨i, hi⟩ : ℕ) else 0)
      (by intro i hi; by_contra hn; simp [hn] at hi)
  have hd (E : J → Fin p) (i : I) :
      d E i = if hi : i ∈ J then (E ⟨i, hi⟩ : ℕ) else 0 := rfl
  let merge (q : (J → Fin p) ×
      {D : I →₀ ℕ // (∀ i, D i < p) ∧ ∀ i ∈ J, D i = 0}) :
      {E : I →₀ ℕ // ∀ i, E i < p} :=
    ⟨(q.2 : I →₀ ℕ) + d q.1, by
      intro i
      by_cases hi : i ∈ J
      · simp only [Finsupp.add_apply, q.2.property.2 i hi, zero_add, hd, dite_eq_left hi]
        exact (q.1 ⟨i, hi⟩).isLt
      · simpa only [Finsupp.add_apply, hd, dite_eq_right hi, add_zero] using q.2.property.1 i⟩
  have hinj : Function.Injective merge := by
    intro q r h
    have heq (i : I) := congrArg (fun E : {E : I →₀ ℕ // ∀ i, E i < p} ↦
      (E : I →₀ ℕ) i) h
    have hleft : q.1 = r.1 := by
      funext i
      apply Fin.ext
      simpa only [merge, Finsupp.add_apply, q.2.property.2 i i.property,
        r.2.property.2 i i.property, zero_add, hd, dite_eq_left i.property] using heq i
    have hright : q.2 = r.2 := by
      apply Subtype.ext
      ext i
      have hdi : d q.1 i = d r.1 i := congrArg (fun E ↦ d E i) hleft
      exact Nat.add_right_cancel (by simpa only [merge, Finsupp.add_apply, hdi] using heq i)
    exact Prod.ext hleft hright
  have hprod (E : J → Fin p) :
      (d E).prod (fun i e ↦ t i ^ e) = ∏ i : J, t i ^ (E i : ℕ) := by
    rw [Finsupp.prod_onFinset]
    · rw [← Finset.prod_attach]
      apply Finset.prod_congr rfl
      intro i _
      simp only [dite_eq_left i.property]
    · intro i _
      exact pow_zero _
  have h := hli.comp merge hinj
  convert h using 1
  funext q
  simp only [Function.comp_apply, merge]
  rw [Finsupp.prod_add_index' (fun i ↦ pow_zero (t i))
    (fun i a b ↦ pow_add (t i) a b), hprod]

/-- Independence over the complementary p-basis subfield.
Source: Stacks Project, Tag 07P5, first proof paragraph, expanded by the
bounded-monomial argument of the parent node.
(blueprint: lem-weil-pbc-p-basis-complement-monomial-basis-linearIndependent).

Proof: Frobenius has subfield image F, containing the prime field; hence this
image equals F_p(k^p). Let L be the F-span of bounded complementary monomials.
It contains 1 and the complementary generators. Multiplication preserves L by
reducing exponents modulo p and absorbing p-th powers into F. If a is nonzero
in L, a^p lies in F, and a inverse = (a^p) inverse times a^(p-1) lies in L.
Thus L is a subfield, and the generating property identifies it with kJ.
In any finite kJ-linear relation among the J monomials, expand each coefficient
as a finite F-linear combination of bounded complementary monomials. Pairing
J exponents with complementary exponents is injective: the restrictions recover
each member of the pair. The original F-basis is linearly independent, so all
expanded coordinates vanish. Every original coefficient is zero. This proves
independence, including empty J, when the family consists of the single nonzero
monomial 1. -/
theorem pBasisComplementMonomialBasis_linearIndependent
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
    LinearIndependent kJ (fun E : J → Fin p ↦ ∏ i : J, t i ^ (E i : ℕ)) := by
  classical
  obtain ⟨b, hb⟩ := hpb
  have hli : LinearIndependent
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k ↦ x ^ p)))
      (fun E : {E : I →₀ ℕ // ∀ i, E i < p} ↦
        (E : I →₀ ℕ).prod (fun i e ↦ t i ^ e)) := by
    convert b.linearIndependent using 1
    funext E
    exact (hb E).symm
  exact independence_over_span
    (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k ↦ x ^ p))) k kJ
    (J → Fin p) {D : I →₀ ℕ // (∀ i, D i < p) ∧ ∀ i ∈ J, D i = 0}
    (fun E ↦ ∏ i : J, t i ^ (E i : ℕ))
    (fun D ↦ (D : I →₀ ℕ).prod (fun i e ↦ t i ^ e))
    (pBasisComplementMonomial_mem_span p k I t J kJ hkJ)
    (paired_monomials _ k p I t J hli)

end RingTheory
