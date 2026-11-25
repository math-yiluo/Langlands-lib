/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import WeilConjectures.AlgebraicGeometry.PolynomialIdealCoefficientsMonomial

/-! Equivalence between subsequence regularity and polynomial-variable regularity.
Source: Stacks Project, Algebra, Lemma 10.68.10, Tag 07DW.
(blueprint: lem-weil-pbc-regular-sequence-subsequences-polynomial-proof).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence


private lemma ofList_take_ofFn {A : Type*} {n : ℕ} [CommRing A]
    (g : Fin n → A) (i : ℕ) (hi : i ≤ n) :
    Ideal.ofList ((List.ofFn g).take i) =
      Ideal.span (Set.range fun j : Fin i ↦ g (Fin.castLE hi j)) := by
  apply congrArg Ideal.span
  ext a
  change a ∈ (List.ofFn g).take i ↔ ∃ j : Fin i, g (Fin.castLE hi j) = a
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, ha⟩
    have hj' : j < i := by
      simpa [List.length_take, List.length_ofFn, Nat.min_eq_left hi] using hj
    refine ⟨⟨j, hj'⟩, ?_⟩
    simpa using ha
  · rintro ⟨j, rfl⟩
    refine ⟨j, by simp [List.length_take, List.length_ofFn, Nat.min_eq_left hi], ?_⟩
    simp
    rfl

private lemma coeff_mem_prefix_iff {R : Type u} [CommRing R]
    (r i : ℕ) (hr : 1 ≤ r) (hi : i ≤ r) (f : Fin r → R)
    (p : MvPolynomial (Fin r) R) :
    p ∈ Ideal.ofList ((List.ofFn (fun j ↦ MvPolynomial.C (f j) * MvPolynomial.X j)).take i) ↔
      ∀ E : Fin r →₀ ℕ,
        AddMonoidAlgebra.coeff p E ∈ Ideal.span (f '' {j : Fin r | j.val < i ∧ E j ≠ 0}) := by
  rw [ofList_take_ofFn _ _ hi]
  have h := (MvPolynomial.ideal_coefficients_monomial r i hr hi
    (fun j ↦ f (Fin.castLE hi j)) p).1
  have hs (E : Fin r →₀ ℕ) :
      f '' {j : Fin r | j.val < i ∧ E j ≠ 0} =
        (fun j : Fin i ↦ f (Fin.castLE hi j)) ''
          {j : Fin i | E (Fin.castLE hi j) ≠ 0} := by
    ext a
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, ⟨hj, he⟩, rfl⟩
      exact ⟨⟨j.val, hj⟩, he, rfl⟩
    · rintro ⟨j, he, rfl⟩
      exact ⟨Fin.castLE hi j, ⟨j.isLt, he⟩, rfl⟩
  simp_rw [hs]
  exact h

private lemma prefix_support_shift {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (i : Fin r) (E : Fin r →₀ ℕ) :
    Ideal.span (f '' {j : Fin r | j.val < i.val ∧
      (Finsupp.single i 1 + E : Fin r →₀ ℕ) j ≠ 0}) =
      Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) := by
  apply congrArg Ideal.span
  apply congrArg (Set.image f)
  ext j
  simp only [Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hj, he⟩ <;> refine ⟨hj, ?_⟩
  · simpa [Finsupp.add_apply, Finsupp.single_eq_of_ne (Fin.ne_of_lt hj)] using he
  · simpa [Finsupp.add_apply, Finsupp.single_eq_of_ne (Fin.ne_of_lt hj)] using he

private lemma polynomial_step_iff {R : Type u} [CommRing R]
    (r : ℕ) (f : Fin r → R) (i : Fin r) :
    (∀ p : MvPolynomial (Fin r) R,
      (MvPolynomial.C (f i) * MvPolynomial.X i) * p ∈
        Ideal.ofList ((List.ofFn (fun j ↦ MvPolynomial.C (f j) * MvPolynomial.X j)).take i.val) →
      p ∈ Ideal.ofList ((List.ofFn (fun j ↦ MvPolynomial.C (f j) * MvPolynomial.X j)).take i.val)) ↔
    ∀ (E : Fin r →₀ ℕ) (a : R),
      f i * a ∈ Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) →
      a ∈ Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) := by
  classical
  have hr : 1 ≤ r := Nat.succ_le_of_lt (Nat.zero_le i.val |>.trans_lt i.isLt)
  have hm := coeff_mem_prefix_iff r i.val hr (Nat.le_of_lt i.isLt) f
  constructor
  · intro h E a ha
    have hp : (MvPolynomial.C (f i) * MvPolynomial.X i) *
        MvPolynomial.monomial E a ∈
        Ideal.ofList ((List.ofFn (fun j ↦ MvPolynomial.C (f j) *
          MvPolynomial.X j)).take i.val) := by
      apply (hm _).mpr
      intro D
      rw [mul_assoc, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul,
        MvPolynomial.C_mul_monomial, MvPolynomial.coeff_monomial]
      split_ifs with hd
      · subst D
        rwa [prefix_support_shift f i E]
      · exact Ideal.zero_mem _
    have hma := (hm _).mp (h _ hp) E
    simpa using hma
  · intro h p hp
    apply (hm p).mpr
    intro E
    have he := (hm _).mp hp (Finsupp.single i 1 + E)
    rw [mul_assoc, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul,
      prefix_support_shift f i E] at he
    exact h E (AddMonoidAlgebra.coeff p E) he

private lemma weak_polynomial_iff {R : Type u} [CommRing R]
    (r : ℕ) (f : Fin r → R) :
    IsWeaklyRegular (MvPolynomial (Fin r) R)
      (List.ofFn (fun i : Fin r ↦ MvPolynomial.C (f i) * MvPolynomial.X i)) ↔
    ∀ (i : Fin r) (E : Fin r →₀ ℕ) (a : R),
      f i * a ∈ Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) →
      a ∈ Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) := by
  constructor
  · intro h i
    have hi : i.val <
        (List.ofFn (fun j : Fin r ↦ MvPolynomial.C (f j) * MvPolynomial.X j)).length := by
      simp
    have hreg := h.regular_mod_prev i.val hi
    simp only [List.getElem_ofFn] at hreg
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hreg
    simp only [smul_eq_mul, Ideal.mul_top] at hreg
    exact (polynomial_step_iff r f i).mp hreg
  · intro h
    refine ⟨?_⟩
    intro i hi
    have hi' : i < r := by simpa using hi
    simp only [List.getElem_ofFn]
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    simp only [smul_eq_mul, Ideal.mul_top]
    exact (polynomial_step_iff r f ⟨i, hi'⟩).mpr (h ⟨i, hi'⟩)

private lemma polynomial_proper {R : Type u} [CommRing R] [Nontrivial R]
    (r : ℕ) (f : Fin r → R) :
    Ideal.ofList (List.ofFn (fun i : Fin r ↦ MvPolynomial.C (f i) * MvPolynomial.X i)) ≠ ⊤ := by
  intro ht
  have hle : Ideal.ofList (List.ofFn (fun i : Fin r ↦ MvPolynomial.C (f i) * MvPolynomial.X i)) ≤
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin r) R →+* R) := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    simp [RingHom.mem_ker]
  have h1 := hle (show (1 : MvPolynomial (Fin r) R) ∈
      Ideal.ofList (List.ofFn (fun i : Fin r ↦ MvPolynomial.C (f i) *
        MvPolynomial.X i)) by rw [ht]; trivial)
  simp only [RingHom.mem_ker, map_one] at h1
  exact (one_ne_zero : (1 : R) ≠ 0) h1

private lemma map_pairwise_sublist {R : Type u} {r : ℕ} (f : Fin r → R)
    (s : List (Fin r)) (hs : s.Pairwise (· < ·)) :
    (s.map f).Sublist (List.ofFn f) := by
  have hp : (s.map (Fin.cast (List.length_ofFn (f := f)).symm)).Pairwise (· < ·) := by
    simpa [List.pairwise_map] using hs
  have h := List.map_getElem_sublist (l := List.ofFn f) hp
  simpa [List.map_map, Function.comp_def] using h

private lemma selected_prefix_ideal {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (i : Fin r) (E : Fin r →₀ ℕ) :
    Ideal.ofList (((List.finRange r).filter
      (fun j ↦ decide (j.val < i.val ∧ E j ≠ 0))).map f) =
      Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) := by
  apply congrArg Ideal.span
  ext a
  simp [List.mem_map, List.mem_filter, Set.mem_image]

private lemma coeff_condition_of_subsequences {R : Type u} [CommRing R]
    (r : ℕ) (f : Fin r → R)
    (h : ∀ l : List R, l.Sublist (List.ofFn f) → IsRegular R l) :
    ∀ (i : Fin r) (E : Fin r →₀ ℕ) (a : R),
      f i * a ∈ Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) →
      a ∈ Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) := by
  classical
  intro i E a ha
  let s := (List.finRange r).filter (fun j ↦ decide (j.val < i.val ∧ E j ≠ 0))
  have hs : (s ++ [i]).Pairwise (· < ·) := by
    rw [List.pairwise_append]
    refine ⟨(List.pairwise_lt_finRange r).sublist (List.filter_sublist), by simp, ?_⟩
    intro j hj k hk
    have hk' : k = i := by simpa using hk
    subst k
    exact (of_decide_eq_true (List.mem_filter.mp hj).2).1
  have hw := (h ((s ++ [i]).map f) (map_pairwise_sublist f _ hs)).toIsWeaklyRegular
  have hi : s.length < ((s ++ [i]).map f).length := by simp
  have hn := hw.regular_mod_prev s.length hi
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem, smul_eq_mul, Ideal.mul_top] at hn
  have htake : (((s ++ [i]).map f).take s.length) = s.map f := by
    simp only [List.map_append, List.map_singleton, List.take_append, List.length_map,
      Nat.sub_self, List.take_zero, List.append_nil]
    exact List.take_of_length_le (by simp)
  have hget : ((s ++ [i]).map f)[s.length] = f i := by simp
  rw [htake, hget, selected_prefix_ideal] at hn
  exact hn a ha

private lemma subsequence_regular_of_coeff_condition {R : Type u} [CommRing R]
    (r : ℕ) (f : Fin r → R) (hproper : Ideal.ofList (List.ofFn f) ≠ ⊤)
    (h : ∀ (i : Fin r) (E : Fin r →₀ ℕ) (a : R),
      f i * a ∈ Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) →
      a ∈ Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0})) :
    ∀ l : List R, l.Sublist (List.ofFn f) → IsRegular R l := by
  classical
  intro l hl
  have hle : Ideal.ofList l ≤ Ideal.ofList (List.ofFn f) :=
    Ideal.span_mono hl.subset
  have hlproper : Ideal.ofList l ≠ ⊤ := by
    intro ht
    apply hproper
    exact top_unique (ht ▸ hle)
  refine ⟨?_, ?_⟩
  · rw [List.ofFn_eq_map] at hl
    obtain ⟨s, hs, rfl⟩ := List.sublist_map_iff.mp hl
    have hp := (List.pairwise_lt_finRange r).sublist hs
    refine ⟨?_⟩
    intro k hk
    have hk' : k < s.length := by simpa using hk
    let i : Fin r := s[k]
    let E : Fin r →₀ ℕ := ∑ j ∈ (s.take k).toFinset, Finsupp.single j 1
    have he (j : Fin r) : E j ≠ 0 ↔ j ∈ s.take k := by
      simp [E, Finsupp.single_apply, Finset.sum_apply, eq_comm]
    have hlt (j : Fin r) (hj : j ∈ s.take k) : j.val < i.val := by
      obtain ⟨n, hn, rfl⟩ := List.mem_take_iff_getElem.mp hj
      exact List.pairwise_iff_getElem.mp hp n k (lt_of_lt_of_le hn (Nat.min_le_right _ _))
        hk' (lt_of_lt_of_le hn (Nat.min_le_left _ _))
    have hset : {j : Fin r | j.val < i.val ∧ E j ≠ 0} =
        {j : Fin r | j ∈ s.take k} := by
      ext j
      exact ⟨fun hj ↦ (he j).mp hj.2, fun hj ↦ ⟨hlt j hj, (he j).mpr hj⟩⟩
    have hid : Ideal.ofList ((s.map f).take k) =
        Ideal.span (f '' {j : Fin r | j.val < i.val ∧ E j ≠ 0}) := by
      rw [hset]
      apply congrArg Ideal.span
      ext a
      change a ∈ (s.map f).take k ↔ _
      rw [← List.map_take]
      simp only [List.mem_map, Set.mem_image, Set.mem_ofPred_eq]
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    simp only [smul_eq_mul, Ideal.mul_top, List.getElem_map]
    rw [hid]
    exact h i E
  · simpa only [smul_eq_mul, Ideal.mul_top, ne_comm] using hlproper

/-- Source: Stacks Project, Algebra, Lemma 10.68.10, Tag 07DW.
(blueprint: lem-weil-pbc-regular-sequence-subsequences-polynomial-proof).
The equivalence is proved by the coefficientwise description of ideals generated by
coordinate multiples, followed by the defining criterion for regular sequences.
-/
theorem isRegular_subsequences_iff_polynomial_variables
    {R : Type u} [CommRing R] (r : ℕ) (f : Fin r → R)
    (hproper : Ideal.ofList (List.ofFn f) ≠ ⊤) :
    (∀ l : List R, l.Sublist (List.ofFn f) → IsRegular R l) ↔
      IsRegular (MvPolynomial (Fin r) R)
        (List.ofFn (fun i : Fin r ↦ MvPolynomial.C (f i) * MvPolynomial.X i)) := by
  have h10 : (1 : R) ≠ 0 := by
    intro hzero
    apply hproper
    apply (Ideal.eq_top_iff_one _).mpr
    rw [hzero]
    exact Ideal.zero_mem _
  have : Nontrivial R := nontrivial_of_ne 1 0 h10
  constructor
  · intro h
    refine ⟨(weak_polynomial_iff r f).mpr (coeff_condition_of_subsequences r f h), ?_⟩
    simpa only [smul_eq_mul, Ideal.mul_top, ne_comm] using polynomial_proper r f
  · intro h
    exact subsequence_regular_of_coeff_condition r f hproper
      ((weak_polynomial_iff r f).mp h.toIsWeaklyRegular)

end RingTheory.Sequence
