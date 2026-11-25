/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous zero relations on a regular sequence

Source: Stacks Project, Algebra, Tag 00LN, proof of (1).
(blueprint: lem-pur-regular-sequence-higher-homogeneous-relations).
-/

@[expose] public section

universe u

namespace Ideal

private theorem raise_homogeneous {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → R) (n : ℕ) (p : MvPolynomial (Fin c) R)
    (hp : p.IsHomogeneous n) (hc : ∀ d, p.coeff d ∈ Ideal.span (Set.range f)) :
    ∃ q : MvPolynomial (Fin c) R, q.IsHomogeneous (n + 1) ∧ q.eval f = p.eval f := by
  classical
  have hrep (d : p.support) : ∃ a : Fin c → R, ∑ i, a i * f i = p.coeff d.val :=
    Ideal.mem_span_range_iff_exists_fun.mp (hc d.val)
  choose a ha using hrep
  let q : MvPolynomial (Fin c) R :=
    ∑ d : p.support, ∑ i : Fin c, MvPolynomial.monomial d.val (a d i) * MvPolynomial.X i
  refine ⟨q, ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro d hd
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    have hdeg : d.val.sum (fun _ k ↦ k) = n := by
      change d.val.degree = n
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hp (MvPolynomial.mem_support_iff.mp d.property)
    exact (MvPolynomial.isHomogeneous_monomial _ hdeg).mul (MvPolynomial.isHomogeneous_X R i)
  · dsimp only [q]
    rw [map_sum]
    simp only [map_sum, map_mul, MvPolynomial.eval_monomial, MvPolynomial.eval_X]
    conv_rhs => rw [p.as_sum, map_sum]
    simp only [MvPolynomial.eval_monomial]
    rw [← Finset.sum_coe_sort p.support]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← ha d, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring

private theorem relation_from_zero {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hz : ∀ (n : ℕ) (p : MvPolynomial (Fin c) R), p.IsHomogeneous n →
      p.eval f = 0 → ∀ d, p.coeff d ∈ Ideal.span (Set.range f))
    (n : ℕ) (p : MvPolynomial (Fin c) R) (hp : p.IsHomogeneous n)
    (hmem : p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1)) :
    ∀ d, p.coeff d ∈ Ideal.span (Set.range f) := by
  classical
  let J := Ideal.span (Set.range f)
  have hrep : ∀ y ∈ J ^ (n + 1), ∃ q : MvPolynomial (Fin c) R,
      q.IsHomogeneous n ∧ q.eval f = y ∧ ∀ d, q.coeff d ∈ J := by
    intro y hy
    rw [pow_succ', ← Ideal.smul_eq_mul] at hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨q, hq, he⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f b).mp hb
      refine ⟨MvPolynomial.C a * q, hq.C_mul a, ?_, ?_⟩
      · simp only [map_mul, MvPolynomial.eval_C, he, smul_eq_mul]
      · intro d
        rw [MvPolynomial.coeff_C_mul]
        exact J.mul_mem_right _ ha
    · intro x y hx hy
      obtain ⟨p, hp, he, hc⟩ := hx
      obtain ⟨q, hq, hf, hd⟩ := hy
      exact ⟨p + q, hp.add hq, by rw [map_add, he, hf],
        fun d ↦ by rw [AddMonoidAlgebra.coeff_add]; exact J.add_mem (hc d) (hd d)⟩
  obtain ⟨q, hq, he, hc⟩ := hrep _ hmem
  have hh := hz n (p - q) (hp.sub hq) (by rw [map_sub, he, sub_self])
  intro d
  have hd : p.coeff d - q.coeff d ∈ J := by
    simpa only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] using hh d
  simpa only [sub_add_cancel] using J.add_mem hd (hc d)

private theorem truncated_relation {R : Type u} [CommRing R] {c : ℕ}
    (g : Fin c → R) (t : R) (J : Ideal R)
    (hK : Ideal.span (Set.range g) ≤ J) (ht : t ∈ J)
    (hreg : IsSMulRegular (R ⧸ Ideal.span (Set.range g)) t)
    (houter : ∀ (n : ℕ) (p : MvPolynomial (Fin c) R), p.IsHomogeneous n →
      p.eval g ∈ Ideal.span (Set.range g) ^ (n + 1) →
        ∀ d, p.coeff d ∈ Ideal.span (Set.range g))
    (n l : ℕ) (hl : l ≤ n) (a : ℕ → MvPolynomial (Fin c) R)
    (ha : ∀ e ≤ l, (a e).IsHomogeneous (n - e))
    (hz : ∑ e ∈ Finset.range (l + 1), (a e).eval g * t ^ e = 0) :
    ∀ e ≤ l, ∀ d, (a e).coeff d ∈ J := by
  classical
  let K := Ideal.span (Set.range g)
  induction l generalizing a with
  | zero =>
    intro e he d
    have he0 : e = 0 := by omega
    subst e
    have hzero : (a 0).eval g = 0 := by simpa using hz
    apply hK
    exact houter n (a 0) (by simpa using ha 0 (by omega)) (by rw [hzero]; exact zero_mem _) d
  | succ l ih =>
    have htopmem : (a (l + 1)).eval g * t ^ (l + 1) ∈ K ^ (n - (l + 1) + 1) := by
      have hlow : (∑ e ∈ Finset.range (l + 1), (a e).eval g * t ^ e) ∈
          K ^ (n - (l + 1) + 1) := by
        apply Ideal.sum_mem
        intro e he
        have hel : e ≤ l := by simpa using Finset.mem_range.mp he
        have hm : (a e).eval g ∈ K ^ (n - e) :=
          (Ideal.mem_span_pow_iff_exists_isHomogeneous g _).mpr
            ⟨a e, ha e (by omega), rfl⟩
        exact Ideal.mul_mem_right _ _
          ((Ideal.pow_le_pow_right (by omega : n - (l + 1) + 1 ≤ n - e)) hm)
      rw [Finset.sum_range_succ] at hz
      rw [eq_neg_of_add_eq_zero_right hz]
      exact (K ^ (n - (l + 1) + 1)).neg_mem hlow
    have htop : ∀ d, (a (l + 1)).coeff d ∈ K := by
      have hh := houter (n - (l + 1))
        (MvPolynomial.C (t ^ (l + 1)) * a (l + 1))
        ((ha (l + 1) (by omega)).C_mul _) (by
          simpa only [map_mul, MvPolynomial.eval_C, mul_comm] using htopmem)
      intro d
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply (hreg.pow (l + 1)).right_eq_zero_of_smul
      change Ideal.Quotient.mk K (t ^ (l + 1) * (a (l + 1)).coeff d) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa only [MvPolynomial.coeff_C_mul] using hh d
    obtain ⟨q, hq, heq⟩ := raise_homogeneous g (n - (l + 1)) (a (l + 1))
      (ha (l + 1) (by omega)) htop
    let b := Function.update a l (a l + MvPolynomial.C t * q)
    have hb : ∀ e ≤ l, (b e).IsHomogeneous (n - e) := by
      intro e he
      by_cases h : e = l
      · subst e
        simp only [b, Function.update_self]
        apply (ha l (by omega)).add
        convert hq.C_mul t using 1
        omega
      · simpa only [b, Function.update_of_ne h] using ha e (by omega)
    have hbz : ∑ e ∈ Finset.range (l + 1), (b e).eval g * t ^ e = 0 := by
      have hsum : ∑ e ∈ Finset.range l, (b e).eval g * t ^ e =
          ∑ e ∈ Finset.range l, (a e).eval g * t ^ e := by
        apply Finset.sum_congr rfl
        intro e he
        dsimp only [b]
        rw [Function.update_of_ne (by have := Finset.mem_range.mp he; omega)]
      rw [Finset.sum_range_succ, hsum]
      simp only [b, Function.update_self]
      simp only [map_add, map_mul, MvPolynomial.eval_C, heq]
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hz
      rw [← hz]
      ring
    have hbc := ih (by omega) b hb hbz
    intro e he d
    by_cases htopindex : e = l + 1
    · subst e
      exact hK (htop d)
    have hel : e ≤ l := by omega
    by_cases h : e = l
    · subst e
      have hcoeff := hbc l (by omega) d
      simp only [b, Function.update_self] at hcoeff
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul] at hcoeff
      simpa only [add_sub_cancel_right] using
        J.sub_mem hcoeff (J.mul_mem_right (q.coeff d) ht)
    · simpa only [b, Function.update_of_ne h] using hbc e hel d

private theorem weakly_regular_relation {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → R) (hf : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f)) :
    ∀ (n : ℕ) (p : MvPolynomial (Fin c) R), p.IsHomogeneous n →
      p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) →
        ∀ d, p.coeff d ∈ Ideal.span (Set.range f) := by
  classical
  induction c with
  | zero =>
    intro n p hp hm d
    have hJ : Ideal.span (Set.range f) = ⊥ := by simp
    have he : p = MvPolynomial.C (p.coeff 0) := by
      ext e
      have he : e = 0 := Subsingleton.elim _ _
      subst e
      simp
    have hc : p.coeff 0 = 0 := by
      have hz : p.eval f = 0 := by simpa [hJ] using hm
      rw [he, MvPolynomial.eval_C] at hz
      exact hz
    rw [he, hc, map_zero]
    simp
  | succ c ih =>
    let g : Fin c → R := fun i ↦ f i.castSucc
    let K := Ideal.span (Set.range g)
    let J := Ideal.span (Set.range f)
    let t := f (Fin.last c)
    have hof : Ideal.ofList (List.ofFn g) = K :=
      congrArg Ideal.span (Set.ext (List.mem_ofFn' g))
    have hs := (RingTheory.Sequence.isWeaklyRegular_append_iff R (List.ofFn g) [t]).mp
      (by simpa only [g, t, List.ofFn_succ', List.concat_eq_append] using hf)
    have hprefix := hs.1
    have hlast : IsSMulRegular (R ⧸ K) t := by
      have ht := (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mp hs.2
      change IsSMulRegular (R ⧸ (Ideal.ofList (List.ofFn g) • (⊤ : Ideal R))) t at ht
      rw [hof, Ideal.smul_eq_mul, Ideal.mul_top] at ht
      exact ht
    have hKJ : K ≤ J := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨i.castSucc, rfl⟩
    have htJ : t ∈ J := Ideal.subset_span ⟨Fin.last c, rfl⟩
    apply relation_from_zero f
    intro n p hp hz
    let e := finSuccEquiv' (Fin.last c)
    let q := MvPolynomial.rename e p
    let P := MvPolynomial.optionEquivLeft R (Fin c) q
    have hq : q.IsHomogeneous n := hp.rename_isHomogeneous
    have hl : P.natDegree ≤ n := by
      calc
        P.natDegree = q.degreeOf none := MvPolynomial.natDegree_optionEquivLeft R q
        _ ≤ q.totalDegree := MvPolynomial.degreeOf_le_totalDegree q none
        _ ≤ n := hq.totalDegree_le
    have hhom : ∀ i ≤ P.natDegree, (P.coeff i).IsHomogeneous (n - i) := by
      intro i hi
      apply MvPolynomial.IsHomogeneous.coeff_isHomogeneous_of_optionEquivLeft_symm
        (p := P) (by simpa only [P, AlgEquiv.symm_apply_apply] using hq) i (n - i)
      omega
    have heval : q.eval (fun x ↦ Option.elim x t g) = p.eval f := by
      dsimp only [q]
      rw [MvPolynomial.eval_rename]
      congr 2
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [e, t]
      · simp [e, g, finSuccEquiv'_last_apply_castSucc]
    have hsum : ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).eval g * t ^ i = 0 := by
      rw [← Polynomial.eval₂_eq_sum_range]
      rw [← Polynomial.eval_map]
      rw [← MvPolynomial.optionEquivLeft_elim_eval]
      exact heval.trans hz
    have hcoeff := truncated_relation g t J hKJ htJ hlast (ih g hprefix)
      n P.natDegree hl P.coeff hhom hsum
    have hall (i : ℕ) (d : Fin c →₀ ℕ) : (P.coeff i).coeff d ∈ J := by
      by_cases hi : i ≤ P.natDegree
      · exact hcoeff i hi d
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    intro d
    let m := d.mapDomain e
    have hd : p.coeff d = q.coeff m :=
      (MvPolynomial.coeff_rename_mapDomain e e.injective p d).symm
    rw [hd, ← MvPolynomial.optionEquivLeft_coeff_some_coeff_none R (Fin c) m q]
    exact hall (m none) m.some

/-- Coefficients of any homogeneous zero relation on a regular sequence lie in its ideal.
Source: Stacks Project, Algebra, Tag 00LN, proof of (1).
(blueprint: lem-pur-regular-sequence-higher-homogeneous-relations).

Proof: prove the coefficient assertion for relations in the next ideal power, by induction
on the sequence length. Subtract a homogeneous expansion with coefficients in the ideal
to reduce to a zero relation. Split off the last variable and induct on its largest exponent.
The lower-exponent terms lie in a higher power of the prefix ideal. The length induction
therefore puts the top coefficients multiplied by a power of the last generator in the
prefix ideal. Cancel this power using regularity modulo the prefix. Expand the resulting
prefix-ideal coefficients in its generators, raising the prefix degree by one. Move one
last-generator factor into the coefficients of the preceding exponent and apply the inner
induction. Its coefficient corrections lie in the full ideal, giving the original assertion.
The empty sequence is the constant-polynomial case; the zero exponent is the prefix case.
-/
theorem regularSequence_homogeneous_relation {R : Type u} [CommRing R]
    {c : ℕ} (f : Fin c → R) (hf : RingTheory.Sequence.IsRegular R (List.ofFn f))
    (n : ℕ) (p : MvPolynomial (Fin c) R) (hp : p.IsHomogeneous n) (hz : p.eval f = 0) :
    ∀ d, p.coeff d ∈ Ideal.span (Set.range f) := by
  exact weakly_regular_relation f hf.toIsWeaklyRegular n p hp
    (by rw [hz]; exact zero_mem _)

end Ideal
