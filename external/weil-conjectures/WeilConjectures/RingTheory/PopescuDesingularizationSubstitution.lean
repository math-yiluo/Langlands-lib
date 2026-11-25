/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
import WeilConjectures.LinearAlgebra.Matrix.LeftInverseMinors
import WeilConjectures.RingTheory.PopescuTranslatedPresentation
import Mathlib.Tactic.LinearCombination

/-! # Polynomial substitution in the desingularization construction

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR, through the
construction of the polynomials `g` and the two observations on the remaining relations.
-/

@[expose] public section

universe u v w

namespace Algebra

open MvPolynomial

/-- First-order Taylor expansion with remainder in the square of the variable ideal.
The polynomial induction keeps all statements valid over rings with zero divisors. -/
private theorem first_order_expansion {R : Type u} [CommRing R]
    {n : ℕ} (p : MvPolynomial (Fin n) R) :
    ∃ q : MvPolynomial (Fin n) R,
      p = C (constantCoeff p) +
        ∑ i, C (constantCoeff (pderiv i p)) * X i + q ∧
      q ∈ (Ideal.span (Set.range (X (σ := Fin n) (R := R)))) ^ 2 := by
  classical
  let J : Ideal (MvPolynomial (Fin n) R) := Ideal.span (Set.range X)
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp, Ideal.zero_mem _⟩
  | add p p' hp hp' =>
    obtain ⟨q, hq, hmem⟩ := hp
    obtain ⟨q', hq', hmem'⟩ := hp'
    refine ⟨q + q', ?_, Ideal.add_mem _ hmem hmem'⟩
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    linear_combination hq + hq'
  | mul_X p i hp =>
    obtain ⟨q, hq, hmem⟩ := hp
    let l := ∑ j : Fin n, C (constantCoeff (pderiv j p)) * X j
    have hl : l ∈ J := by
      apply Ideal.sum_mem
      intro j _
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have hqJ : q ∈ J := (Ideal.pow_le_self (by decide : 2 ≠ 0)) hmem
    refine ⟨(l + q) * X i, ?_, ?_⟩
    · have hd : ∀ j : Fin n,
          constantCoeff (pderiv j (p * X i)) =
            if j = i then constantCoeff p else 0 := by
        intro j
        by_cases h : j = i
        · subst j
          simp
        · simp [h, pderiv_X_of_ne (Ne.symm h)]
      simp only [map_mul, constantCoeff_X, mul_zero, map_zero, zero_add, hd]
      simp only [apply_ite C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      dsimp [l] at *
      linear_combination hq * X i
    · rw [pow_two]
      exact Ideal.mul_mem_mul (Ideal.add_mem J hl hqJ) (Ideal.subset_span ⟨i, rfl⟩)

/-- The polynomial part of desingularization, before descending evaluation to a quotient
or proving any smoothness. The variable-index universe lift puts the polynomial quotient
in the universe required by the original algebra.

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR, presentation, translation,
scalar left inverse, substitution, and the two observations on the remaining relations.
(blueprint: lem-weil-pbc-popescu-desingularization-substitution).

Proof: choose a strictly standard presentation with `c` selected relations. Translate its
variables by lifts of their images under the section, so their images under `α` are
`π⁴λᵢ` and every relation has constant term in `π⁴R`. Write its linear coefficients as
`rⱼᵢ`. Applying the section to the strictly standard minor identity gives a linear
combination of constant minors equal to `uπ`, where `u = 1 - π³t`. Apply the scalar
left-inverse lemma to obtain `s` with `Σᵢ rⱼᵢsᵢₖ = uπδⱼₖ`. Substitute
`ξᵢ = π²Σₖsᵢₖvₖ + π³wᵢ`. For the first `c` relations, their constant and higher-degree
terms are divisible by `π⁴`, and their linear terms are
`π³(vⱼ + Σᵢrⱼᵢwᵢ)` modulo `π⁴`. Construct the corresponding polynomials `gⱼ` by dividing
these displayed coefficients, obtaining `fⱼ(ξ) = π³gⱼ` and
`gⱼ = vⱼ + Σᵢrⱼᵢwᵢ + πeⱼ`. This is coefficientwise division of explicitly divisible
terms, not cancellation of a possibly zero divisor. All substituted relations lie in
`(π²)`. Substitute into the strictly standard ideal-square relation to get
`πfⱼ(ξ)` in `(g)+(f(ξ))²` for each remaining relation. The chosen lift
`P.σ (algebraMap R A π)` differs from `C π` by an element of the relation ideal, so
replacing it by `C π` changes its product with a relation only by an ideal-square
element. The first `c` relations already lie in `(g)`. The coefficient-ring lift and
the lifted variable indices do not change
any of these identities. This argument does not need annihilator stability or any
Noetherian hypothesis. -/
theorem exists_desingularization_substitution
    (R : Type u) (Λ : Type v) (A : Type w)
    [CommRing R] [CommRing Λ] [CommRing A]
    [Algebra R Λ] [Algebra R A] [FinitePresentation R A]
    (π : R) (α : A →ₐ[R] Λ)
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π))
    (hρ : ∃ ρ :
      (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (R ⧸ Ideal.span {π ^ 4}),
      ∀ (a : A) (r : R),
        ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ r →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (algebraMap R Λ r)) :
    ∃ (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m)) (hc : c ≤ m)
      (s : Fin n → Fin c → R) (lam : Fin n → Λ)
      (r : Fin c → Fin n → R)
      (g e : Fin c → MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R),
      let ξ : Fin n → MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R := fun i ↦
        C π ^ 2 * ∑ k, C (s i k) *
          X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inl k)) +
          C π ^ 3 *
            X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inr i))
      let F := fun j : Fin m ↦ aeval (R := R) ξ (P.relation j)
      (∀ j, g j = (X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inl j)) :
        MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R) +
        ∑ i, C (r j i) *
          X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inr i)) + C π * e j) ∧
      (∀ j, F (Fin.castLE hc j) = C π ^ 3 * g j) ∧
      (∀ j, F j ∈ Ideal.span {C π ^ 2}) ∧
      (∀ j, C π * F j ∈
        Ideal.span (Set.range g) + (Ideal.span (Set.range F)) ^ 2) ∧
      (∀ i, α (P.val i) = algebraMap R Λ π ^ 4 * lam i) := by
  classical
  obtain ⟨n, m, c, P, hc, lam, a, t, hlam, ha, hminor, hrel⟩ :=
    exists_popescu_translated_presentation R Λ A π α hstandard hρ
  let hcm : c ≤ m := le_trans hc (min_le_right n m)
  let r : Fin m → Fin n → R := fun j i ↦ constantCoeff (pderiv i (P.relation j))
  let M : Matrix (Fin n) (Fin c) R := fun i j ↦ r (Fin.castLE hcm j) i
  obtain ⟨S, hS⟩ :=
    (Matrix.scalar_left_inverse_maximal_minors n c
      (le_trans hc (min_le_left n m)) M).1 ((1 - π ^ 3 * t) * π) hminor
  let s : Fin n → Fin c → R := fun i k ↦ S k i
  have hinv (j k : Fin c) :
      ∑ i, r (Fin.castLE hcm j) i * s i k =
        if j = k then (1 - π ^ 3 * t) * π else 0 := by
    have h := congrArg (fun N : Matrix (Fin c) (Fin c) R ↦ N k j) hS
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      M, s, mul_comm, eq_comm] using h
  let T := MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R
  let V : Fin c → T := fun j ↦ X (ULift.up (Sum.inl j))
  let W : Fin n → T := fun i ↦ X (ULift.up (Sum.inr i))
  let ξ : Fin n → T := fun i ↦
    C π ^ 2 * ∑ k, C (s i k) * V k + C π ^ 3 * W i
  let φ : MvPolynomial (Fin n) R →ₐ[R] T := aeval ξ
  let F : Fin m → T := fun j ↦ φ (P.relation j)
  let J : Ideal (MvPolynomial (Fin n) R) := Ideal.span (Set.range X)
  let K : Ideal T := Ideal.span {C π ^ 2}
  have hξ (i : Fin n) : ξ i ∈ K := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨∑ k, C (s i k) * V k + C π * W i, ?_⟩
    dsimp [ξ]
    ring
  have hmap : Ideal.map φ J ≤ K := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simpa [φ] using hξ i
  have hexp (j : Fin m) : ∃ b : T,
      F j = C π ^ 4 * b + ∑ i, C (r j i) * ξ i := by
    obtain ⟨q, hq, hqmem⟩ := first_order_expansion (P.relation j)
    have hqmap : φ q ∈ K ^ 2 := by
      apply (pow_le_pow_left' hmap 2)
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem φ hqmem
    rw [Ideal.span_singleton_pow, ← pow_mul] at hqmap
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hqmap
    refine ⟨C (a j) + b, ?_⟩
    have he := congrArg φ hq
    dsimp only [φ] at he
    simp only [map_add, map_sum, map_mul, aeval_C, aeval_X, ha, map_pow] at he
    change F j = C π ^ 4 * C (a j) + ∑ i, C (r j i) * ξ i + φ q at he
    linear_combination he + hb
  choose b hb using hexp
  have hF (j : Fin m) : F j ∈ K := by
    rw [hb j]
    apply Ideal.add_mem
    · apply Ideal.mem_span_singleton.mpr
      exact ⟨C π ^ 2 * b j, by ring⟩
    · apply Ideal.sum_mem
      intro i _
      exact Ideal.mul_mem_left _ _ (hξ i)
  have hlinear (j : Fin c) :
      (∑ i, C (r (Fin.castLE hcm j) i) * ξ i) =
        C π ^ 3 * (V j + ∑ i, C (r (Fin.castLE hcm j) i) * W i) -
          C π ^ 6 * C t * V j := by
    have hsum : (∑ i, C (r (Fin.castLE hcm j) i) * ξ i) =
        C π ^ 2 * ∑ k, C (∑ i, r (Fin.castLE hcm j) i * s i k) * V k +
          C π ^ 3 * ∑ i, C (r (Fin.castLE hcm j) i) * W i := by
      calc
        _ = ∑ i, (C π ^ 2 *
              ∑ k, C (r (Fin.castLE hcm j) i * s i k) * V k +
                C π ^ 3 * (C (r (Fin.castLE hcm j) i) * W i)) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [ξ]
          simp only [map_mul, mul_add, Finset.mul_sum]
          ring_nf
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          simp only [map_sum, Finset.sum_mul]
    rw [hsum]
    simp only [hinv, apply_ite C, map_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, map_mul, map_sub, map_one, map_pow]
    ring
  let e : Fin c → T := fun j ↦ b (Fin.castLE hcm j) - C π ^ 2 * C t * V j
  let g : Fin c → T := fun j ↦
    V j + ∑ i, C (r (Fin.castLE hcm j) i) * W i + C π * e j
  have hlead (j : Fin c) : F (Fin.castLE hcm j) = C π ^ 3 * g j := by
    rw [hb, hlinear]
    dsimp [g, e]
    ring
  refine ⟨n, m, c, P, hcm, s, lam, (fun j ↦ r (Fin.castLE hcm j)), g, e,
    (fun _ ↦ rfl), hlead, hF, ?_, hlam⟩
  change ∀ j, C π * F j ∈ Ideal.span (Set.range g) +
    (Ideal.span (Set.range F)) ^ 2
  let I : Ideal (MvPolynomial (Fin n) R) := Ideal.span (Set.range P.relation)
  let I₀ : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k}
  let G : Ideal T := Ideal.span (Set.range g)
  let H : Ideal T := Ideal.span (Set.range F)
  have hdelta : C π - P.σ (algebraMap R A π) ∈ I := by
    dsimp only [I]
    rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker]
    simp
  have hcorrect (j : Fin m) : C π * P.relation j ∈ I₀ + I ^ 2 := by
    by_cases hj : j.val < c
    · apply (show I₀ ≤ I₀ + I ^ 2 by rw [Ideal.add_eq_sup]; exact le_sup_left)
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, hj, rfl⟩)
    · have hd : (C π - P.σ (algebraMap R A π)) * P.relation j ∈ I ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul hdelta (Ideal.subset_span ⟨j, rfl⟩)
      have hd' : (C π - P.σ (algebraMap R A π)) * P.relation j ∈ I₀ + I ^ 2 :=
        (show I ^ 2 ≤ I₀ + I ^ 2 by rw [Ideal.add_eq_sup]; exact le_sup_right) hd
      have h := Ideal.add_mem (I₀ + I ^ 2) hd' (hrel j (Nat.le_of_not_gt hj))
      convert h using 1
      ring
  have hI : Ideal.map φ I = H := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hI₀ : Ideal.map φ I₀ ≤ G := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    let j : Fin c := ⟨k.val, hk⟩
    have hcast : Fin.castLE hcm j = k := Fin.ext rfl
    change F k ∈ G
    rw [← hcast, hlead]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  intro j
  have h := Ideal.mem_map_of_mem φ (hcorrect j)
  rw [Ideal.add_eq_sup, Ideal.map_sup, Ideal.map_pow, hI] at h
  have hle : Ideal.map φ I₀ ⊔ H ^ 2 ≤ G + H ^ 2 := by
    rw [Ideal.add_eq_sup]
    exact sup_le_sup hI₀ le_rfl
  have hfinal : φ (C π * P.relation j) ∈ G + H ^ 2 := hle h
  change C π * F j ∈ G + H ^ 2
  have hC : φ (C π) = (C π : T) := by
    change aeval ξ (C π) = (C π : MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R)
    simp only [aeval_C]
    exact congrArg (fun f : R →+* MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R ↦ f π)
      (MvPolynomial.algebraMap_eq (R := R) (σ := ULift.{w} (Fin c ⊕ Fin n)))
  rw [map_mul, hC] at hfinal
  exact hfinal

end Algebra
