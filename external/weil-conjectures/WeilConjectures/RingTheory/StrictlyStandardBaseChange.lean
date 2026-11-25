/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.FiniteStability

/-!
# Base change of elementary and strictly standard elements

Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07CC
(blueprint: lem-weil-pbc-strictly-standard-base-change).

Mathlib writes the base change as `R' ⊗[R] A`, with its canonical left `R'`-algebra
structure. Tensor commutativity identifies `1 ⊗ a` with the source's `a ⊗ 1`
in `A ⊗[R] R'` as an `R'`-algebra.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

private theorem baseChange_aeval
    {R : Type u} {A : Type v} {R' : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    {n m : ℕ} (P : Presentation R A (Fin n) (Fin m))
    (f : MvPolynomial (Fin n) R) :
    MvPolynomial.aeval (P.baseChange R').val (MvPolynomial.map (algebraMap R R') f) =
      TensorProduct.includeRight (MvPolynomial.aeval P.val f) := by
  rw [MvPolynomial.aeval_map_algebraMap]
  exact (MvPolynomial.comp_aeval_apply P.val
    (TensorProduct.includeRight (R := R) (A := R')) f).symm

private theorem baseChange_minor
    {R : Type u} {A : Type v} {R' : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    {n m c : ℕ} (P : Presentation R A (Fin n) (Fin m))
    (vars : Fin c → Fin n) (fs : Fin c → Fin m) :
    Matrix.det (fun i j : Fin c ↦
      MvPolynomial.aeval (P.baseChange R').val
        (MvPolynomial.pderiv (vars i) ((P.baseChange R').relation (fs j)))) =
    TensorProduct.includeRight (R := R) (A := R')
      (Matrix.det (fun i j : Fin c ↦
        MvPolynomial.aeval P.val (MvPolynomial.pderiv (vars i) (P.relation (fs j))))) := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp only [Presentation.baseChange_relation, MvPolynomial.pderiv_map]
  exact baseChange_aeval P _

private theorem baseChange_relationCondition
    {R : Type u} {A : Type v} {R' : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    {n m c : ℕ} (P : Presentation R A (Fin n) (Fin m)) (a : A)
    (h : ∀ j : Fin m, c ≤ j.val →
      P.σ a * P.relation j ∈
        Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
          (Ideal.span (Set.range P.relation)) ^ 2) :
    ∀ j : Fin m, c ≤ j.val →
      (P.baseChange R').σ (1 ⊗ₜ[R] a) * (P.baseChange R').relation j ∈
        Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = (P.baseChange R').relation k} +
          (Ideal.span (Set.range (P.baseChange R').relation)) ^ 2 := by
  let κ := MvPolynomial.map (algebraMap R R') (σ := Fin n)
  let Q := P.baseChange R'
  have hfirst : Ideal.map κ
      (Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k}) =
      Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = Q.relation k} := by
    rw [Ideal.map_span]
    congr 1
    ext f
    constructor
    · rintro ⟨g, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨P.relation k, ⟨k, hk, rfl⟩, rfl⟩
  have hall : Ideal.map κ (Ideal.span (Set.range P.relation)) =
      Ideal.span (Set.range Q.relation) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  intro j hj
  have hm := Ideal.mem_map_of_mem κ (h j hj)
  rw [map_mul, Ideal.add_eq_sup, Ideal.map_sup, Ideal.map_pow, hfirst, hall] at hm
  have hd : Q.σ (1 ⊗ₜ[R] a) - κ (P.σ a) ∈ Ideal.span (Set.range Q.relation) := by
    rw [Q.span_range_relation_eq_ker, Q.ker_eq_ker_aeval_val, RingHom.mem_ker]
    rw [map_sub, Q.aeval_val_σ, baseChange_aeval, P.aeval_val_σ]
    simp only [TensorProduct.includeRight_apply, sub_self]
  have hr : Q.relation j ∈ Ideal.span (Set.range Q.relation) :=
    Ideal.subset_span ⟨j, rfl⟩
  have hsq : (Q.σ (1 ⊗ₜ[R] a) - κ (P.σ a)) * Q.relation j ∈
      (Ideal.span (Set.range Q.relation)) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hd hr
  have hsum := Ideal.add_mem _ hm (Ideal.mem_sup_right hsq)
  rw [Ideal.add_eq_sup]
  change κ (P.σ a) * Q.relation j +
    (Q.σ (1 ⊗ₜ[R] a) - κ (P.σ a)) * Q.relation j ∈ _ at hsum
  convert hsum using 1
  ring

/-- Elementary standard and strictly standard elements remain so under arbitrary base change.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07CC
(blueprint: lem-weil-pbc-strictly-standard-base-change).

Proof:
1. Choose the presentation and integer `c` witnessing the given standardness
   (theorem-finite-etale-covers-proper-henselian--2). Base change the presentation, keeping the
   same numbers of variables and relations and the same `c`
   (def-weil-pbc-finitely-presented-algebra, lem-weil-pbc-presentation-base-change).
   The resulting algebra is finitely presented
   (lem-weil-pbc-finite-presentation-base-change-composition).
2. The new presentation map composed with the coefficient map equals the old presentation
   map followed by the tensor inclusion: both maps agree on coefficients and variables
   (def-weil-pbc-mv-polynomial-ring). In particular a polynomial lift of `a` maps to a lift
   of `1 ⊗ a`, and the relation ideals map into the new relation ideals.
3. Partial derivatives commute with the coefficient map
   (lem-weil-pbc-partial-derivative-coefficient-map,
   def-weil-pbc-polynomial-partial-derivative). The determinant's Leibniz formula then
   shows that every Jacobian minor maps to the corresponding new minor.
4. Apply the tensor inclusion to the elementary standard multiple identity, respectively
   the strictly standard sum identity. This gives the first condition of
   theorem-finite-etale-covers-proper-henselian--2 with the base-changed coefficients.
5. Apply the coefficient map to each expression of a lifted element times a remaining
   relation in the ideal of the first `c` relations plus the square of the relation ideal.
   The resulting expression satisfies the second condition in the new presentation.
   Independence of the polynomial lift is part of theorem-finite-etale-covers-proper-henselian--2.
   These witnesses establish both conclusions. -/
theorem standardElements_baseChange
    {R : Type u} {A : Type v} {R' : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    [FinitePresentation R A] (a : A) :
    (IsElementaryStandardElement (R := R) a →
      IsElementaryStandardElement (R := R') (1 ⊗ₜ[R] a : R' ⊗[R] A)) ∧
    (IsStrictlyStandardElement (R := R) a →
      IsStrictlyStandardElement (R := R') (1 ⊗ₜ[R] a : R' ⊗[R] A)) := by
  classical
  constructor
  · rintro ⟨n, m, c, P, hc, a', ha, hrel⟩
    refine ⟨n, m, c, P.baseChange R', hc, 1 ⊗ₜ[R] a', ?_,
      baseChange_relationCondition P a hrel⟩
    rw [baseChange_minor]
    change TensorProduct.includeRight (R := R) (A := R') a = _
    rw [ha, map_mul]
    rfl
  · rintro ⟨n, m, c, P, hc, a', ha, hrel⟩
    refine ⟨n, m, c, P.baseChange R', hc, fun s ↦ 1 ⊗ₜ[R] a' s, ?_,
      baseChange_relationCondition P a hrel⟩
    change TensorProduct.includeRight (R := R) (A := R') a = _
    rw [ha, map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [map_mul, AlgHom.map_det]
    congr 1
    congr 1
    ext j i
    simp only [Presentation.baseChange_relation, MvPolynomial.pderiv_map]
    exact (baseChange_aeval P _).symm

end Algebra
