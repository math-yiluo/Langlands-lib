/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.RingTheory.Regular.RegularSequenceHigherRelations

/-!
# The associated graded algebra of a regular-sequence ideal

Source: Stacks Project, Algebra, Tags 00LN (part (1)), 061N and 061P
(blueprint: lem-pur-regular-sequence-graded-polynomial).

The canonical map is constructed by polynomial evaluation. Its being a graded algebra
isomorphism is expressed by bijectivity and an equivalence between homogeneity of a
polynomial and membership of its image in the corresponding direct-sum summand.
The basis clause uses the finite, unique expansion criterion of
`def-weil-pbc-free-module`, so it does not choose another scalar action on the pieces.
-/

@[expose] public section

universe u

namespace Ideal

/-- The canonical polynomial-to-associated-graded map of Stacks, Algebra, Tag 061N,
specialized to `M = R` (blueprint: lem-pur-regular-sequence-graded-polynomial).
It sends each variable to the degree-one class of the corresponding generator and
commutes with the quotient-ring structure maps, hence fixes constants in degree zero. -/
noncomputable def regularSequenceGradedPolynomialMap {R : Type u} [CommRing R]
    {c : ℕ} (f : Fin c → R) :
    MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f)) →ₐ[R ⧸ Ideal.span (Set.range f)]
      associatedGraded (Ideal.span (Set.range f)) :=
  MvPolynomial.aeval (fun j ↦
    DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) 1
      (Submodule.Quotient.mk
        (⟨f j, by simpa using Ideal.subset_span (Set.mem_range_self j)⟩ :
          (Ideal.span (Set.range f) ^ 1 : Ideal R))))

set_option backward.isDefEq.respectTransparency false in
private theorem monomial_class {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (d : Fin c →₀ ℕ) :
    ∃ x : (Ideal.span (Set.range f) ^ d.degree : Ideal R),
      x.val = d.prod (fun j k ↦ f j ^ k) ∧
      regularSequenceGradedPolynomialMap f (MvPolynomial.monomial d 1) =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) d.degree
          (Submodule.Quotient.mk x) := by
  classical
  let J := Ideal.span (Set.range f)
  let P := fun d : Fin c →₀ ℕ ↦
    ∃ x : (J ^ d.degree : Ideal R),
      x.val = d.prod (fun j k ↦ f j ^ k) ∧
      regularSequenceGradedPolynomialMap f (MvPolynomial.monomial d 1) =
        DirectSum.of (associatedGradedPiece J) d.degree (Submodule.Quotient.mk x)
  have hzero : P 0 := by
    refine ⟨⟨1, by simp⟩, by simp, ?_⟩
    change regularSequenceGradedPolynomialMap f 1 = _
    rw [map_one]
    exact associatedGraded_one J
  have hadd (d e : Fin c →₀ ℕ) (hd : P d) (he : P e) : P (d + e) := by
    obtain ⟨x, hx, hx'⟩ := hd
    obtain ⟨y, hy, hy'⟩ := he
    dsimp only [P]
    rw [Finsupp.degree.map_add]
    refine ⟨⟨x.val * y.val, by simpa [pow_add] using Ideal.mul_mem_mul x.property y.property⟩,
      ?_, ?_⟩
    · change x.val * y.val = _
      rw [hx, hy, Finsupp.prod_add_index]
      · intro a ha; simp
      · intro a ha b₁ b₂; exact pow_add _ _ _
    · rw [← one_mul (1 : R ⧸ J), ← MvPolynomial.monomial_mul_monomial, map_mul, hx', hy']
      exact associatedGraded_mul J _ _ x y
  have hsingle (j : Fin c) : P (Finsupp.single j 1) := by
    dsimp only [P]
    rw [Finsupp.degree_single]
    refine ⟨⟨f j, by simpa using Ideal.subset_span (Set.mem_range_self j)⟩,
      by simp, ?_⟩
    change regularSequenceGradedPolynomialMap f (MvPolynomial.X j) = _
    exact MvPolynomial.aeval_X (R := R ⧸ J) (S₁ := associatedGraded J) _ j
  change P d
  induction d using Finsupp.induction_linear with
  | zero => exact hzero
  | add d e hd he => exact hadd d e hd he
  | single j k =>
    induction k with
    | zero => simpa using hzero
    | succ k hk =>
      simpa only [Finsupp.single_add] using hadd _ _ hk (hsingle j)

set_option backward.isDefEq.respectTransparency false in
private theorem coeff_monomial_class {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (d : Fin c →₀ ℕ) (r : R) :
    ∃ x : (Ideal.span (Set.range f) ^ d.degree : Ideal R),
      x.val = r * d.prod (fun j k ↦ f j ^ k) ∧
      regularSequenceGradedPolynomialMap f
          (MvPolynomial.monomial d (Ideal.Quotient.mk (Ideal.span (Set.range f)) r)) =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) d.degree
          (Submodule.Quotient.mk x) := by
  obtain ⟨x, hx, hx'⟩ := monomial_class f d
  refine ⟨⟨r * x.val, Ideal.mul_mem_left _ r x.property⟩, by dsimp only; rw [hx], ?_⟩
  have hm : MvPolynomial.monomial d (Ideal.Quotient.mk (Ideal.span (Set.range f)) r) =
      Ideal.Quotient.mk (Ideal.span (Set.range f)) r • MvPolynomial.monomial d 1 := by
    simpa only [smul_eq_mul, mul_one] using
      ((MvPolynomial.monomial d).map_smul
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) r) 1)
  rw [hm, map_smul, hx']
  exact associatedGraded_smul _ _ _ x

set_option backward.isDefEq.respectTransparency false in
private theorem homogeneous_class {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (n : ℕ) (p : MvPolynomial (Fin c) R) (hp : p.IsHomogeneous n) :
    ∃ x : (Ideal.span (Set.range f) ^ n : Ideal R),
      x.val = p.eval f ∧
      regularSequenceGradedPolynomialMap f
          (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span (Set.range f))) p) =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n
          (Submodule.Quotient.mk x) := by
  classical
  let J := Ideal.span (Set.range f)
  have hd (d : p.support) : Finsupp.degree d.val = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp d.property)
  have hmon (d : p.support) :
      ∃ x : (J ^ n : Ideal R),
        x.val = p.coeff d.val * d.val.prod (fun j k ↦ f j ^ k) ∧
        regularSequenceGradedPolynomialMap f
            (MvPolynomial.monomial d.val (Ideal.Quotient.mk J (p.coeff d.val))) =
          DirectSum.of (associatedGradedPiece J) n (Submodule.Quotient.mk x) := by
    have h := coeff_monomial_class f d.val (p.coeff d.val)
    rw [hd d] at h
    exact h
  choose x hx hx' using hmon
  refine ⟨∑ d : p.support, x d, ?_, ?_⟩
  · simp only [Submodule.coe_sum, hx]
    conv_rhs => rw [p.as_sum, map_sum]
    simp only [MvPolynomial.eval_monomial]
    exact Finset.sum_coe_sort p.support (fun d ↦ p.coeff d * d.prod (fun j k ↦ f j ^ k))
  · conv_lhs => rw [p.as_sum, map_sum, map_sum]
    simp only [MvPolynomial.map_monomial]
    rw [← Finset.sum_coe_sort p.support]
    simp only [map_sum, ← Submodule.mkQ_apply]
    apply Finset.sum_congr rfl
    intro d hd
    exact hx' d

set_option backward.isDefEq.respectTransparency false in
private theorem homogeneous_lift {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (n : ℕ) (p : MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f)))
    (hp : p.IsHomogeneous n) :
    ∃ q : MvPolynomial (Fin c) R, q.IsHomogeneous n ∧
      MvPolynomial.map (Ideal.Quotient.mk (Ideal.span (Set.range f))) q = p := by
  obtain ⟨q, hq⟩ := MvPolynomial.map_surjective _ (Ideal.Quotient.mk_surjective) p
  refine ⟨MvPolynomial.homogeneousComponent n q,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩
  ext d
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
  split_ifs with h
  · simpa only [MvPolynomial.coeff_map] using congrArg (fun p ↦ p.coeff d) hq
  · rw [map_zero]
    exact (hp.coeff_eq_zero h).symm

set_option backward.isDefEq.respectTransparency false in
private theorem polynomial_expansion {B : Type u} [CommRing B] {c : ℕ} (n : ℕ)
    (p : MvPolynomial (Fin c) B) (hp : p.IsHomogeneous n) :
    ∃ a : {d : Fin c →₀ ℕ // d.sum (fun _ k ↦ k) = n} →₀ B,
      a.sum (fun d b ↦ MvPolynomial.monomial d.val b) = p := by
  refine ⟨(AddMonoidAlgebra.coeff p).subtypeDomain (fun d ↦ d.sum (fun _ k ↦ k) = n), ?_⟩
  calc
    _ = (AddMonoidAlgebra.coeff p).sum (fun d b ↦ MvPolynomial.monomial d b) :=
      Finsupp.sum_subtypeDomain_index (h := fun d b ↦ MvPolynomial.monomial d b)
        (fun d hd ↦ by
          change d.degree = n
          simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
            hp (Finsupp.mem_support_iff.mp hd))
    _ = p := p.as_sum.symm

set_option backward.isDefEq.respectTransparency false in
private theorem expansion_coeff {B : Type u} [CommRing B] {c : ℕ} (n : ℕ)
    (a : {d : Fin c →₀ ℕ // d.sum (fun _ k ↦ k) = n} →₀ B)
    (d : {d : Fin c →₀ ℕ // d.sum (fun _ k ↦ k) = n}) :
    AddMonoidAlgebra.coeff (a.sum (fun e b ↦ MvPolynomial.monomial e.val b)) d.val = a d := by
  classical
  simpa [Finsupp.sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Subtype.val_inj] using (fun h : a d = 0 ↦ h.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem component_map {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (n : ℕ) (p : MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f))) :
    regularSequenceGradedPolynomialMap f (MvPolynomial.homogeneousComponent n p) =
      DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n
        (regularSequenceGradedPolynomialMap f p n) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d b =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨x, hx, hx'⟩ := coeff_monomial_class f d r
    rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial _ rfl)]
    by_cases h : n = d.degree
    · subst n
      simp only [ite_true, hx', DirectSum.of_eq_same]
    · simp only [ite_eq_right h, map_zero, hx', DirectSum.of_eq_of_ne _ _ _ h]
  | add p q hp hq =>
    simp only [map_add, DirectSum.add_apply, hp, hq]

set_option backward.isDefEq.respectTransparency false in
private theorem homogeneous_kernel {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hrel : ∀ (n : ℕ) (p : MvPolynomial (Fin c) R), p.IsHomogeneous n →
      p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) →
        ∀ d, p.coeff d ∈ Ideal.span (Set.range f))
    (n : ℕ) (p : MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f)))
    (hp : p.IsHomogeneous n) (hz : regularSequenceGradedPolynomialMap f p = 0) : p = 0 := by
  obtain ⟨q, hq, hqp⟩ := homogeneous_lift f n p hp
  obtain ⟨x, hx, hx'⟩ := homogeneous_class f n q hq
  have hzero : Submodule.Quotient.mk x =
      (0 : associatedGradedPiece (Ideal.span (Set.range f)) n) := by
    apply DirectSum.of_injective n
    simpa only [hqp, hz, map_zero] using hx'.symm
  have hmem : q.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) := by
    rw [← hx]
    exact (Submodule.Quotient.mk_eq_zero
      (Submodule.comap (Ideal.span (Set.range f) ^ n : Ideal R).subtype
        (Ideal.span (Set.range f) ^ (n + 1)))).mp hzero
  rw [← hqp]
  ext d
  rw [MvPolynomial.coeff_map]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrel n q hq hmem d)

set_option backward.isDefEq.respectTransparency false in
private theorem bijective_of_relation {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hrel : ∀ (n : ℕ) (p : MvPolynomial (Fin c) R), p.IsHomogeneous n →
      p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) →
        ∀ d, p.coeff d ∈ Ideal.span (Set.range f)) :
    Function.Bijective (regularSequenceGradedPolynomialMap f) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro p hp
    have hc (n : ℕ) : MvPolynomial.homogeneousComponent n p = 0 := by
      apply homogeneous_kernel f hrel n _ (MvPolynomial.homogeneousComponent_isHomogeneous _ _)
      rw [component_map, hp]
      simp
    rw [← MvPolynomial.sum_homogeneousComponent p]
    simp only [hc, Finset.sum_const_zero]
  · intro y
    induction y using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of n y =>
      induction y using Submodule.Quotient.induction_on with
      | _ x =>
        obtain ⟨p, hp, hpx⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f x.val).mp x.property
        obtain ⟨z, hz, hz'⟩ := homogeneous_class f n p hp
        have he : z = x := Subtype.ext (hz.trans hpx)
        exact ⟨MvPolynomial.map (Ideal.Quotient.mk _) p, by simpa only [he] using hz'⟩
    | add x y hx hy =>
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := hy
      exact ⟨p + q, map_add _ _ _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem homogeneous_iff_of_injective {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hi : Function.Injective (regularSequenceGradedPolynomialMap f))
    (n : ℕ) (p : MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f))) :
    p.IsHomogeneous n ↔ ∃ x : associatedGradedPiece (Ideal.span (Set.range f)) n,
      regularSequenceGradedPolynomialMap f p =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n x := by
  constructor
  · intro hp
    exact ⟨regularSequenceGradedPolynomialMap f p n, by
      simpa only [MvPolynomial.homogeneousComponent_eq_self hp] using component_map f n p⟩
  · rintro ⟨x, hx⟩
    have he : MvPolynomial.homogeneousComponent n p = p := by
      apply hi
      rw [component_map, hx, DirectSum.of_eq_same]
    rw [← he]
    exact MvPolynomial.homogeneousComponent_isHomogeneous _ _

set_option backward.isDefEq.respectTransparency false in
private theorem expansion_map {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R) (n : ℕ)
    (a : {d : Fin c →₀ ℕ // d.sum (fun _ k ↦ k) = n} →₀ (R ⧸ Ideal.span (Set.range f))) :
    a.sum (fun d b ↦ b • regularSequenceGradedPolynomialMap f
        (MvPolynomial.monomial d.val 1)) =
      regularSequenceGradedPolynomialMap f (a.sum (fun d b ↦ MvPolynomial.monomial d.val b)) := by
  classical
  change (∑ d ∈ a.support, a d • regularSequenceGradedPolynomialMap f
      (MvPolynomial.monomial d.val 1)) =
    regularSequenceGradedPolynomialMap f
      (∑ d ∈ a.support, MvPolynomial.monomial d.val (a d))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hm : MvPolynomial.monomial d.val (a d) =
      a d • MvPolynomial.monomial d.val 1 := by
    simpa only [smul_eq_mul, mul_one] using
      ((MvPolynomial.monomial d.val).map_smul (a d) 1)
  rw [hm, map_smul]

set_option backward.isDefEq.respectTransparency false in
private theorem formula {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R) (n : ℕ)
    (a : {d : Fin c →₀ ℕ // d.sum (fun _ k ↦ k) = n} →₀ R) :
    ∃ x : (Ideal.span (Set.range f) ^ n : Ideal R),
      x.val = a.sum (fun d r ↦ r * d.val.prod (fun j k ↦ f j ^ k)) ∧
      regularSequenceGradedPolynomialMap f
          (a.sum (fun d r ↦ MvPolynomial.monomial d.val
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) r))) =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n
          (Submodule.Quotient.mk x) := by
  let p : MvPolynomial (Fin c) R := a.sum (fun d r ↦ MvPolynomial.monomial d.val r)
  have hp : p.IsHomogeneous n := by
    apply MvPolynomial.IsHomogeneous.sum
    intro d hd
    exact MvPolynomial.isHomogeneous_monomial _ d.property
  obtain ⟨x, hx, hx'⟩ := homogeneous_class f n p hp
  refine ⟨x, ?_, ?_⟩
  · simpa only [p, Finsupp.sum, map_sum, MvPolynomial.eval_monomial] using hx
  · simpa only [p, Finsupp.sum, map_sum, MvPolynomial.map_monomial] using hx'

set_option backward.isDefEq.respectTransparency false in
private theorem basis_of_bijective {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hb : Function.Bijective (regularSequenceGradedPolynomialMap f))
    (n : ℕ) (x : associatedGradedPiece (Ideal.span (Set.range f)) n) :
    ∃! a : {d : Fin c →₀ ℕ // d.sum (fun _ k ↦ k) = n} →₀
        (R ⧸ Ideal.span (Set.range f)),
      a.sum (fun d b ↦ b • regularSequenceGradedPolynomialMap f
        (MvPolynomial.monomial d.val 1)) =
          DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n x := by
  obtain ⟨p, hp⟩ := hb.2 (DirectSum.of _ n x)
  have hph : p.IsHomogeneous n := (homogeneous_iff_of_injective f hb.1 n p).mpr ⟨x, hp⟩
  obtain ⟨a, ha⟩ := polynomial_expansion n p hph
  refine ⟨a, ?_, ?_⟩
  · dsimp only
    rw [expansion_map, ha, hp]
  · intro b hb'
    have he : b.sum (fun d r ↦ MvPolynomial.monomial d.val r) =
        a.sum (fun d r ↦ MvPolynomial.monomial d.val r) := by
      apply hb.1
      rw [← expansion_map, ← expansion_map, hb']
      rw [expansion_map, ha, hp]
    ext d
    simpa only [expansion_coeff] using congrArg (fun p ↦ p.coeff d.val) he

set_option backward.isDefEq.respectTransparency false in
private theorem relation_of_zero_relation {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
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

/-- A regular sequence has polynomial associated graded algebra, including the formula
on coefficient lifts and the monomial basis in each degree. Source: Stacks, Algebra,
Tags 00LN (part (1)), 061N and 061P
(blueprint: lem-pur-regular-sequence-graded-polynomial).

Proof (the thirteen steps of the node):
1. Use `lem-weil-pbc-associated-graded-ring-structure` for the quotient-algebra
   structure, degree-zero inclusion, product formula and scalar formula.
2. Polynomial evaluation gives the displayed canonical map. Multiplying homogeneous
   classes gives its monomial formula; additivity gives the finite-sum formula.
   Changing a coefficient lift by an element of the ideal changes the sum by an
   element of the next power, so the formula is independent of all coefficient lifts.
3. Expand products of generators to span every ideal power by monomials of that
   degree. Elements of the next power have degree-n expansions with coefficients in J.
4. Induct on the length, in all rings and degrees, to show that a degree-n relation
   modulo the next power has all coefficients in J. For the empty sequence, degree
   zero says the sole coefficient is zero and positive degrees have no monomials.
5. The prefix is regular and the last generator t acts injectively modulo its ideal K;
   repeated cancellation shows that t^l a in K implies a in K.
6. Subtract an expansion with coefficients in J to reduce to a zero relation. Group
   by powers of t and induct on the largest exponent l, with length and degree fixed.
7. At l = 0, apply the outer induction to the regular prefix in degree n.
8. At l > 0, put d = n-l. Lower-exponent terms lie in K^(d+1); the outer induction
   in degree d puts t^l times every top coefficient in K. Cancel t^l by step 5.
9. Expand these top coefficients in the prefix generators. Group terms indexed by
   beta plus a unit multi-index, and move one factor t into the coefficients of the
   exponent-(l-1) terms. This also works for an empty prefix, when the top term is zero.
10. The inner induction puts the modified coefficients in J. Subtract their added
    multiples of t, restore the coefficients subtracted in step 6, and finish both inductions.
11. Lift the coefficients of a homogeneous polynomial in the kernel; step 4 makes
    them zero modulo J. Step 3 supplies a preimage of every homogeneous class.
12. Decompose polynomials and direct-sum elements into finitely many homogeneous
    components. Degreewise injectivity and surjectivity give bijectivity and the
    asserted equivalence of degree conditions, also for the inverse.
13. Transport the unique finite monomial expansions of homogeneous polynomials by
    the degreewise bijection. These are exactly the stated basis expansions; at
    degree zero the basis is the singleton 1, and for an empty sequence in positive
    degree the basis is empty and the piece is zero. -/
theorem regularSequence_gradedPolynomial {R : Type u} [CommRing R]
    {c : ℕ} (f : Fin c → R) (hf : RingTheory.Sequence.IsRegular R (List.ofFn f)) :
    Function.Bijective (regularSequenceGradedPolynomialMap f) ∧
    (∀ (n : ℕ) (p : MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f))),
      p.IsHomogeneous n ↔
        ∃ x : associatedGradedPiece (Ideal.span (Set.range f)) n,
          regularSequenceGradedPolynomialMap f p =
            DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n x) ∧
    (∀ (n : ℕ) (a : {α : Fin c →₀ ℕ // α.sum (fun _ k ↦ k) = n} →₀ R),
      ∃ x : (Ideal.span (Set.range f) ^ n : Ideal R),
        x.val = a.sum (fun α r ↦ r * α.val.prod (fun j k ↦ f j ^ k)) ∧
        regularSequenceGradedPolynomialMap f
            (a.sum (fun α r ↦
              MvPolynomial.monomial α.val (Ideal.Quotient.mk (Ideal.span (Set.range f)) r))) =
          DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n
            (Submodule.Quotient.mk x)) ∧
    (∀ (n : ℕ) (x : associatedGradedPiece (Ideal.span (Set.range f)) n),
      ∃! a : {α : Fin c →₀ ℕ // α.sum (fun _ k ↦ k) = n} →₀
          (R ⧸ Ideal.span (Set.range f)),
        a.sum (fun α b ↦ b • regularSequenceGradedPolynomialMap f
          (MvPolynomial.monomial α.val 1)) =
            DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n x) := by
  have hrel := relation_of_zero_relation f (regularSequence_homogeneous_relation f hf)
  have hb := bijective_of_relation f hrel
  exact ⟨hb, homogeneous_iff_of_injective f hb.1, formula f, basis_of_bijective f hb⟩

end Ideal
