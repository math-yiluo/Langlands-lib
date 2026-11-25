/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra
public import WeilConjectures.RingTheory.QuasiRegular

/-!
# The associated graded ring of a regular sequence

Let `I = (a₁, …, a_c)` be an ideal of a commutative ring `R`. The associated graded ring of `I` is
the quotient `R[t, I t⁻¹] / (t) = ⨁_{d ≥ 0} I^d / I^{d+1}` of the extended Rees algebra. Sending
`Xₖ` to the class of `aₖ t⁻¹` defines a surjection
`(R / I)[X₁, …, X_c] ⟶ R[t, I t⁻¹] / (t)` (`Ideal.mvPolynomialToReesQuot`), which is an isomorphism
when `a` is a regular sequence (`Ideal.bijective_mvPolynomialToReesQuot`), by quasi-regularity
(`MvPolynomial.coeff_mem_of_eval_mem_pow_succ`).
-/

@[expose] public section

open LaurentPolynomial

namespace Ideal

variable {R : Type*} [CommRing R]

/-- The coefficient of `t^j` of an element of the extended Rees algebra `R[t, I t⁻¹]` lies in
`I^{-j}` (with `I^{-j} = R` for `j ≥ 0`). -/
lemma coeff_mem_pow_of_mem_extendedReesAlgebra {I : Ideal R} {x : R[T;T⁻¹]}
    (hx : x ∈ I.extendedReesAlgebra) (j : ℤ) : x.coeff j ∈ I ^ (-j).toNat := by
  induction hx using Algebra.adjoin_induction generalizing j with
  | mem y hy =>
    rcases hy with rfl | ⟨z, hz, rfl⟩
    · rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs with h
      · subst h; simp
      · exact zero_mem _
    · change (C z * T (-1)).coeff j ∈ _
      rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs with h
      · subst h; simpa using hz
      · exact zero_mem _
  | algebraMap r =>
    rw [← LaurentPolynomial.C_eq_algebraMap, C_apply]
    split_ifs with h
    · subst h; simp
    · exact zero_mem _
  | add x y _ _ hx hy =>
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; exact add_mem (hx j) (hy j)
  | mul x y _ _ hx hy =>
    classical
    rw [AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    refine Ideal.sum_mem _ fun p _ ↦ Ideal.sum_mem _ fun q _ ↦ ?_
    split_ifs with h
    · refine Ideal.pow_le_pow_right (n := (-p).toNat + (-q).toNat) (by omega) ?_
      rw [pow_add]
      exact Ideal.mul_mem_mul (hx p) (hy q)
    · exact zero_mem _

variable {c : ℕ} (a : Fin c → R)

/-- The generator `aₖ t⁻¹` of the extended Rees algebra of `I = (a)`. -/
noncomputable def reesGen (k : Fin c) : (span (Set.range a)).extendedReesAlgebra :=
  ⟨C (a k) * T (-1), C_mul_T_neg_one_mem_extendedReesAlgebra (subset_span ⟨k, rfl⟩)⟩

variable (I : Ideal R)

lemma algebraMap_mem_span_extendedReesAlgebraT {x : R} (hx : x ∈ I) :
    algebraMap R I.extendedReesAlgebra x ∈ span {I.extendedReesAlgebraT} := by
  refine mem_span_singleton'.2 ⟨⟨C x * T (-1), C_mul_T_neg_one_mem_extendedReesAlgebra hx⟩,
    Subtype.ext ?_⟩
  simp only [MulMemClass.coe_mul, coe_extendedReesAlgebraT, coe_algebraMap_extendedReesAlgebra,
    mul_assoc, ← T_add]
  simp

/-- The inclusion `R / I ⟶ R[t, I t⁻¹] / (t)` of the degree zero part. -/
noncomputable def quotientToReesQuot :
    R ⧸ I →+* I.extendedReesAlgebra ⧸ span {I.extendedReesAlgebraT} :=
  Quotient.lift I ((Quotient.mk _).comp (algebraMap R _)) fun _ hx ↦
    Quotient.eq_zero_iff_mem.2 (algebraMap_mem_span_extendedReesAlgebraT I hx)

/-- The map `(R / I)[X₁, …, X_c] ⟶ R[t, I t⁻¹] / (t)`, `Xₖ ↦ aₖ t⁻¹`, for `I = (a)`. -/
noncomputable def mvPolynomialToReesQuot :
    MvPolynomial (Fin c) (R ⧸ span (Set.range a)) →+*
      (span (Set.range a)).extendedReesAlgebra ⧸
        span {(span (Set.range a)).extendedReesAlgebraT} :=
  MvPolynomial.eval₂Hom (quotientToReesQuot _) fun k ↦ Quotient.mk _ (reesGen a k)

/-- The map `R[X₁, …, X_c] ⟶ R[t, I t⁻¹]`, `Xₖ ↦ aₖ t⁻¹`. -/
noncomputable def mvPolynomialToRees :
    MvPolynomial (Fin c) R →+* (span (Set.range a)).extendedReesAlgebra :=
  MvPolynomial.eval₂Hom (algebraMap R _) (reesGen a)

lemma mvPolynomialToReesQuot_map (P : MvPolynomial (Fin c) R) :
    mvPolynomialToReesQuot a (MvPolynomial.map (Quotient.mk _) P) =
      Quotient.mk _ (mvPolynomialToRees a P) := by
  have : (mvPolynomialToReesQuot a).comp (MvPolynomial.map (Quotient.mk _)) =
      (Quotient.mk _).comp (mvPolynomialToRees a) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) fun k ↦ ?_
    · simp [mvPolynomialToReesQuot, mvPolynomialToRees, quotientToReesQuot]
    · simp [mvPolynomialToReesQuot, mvPolynomialToRees]
  exact congr($this P)

lemma coe_mvPolynomialToRees_monomial (m : Fin c →₀ ℕ) (r : R) :
    (mvPolynomialToRees a (MvPolynomial.monomial m r) : R[T;T⁻¹]) =
      C (r * m.prod fun i e ↦ a i ^ e) * T (-1) ^ m.degree := by
  rw [mvPolynomialToRees, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
    MulMemClass.coe_mul, coe_algebraMap_extendedReesAlgebra, map_mul, mul_assoc]
  congr 1
  rw [Finsupp.prod, Finsupp.prod, SubmonoidClass.coe_finsetProd, map_prod,
    show m.degree = ∑ i ∈ m.support, m i from rfl,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp [reesGen, mul_pow]

/-- For a homogeneous polynomial `G` of degree `d`, `G(a t⁻¹) = G(a) t^{-d}`. -/
lemma coe_mvPolynomialToRees_of_isHomogeneous {G : MvPolynomial (Fin c) R} {d : ℕ}
    (hG : G.IsHomogeneous d) :
    (mvPolynomialToRees a G : R[T;T⁻¹]) = C (MvPolynomial.eval a G) * T (-1) ^ d := by
  conv_lhs => rw [← G.support_sum_monomial_coeff]
  rw [map_sum, AddSubmonoidClass.coe_finsetSum, MvPolynomial.eval_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [coe_mvPolynomialToRees_monomial, hG.degree_eq_sum_deg_support hm, Finsupp.prod]
  rfl

/-- The map `(R / I)[X₁, …, X_c] ⟶ R[t, I t⁻¹] / (t)` is surjective: the extended Rees algebra is
generated by `t`, which vanishes modulo `t`, by `R`, and by the elements `x t⁻¹ = ∑ cₖ aₖ t⁻¹`. -/
theorem surjective_mvPolynomialToReesQuot : Function.Surjective (mvPolynomialToReesQuot a) := by
  intro z
  obtain ⟨⟨x, hx⟩, rfl⟩ := Quotient.mk_surjective z
  change Quotient.mk _ ⟨x, hx⟩ ∈ (mvPolynomialToReesQuot a).range
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨w, hw, rfl⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, Quotient.eq_zero_iff_mem]
      exact subset_span (Set.mem_singleton_iff.2 rfl)
    · obtain ⟨c', rfl⟩ := (mem_span_range_iff_exists_fun).1 hw
      refine ⟨∑ k, MvPolynomial.C (Quotient.mk _ (c' k)) * MvPolynomial.X k, ?_⟩
      have : (⟨C (∑ k, c' k * a k) * T (-1), C_mul_T_neg_one_mem_extendedReesAlgebra hw⟩ :
          (span (Set.range a)).extendedReesAlgebra) = ∑ k, algebraMap R _ (c' k) * reesGen a k := by
        apply Subtype.ext
        simp [reesGen, map_sum, Finset.sum_mul, mul_assoc]
      rw [this]
      simp [mvPolynomialToReesQuot, quotientToReesQuot]
  | algebraMap r =>
    refine ⟨MvPolynomial.C (Quotient.mk _ r), ?_⟩
    simp [mvPolynomialToReesQuot, quotientToReesQuot]
    rfl
  | add x y hx hy hx' hy' =>
    exact add_mem hx' hy'
  | mul x y hx hy hx' hy' =>
    exact mul_mem hx' hy'

/-- The coefficient of `t^{-d}` of `F(a t⁻¹)` is `F_d(a)`, `F_d` the homogeneous component of
degree `d` of `F`. -/
lemma coeff_mvPolynomialToRees (P : MvPolynomial (Fin c) R) (d : ℕ) :
    (mvPolynomialToRees a P : R[T;T⁻¹]).coeff (-(d : ℤ)) =
      MvPolynomial.eval a (MvPolynomial.homogeneousComponent d P) := by
  conv_lhs => rw [← P.sum_homogeneousComponent]
  rw [map_sum, AddSubmonoidClass.coe_finsetSum, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp_rw [coe_mvPolynomialToRees_of_isHomogeneous a
    (MvPolynomial.homogeneousComponent_isHomogeneous _ _), T_pow, ← single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hb; rw [ite_eq_right (by omega)]
  · intro hd
    rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by simpa using hd)]
    simp

/-- **The associated graded ring of a regular sequence is a polynomial ring.** For a regular
sequence `a` (`MvPolynomial.IsRevRegular`), the map `(R / I)[X₁, …, X_c] ⟶ R[t, I t⁻¹] / (t)`,
`Xₖ ↦ aₖ t⁻¹`, is injective. -/
theorem injective_mvPolynomialToReesQuot (ha : MvPolynomial.IsRevRegular a) :
    Function.Injective (mvPolynomialToReesQuot a) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective _ Quotient.mk_surjective P
  rw [mvPolynomialToReesQuot_map, Quotient.eq_zero_iff_mem] at hP
  obtain ⟨w, hw⟩ := mem_span_singleton'.1 hP
  have hcoeff (d : ℕ) : MvPolynomial.eval a (MvPolynomial.homogeneousComponent d P) ∈
      span (Set.range a) ^ (d + 1) := by
    rw [← coeff_mvPolynomialToRees, ← hw]
    simp only [MulMemClass.coe_mul, coe_extendedReesAlgebraT, T,
      AddMonoidAlgebra.coeff_mul_single_apply, mul_one]
    have := coeff_mem_pow_of_mem_extendedReesAlgebra w.2 (-(d : ℤ) - 1)
    rwa [show (-(-(d : ℤ) - 1)).toNat = d + 1 by omega] at this
  ext m
  rw [MvPolynomial.coeff_map]
  change _ = (0 : R ⧸ span (Set.range a))
  rw [Quotient.eq_zero_iff_mem]
  have := MvPolynomial.coeff_mem_of_eval_mem_pow_succ ha m.degree
    (MvPolynomial.homogeneousComponent_isHomogeneous _ _) (hcoeff m.degree) m
  rwa [MvPolynomial.coeff_homogeneousComponent, ite_eq_left rfl] at this

/-- For a regular sequence `a`, `(R / I)[X₁, …, X_c] ≅ R[t, I t⁻¹] / (t) = ⨁_d I^d / I^{d+1}`. -/
noncomputable def mvPolynomialEquivReesQuot (ha : MvPolynomial.IsRevRegular a) :
    MvPolynomial (Fin c) (R ⧸ span (Set.range a)) ≃+*
      (span (Set.range a)).extendedReesAlgebra ⧸
        span {(span (Set.range a)).extendedReesAlgebraT} :=
  RingEquiv.ofBijective _
    ⟨injective_mvPolynomialToReesQuot a ha, surjective_mvPolynomialToReesQuot a⟩

end Ideal

namespace Ideal

variable {R : Type*} [CommRing R] {c : ℕ} (a : Fin c → R) {J : Ideal R}

/-- `(R / J)[X₁, …, X_c] ≅ R[t, J t⁻¹] / (t)` for an ideal `J` generated by a regular sequence. -/
noncomputable def mvPolynomialEquivReesQuotOfEq (ha : MvPolynomial.IsRevRegular a)
    (h : span (Set.range a) = J) :
    MvPolynomial (Fin c) (R ⧸ J) ≃+* J.extendedReesAlgebra ⧸ span {J.extendedReesAlgebraT} := by
  subst h; exact mvPolynomialEquivReesQuot a ha

lemma mvPolynomialEquivReesQuotOfEq_C (ha : MvPolynomial.IsRevRegular a)
    (h : span (Set.range a) = J) (x : R ⧸ J) :
    mvPolynomialEquivReesQuotOfEq a ha h (MvPolynomial.C x) = quotientToReesQuot J x := by
  subst h
  simp [mvPolynomialEquivReesQuotOfEq, mvPolynomialEquivReesQuot, mvPolynomialToReesQuot]

lemma mvPolynomialEquivReesQuotOfEq_X (ha : MvPolynomial.IsRevRegular a)
    (h : span (Set.range a) = J) (k : Fin c) :
    mvPolynomialEquivReesQuotOfEq a ha h (MvPolynomial.X k) =
      Quotient.mk _ ⟨LaurentPolynomial.C (a k) * T (-1),
        C_mul_T_neg_one_mem_extendedReesAlgebra (h ▸ subset_span ⟨k, rfl⟩)⟩ := by
  subst h
  simp [mvPolynomialEquivReesQuotOfEq, mvPolynomialEquivReesQuot, mvPolynomialToReesQuot,
    reesGen]

end Ideal
