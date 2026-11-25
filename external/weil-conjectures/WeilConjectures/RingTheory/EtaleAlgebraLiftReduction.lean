/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.JacobianPresentationLift
@[expose] public section
universe u v
namespace Algebra
/-- The coefficient lift has the specified reduction isomorphism.
Source: Stacks Project, Tag 04D1.
(blueprint: lem-exc-etale-algebra-lift-reduction)

Proof: quotienting the lifted polynomial ring by the constants from I reduces its coefficients
to A/I. The old equations then become P.relation by L.map_relation, and partial derivatives
and determinants commute with this coefficient map. Quotienting further by the old equations
identifies their quotient with B by P's presentation property. The remaining equation is
therefore t * P.jacobian - 1. Since P.jacobian is a unit, evaluation at its inverse gives an
isomorphism B[t]/(t * P.jacobian - 1) to B: its inverse includes B as constants, and their
composites fix B and t, the latter because t * P.jacobian = 1 forces t to be that inverse.
Composing these identifications gives e. On coefficients, old variables, and t its composite
with the quotient map agrees with L.polynomialReduction; polynomial and quotient induction
therefore give e (mk x) = L.reduction x for every x. -/
theorem coefficientLift_reduction_equiv
    {A : Type u} [CommRing A] (I : Ideal A)
    {B : Type v} [CommRing B] [Algebra (A ⧸ I) B] {m : ℕ}
    (P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m))
    (L : Algebra.SquareJacobianPresentation.CoefficientLift I P) :
    ∃ e : (L.LiftRing ⧸ I.map (algebraMap A L.LiftRing)) ≃+* B,
      ∀ x : L.LiftRing,
        e (Ideal.Quotient.mk (I.map (algebraMap A L.LiftRing)) x) = L.reduction x := by
  classical
  let J := I.map (algebraMap A L.LiftRing)
  let Q := L.LiftRing ⧸ J
  let q : MvPolynomial (Option (Fin m)) A →+* Q :=
    (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk L.liftIdeal)
  have hqC (a : A) : q (MvPolynomial.C a) =
      Ideal.Quotient.mk J (algebraMap A L.LiftRing a) := rfl
  -- Descend coefficients and the old variables to the twice-quotiented lift.
  let c : (A ⧸ I) →+* Q := Ideal.Quotient.lift I (q.comp MvPolynomial.C) (by
    intro a ha
    change q (MvPolynomial.C a) = 0
    rw [hqC, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha)
  have hc (a : A) : c (Ideal.Quotient.mk I a) = q (MvPolynomial.C a) := rfl
  let v : Fin m → Q := fun i ↦ q (MvPolynomial.X (some i))
  let g : MvPolynomial (Fin m) (A ⧸ I) →+* Q := MvPolynomial.eval₂Hom c v
  have hg (p : MvPolynomial (Fin m) A) :
      g (MvPolynomial.map (Ideal.Quotient.mk I) p) = q (MvPolynomial.rename some p) := by
    have hh : g.comp (MvPolynomial.map (Ideal.Quotient.mk I)) =
        q.comp (MvPolynomial.rename some).toRingHom := by
      apply MvPolynomial.ringHom_ext <;> intro x <;> simp [g, v, hc]
    exact RingHom.congr_fun hh p
  have hrel (i : Fin m) : g (P.relation i) = 0 := by
    rw [← L.map_relation i, hg]
    change Ideal.Quotient.mk J
      (Ideal.Quotient.mk L.liftIdeal (MvPolynomial.rename some (L.relation i))) = 0
    have hz : Ideal.Quotient.mk L.liftIdeal
        (MvPolynomial.rename some (L.relation i)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)
    rw [hz, map_zero]
  -- The presentation relations vanish, giving the inverse map from B.
  have hker : ∀ p ∈ P.ker, g p = 0 := by
    have hk : P.ker ≤ RingHom.ker g := by
      rw [← P.span_range_relation_eq_ker]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hrel i
    exact fun p hp ↦ hk hp
  let h : B →+* Q := (Ideal.Quotient.lift P.ker g hker).comp
    P.toPresentation.quotientEquiv.symm.toRingEquiv.toRingHom
  have hh (p : MvPolynomial (Fin m) (A ⧸ I)) :
      h ((MvPolynomial.aeval P.val) p) = g p := by
    change (Ideal.Quotient.lift P.ker g hker) (P.toPresentation.quotientEquiv.symm
      ((MvPolynomial.aeval P.val) p)) = g p
    have he : P.toPresentation.quotientEquiv (Ideal.Quotient.mk P.ker p) =
        (MvPolynomial.aeval P.val) p := P.algebraMap_apply p
    rw [← he, AlgEquiv.symm_apply_apply]
    rfl
  have hJ : ∀ x ∈ J, L.reduction x = 0 := by
    have hj : J ≤ RingHom.ker L.reduction := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change L.reduction (algebraMap A L.LiftRing a) = 0
      change L.polynomialReduction (MvPolynomial.C a) = 0
      simp [SquareJacobianPresentation.CoefficientLift.polynomialReduction,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact fun x hx ↦ hj hx
  let f : Q →+* B := Ideal.Quotient.lift J L.reduction hJ
  have hf (p : MvPolynomial (Option (Fin m)) A) : f (q p) = L.polynomialReduction p := rfl
  have hfg : f.comp g = (MvPolynomial.aeval P.val).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp [g, hc, hf, SquareJacobianPresentation.CoefficientLift.polynomialReduction]
    · intro i
      simp [g, v, hf, SquareJacobianPresentation.CoefficientLift.polynomialReduction]
  have hfh (b : B) : f (h b) = b := by
    obtain ⟨p, rfl⟩ := P.aeval_val_surjective b
    rw [hh]
    exact RingHom.congr_fun hfg p
  -- Coefficient reduction commutes with differentiation and determinant.
  have hdet : MvPolynomial.map (Ideal.Quotient.mk I) L.jacobianPolynomial =
      P.jacobiMatrix.det := by
    rw [SquareJacobianPresentation.CoefficientLift.jacobianPolynomial, RingHom.map_det]
    have hm : (MvPolynomial.map (Ideal.Quotient.mk I)).mapMatrix
        (fun i j ↦ MvPolynomial.pderiv j (L.relation i)) = P.jacobiMatrix.transpose := by
      ext i j
      simp [PreSubmersivePresentation.jacobiMatrix_apply, P.map_eq_id,
        ← MvPolynomial.pderiv_map, L.map_relation]
    rw [hm, Matrix.det_transpose]
  have hjac : h P.jacobian = q (MvPolynomial.rename some L.jacobianPolynomial) := by
    rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply, hh, ← hdet, hg]
  -- The extra relation forces the image of t to be the inverse Jacobian.
  have ht : q (MvPolynomial.X none) * h P.jacobian = 1 := by
    rw [hjac, ← map_mul, ← sub_eq_zero, ← map_one q, ← map_sub]
    change Ideal.Quotient.mk J (Ideal.Quotient.mk L.liftIdeal _) = 0
    have hz : Ideal.Quotient.mk L.liftIdeal
        (MvPolynomial.X none * MvPolynomial.rename some L.jacobianPolynomial - 1) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_union_right _ (Set.mem_singleton _))
    rw [hz, map_zero]
  have hinv : h (↑(P.jacobian_isUnit.unit⁻¹) : B) = q (MvPolynomial.X none) := by
    apply (P.jacobian_isUnit.map h).mul_right_cancel
    rw [ht, ← map_mul]
    simp
  have hcoeff (a : A) :
      h (algebraMap (A ⧸ I) B (Ideal.Quotient.mk I a)) = q (MvPolynomial.C a) := by
    simpa [g, hc] using hh (MvPolynomial.C (Ideal.Quotient.mk I a))
  have hvar (i : Fin m) : h (P.val i) = q (MvPolynomial.X (some i)) := by
    simpa [g, v] using hh (MvPolynomial.X i)
  -- The composites fix coefficients and every generator, including t.
  have hpoly : h.comp L.polynomialReduction = q := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa [SquareJacobianPresentation.CoefficientLift.polynomialReduction] using hcoeff a
    · intro i
      cases i with
      | none => simpa [SquareJacobianPresentation.CoefficientLift.polynomialReduction] using hinv
      | some i =>
        simpa [SquareJacobianPresentation.CoefficientLift.polynomialReduction] using hvar i
  have hhf (x : Q) : h (f x) = x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change h (f (q p)) = q p
    rw [hf]
    exact RingHom.congr_fun hpoly p
  let e : Q ≃+* B := { f with invFun := h, left_inv := hhf, right_inv := hfh }
  exact ⟨e, fun x ↦ rfl⟩
end Algebra
