/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.JacobianPresentationLift
public import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
@[expose] public section
universe u v
namespace Algebra
private lemma pderiv_none_rename {R : Type*} [CommRing R] {ι : Type*}
    (p : MvPolynomial ι R) :
    MvPolynomial.pderiv none (MvPolynomial.rename some p) = 0 := by
  classical
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename some p h
  cases hi

private lemma det_option {R : Type*} [CommRing R] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix (Option ι) (Option ι) R)
    (h : ∀ j, M none (some j) = 0) :
    M.det = Matrix.det (fun i j ↦ M (some i) (some j)) * M none none := by
  let e := Equiv.optionEquivSumPUnit.{0} ι
  rw [← Matrix.det_reindex_self e M]
  have he : Matrix.reindex e e M = Matrix.fromBlocks
      (fun i j ↦ M (some i) (some j)) (fun i (_ : PUnit.{1}) ↦ M (some i) none)
      0 (fun (_ _ : PUnit.{1}) ↦ M none none) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.reindex_apply, e, h]
  rw [he, Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_unique]

/-- Etaleness and finite presentation of the coefficient lift.
Source: Stacks Project, Tag 04D1.
(blueprint: lem-exc-etale-algebra-lift-etale-fp)

Proof: use the quotient presentation with variables and relations indexed by Option (Fin m).
The old equations have no t term, so their partial derivatives with respect to t vanish. The
last equation t * Delta - 1 has t derivative Delta. Hence the full Jacobian is block triangular
with determinant Delta squared. In the quotient t * Delta = 1, making Delta and its square
units. Pair each old equation with its old variable and the last equation with t. This gives a
square Jacobian presentation; its etale theorem gives etaleness. Finally an etale algebra is
finitely presented, by the finite-presentation field of Algebra.Etale. -/
theorem coefficientLift_etale_fp
    {A : Type u} [CommRing A] (I : Ideal A)
    {B : Type v} [CommRing B] [Algebra (A ⧸ I) B] {m : ℕ}
    (P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m))
    (L : Algebra.SquareJacobianPresentation.CoefficientLift I P) :
    Algebra.Etale A L.LiftRing ∧ Algebra.FinitePresentation A L.LiftRing := by
  classical
  let f : Option (Fin m) → MvPolynomial (Option (Fin m)) A := fun i ↦
    match i with
    | none => MvPolynomial.X none * MvPolynomial.rename some L.jacobianPolynomial - 1
    | some j => MvPolynomial.rename some (L.relation j)
  have hI : L.liftIdeal = Ideal.span (Set.range f) := by
    unfold SquareJacobianPresentation.CoefficientLift.liftIdeal
    apply congrArg Ideal.span
    ext q
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro (⟨j, rfl⟩ | rfl)
      · exact ⟨some j, rfl⟩
      · exact ⟨none, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inr rfl
      | some j => exact Or.inl ⟨j, rfl⟩
  let Q := Algebra.PreSubmersivePresentation.naive (v := f) _root_.id Function.injective_id
  have hdet : Q.jacobiMatrix.det =
      MvPolynomial.rename some L.jacobianPolynomial ^ 2 := by
    have hzero : ∀ j, Q.jacobiMatrix none (some j) = 0 := by
      intro j
      simp [Q, f, pderiv_none_rename]
    rw [det_option Q.jacobiMatrix hzero]
    have hold : (fun i j ↦ Q.jacobiMatrix (some i) (some j) :
        Matrix (Fin m) (Fin m) (MvPolynomial (Option (Fin m)) A)) =
        (MvPolynomial.rename some).mapMatrix
          (Matrix.transpose (fun i j ↦ MvPolynomial.pderiv j (L.relation i) :
            Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) A))) := by
      ext i j
      simp [Q, f, MvPolynomial.pderiv_rename (Option.some_injective _)]
    rw [hold, ← AlgHom.map_det, Matrix.det_transpose]
    simp [Q, f, SquareJacobianPresentation.CoefficientLift.jacobianPolynomial,
      Derivation.leibniz, pderiv_none_rename, pow_two]
  have hunit : IsUnit Q.jacobian := by
    rw [Q.jacobian_eq_jacobiMatrix_det, hdet, map_pow]
    apply IsUnit.pow
    let J := Ideal.span (Set.range f)
    have hrel : f none ∈ J := Ideal.subset_span ⟨none, rfl⟩
    have heq : (Ideal.Quotient.mk J) (MvPolynomial.X none) *
        (Ideal.Quotient.mk J) (MvPolynomial.rename some L.jacobianPolynomial) = 1 := by
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hrel
      simpa only [f, map_sub, map_mul, map_one, sub_eq_zero] using hz
    exact IsUnit.of_mul_eq_one_right _ heq
  let S : Algebra.SquareJacobianPresentation A
      (MvPolynomial (Option (Fin m)) A ⧸ Ideal.span (Set.range f)) (Option (Fin m)) :=
    { toPreSubmersivePresentation := Q
      jacobian_isUnit := hunit
      map_eq_id := rfl }
  have he : Algebra.Etale A L.LiftRing := by
    change Algebra.Etale A (MvPolynomial (Option (Fin m)) A ⧸ L.liftIdeal)
    rw [hI]
    exact S.etale
  exact ⟨he, he.finitePresentation⟩
end Algebra
