/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal

/-!
# Closed subgroups of `GL_n` cut out by linear equations

An ideal `J` of the coordinate ring `k[GL_n]` is a Hopf ideal as soon as its points
`{g ∈ GL n R | ∀ a ∈ J, g(a) = 0}` form a subgroup of `GL n R` for every `k`-algebra `R`: testing
the Hopf ideal conditions on the universal points (the generic matrix over `k[GL_n] ⧸ J`, and the
universal pair of points over `(k[GL_n] ⧸ J) ⊗ (k[GL_n] ⧸ J)`) gives them
(`Matrix.GeneralLinearGroup.isHopfIdeal_of_forall`).

This applies to the closed subgroups of a closed subgroup `V(I)` of `GL_n` cut out by *linear*
equations `(B g C)_ij = 0` (`Matrix.GeneralLinearGroup.sandwichEquation`) whose solutions in
`Matrix n n R` form a subalgebra for every `R`: an invertible matrix in a subalgebra of
`Matrix n n R` has its inverse there (`Matrix.inv_mem_of_mem_subalgebra`, by Cayley–Hamilton).
Examples are stabilizers of subspaces and centralizers of sets of matrices.

## Main results

- `Matrix.GeneralLinearGroup.isHopfIdeal_of_forall`: an ideal whose points form subgroups is a
  Hopf ideal.
- `Matrix.GeneralLinearGroup.isHopfIdeal_sup_span_of_forall`: the ideal `I ⊔ span E` of `V(I)` cut
  out by extra equations `E` whose solutions form subgroups is a Hopf ideal.

## Blueprint

- `lemma-stable-subspaces-center--1`, `lemma-stable-subspaces-center--2`: the stabilizer of a
subspace and the
  centralizer of a set of matrices are closed subgroup schemes, cut out by linear equations.
-/

@[expose] public section

open WithConv
open scoped Matrix TensorProduct

namespace Matrix

/-- An invertible matrix lying in a subalgebra of `Matrix n n R` has its inverse in the
subalgebra: by Cayley–Hamilton, `M⁻¹` is a polynomial in `M`. -/
theorem inv_mem_of_mem_subalgebra {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (S : Subalgebra R (Matrix n n R)) {M : Matrix n n R} (hM : IsUnit M) (hMS : M ∈ S) :
    M⁻¹ ∈ S := by
  set p := M.charpoly
  obtain ⟨q, hq⟩ : Polynomial.X ∣ p - Polynomial.C (p.coeff 0) := Polynomial.X_dvd_sub_C
  have hdet : IsUnit (p.coeff 0) := by
    have h := det_eq_sign_charpoly_coeff M
    have hu : IsUnit M.det := (isUnit_iff_isUnit_det M).1 hM
    rw [h] at hu
    exact isUnit_of_mul_isUnit_right hu
  have hMq : M * Polynomial.aeval M q = -(p.coeff 0) • (1 : Matrix n n R) := by
    have h0 : Polynomial.aeval M (p - Polynomial.C (p.coeff 0)) =
        Polynomial.aeval M (Polynomial.X * q) := by rw [hq]
    rw [map_sub, aeval_self_charpoly, Polynomial.aeval_C, map_mul, Polynomial.aeval_X,
      zero_sub, Algebra.algebraMap_eq_smul_one] at h0
    rw [← h0, neg_smul]
  have hinv : M⁻¹ = -((hdet.unit⁻¹ : Rˣ) : R) • Polynomial.aeval M q := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_smul, hMq, smul_smul, neg_mul_neg, IsUnit.val_inv_mul, one_smul]
  rw [hinv]
  exact S.smul_mem (Algebra.adjoin_le (Set.singleton_subset_iff.2 hMS)
    (Polynomial.aeval_mem_adjoin_singleton R M)) _

end Matrix

namespace Matrix.GeneralLinearGroup

universe u

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [CommRing k]

/-- **A functor-of-points criterion for Hopf ideals.** An ideal `J` of the coordinate ring of
`GL_n` whose points `{g | ∀ a ∈ J, g(a) = 0}` contain the identity and are stable under products
and inverses, over every `k`-algebra `R`, is a Hopf ideal: `V(J)` is a closed subgroup scheme.
The conditions are tested on the universal points over `k[GL_n] ⧸ J` and
`(k[GL_n] ⧸ J) ⊗ (k[GL_n] ⧸ J)`. -/
theorem isHopfIdeal_of_forall {J : Ideal (CoordinateRing n k)}
    (hone : ∀ a ∈ J, evalAlgHom (1 : GL n k) a = 0)
    (hmul : ∀ (R : Type u) [CommRing R] [Algebra k R] (g h : GL n R),
      (∀ a ∈ J, evalAlgHom g a = 0) → (∀ a ∈ J, evalAlgHom h a = 0) →
        ∀ a ∈ J, evalAlgHom (g * h) a = 0)
    (hinv : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : GL n R),
      (∀ a ∈ J, evalAlgHom g a = 0) → ∀ a ∈ J, evalAlgHom g⁻¹ a = 0) :
    J.IsHopfIdeal k where
  counit_eq_zero a ha := by
    have h := congr(($(evalAlgHom_one (n := n) (k := k) (R := k))).ofConv a)
    rw [ofConv_toConv] at h
    rw [← hone a ha, h, AlgHom.convOne_apply]
    rfl
  map_mkQ_comul_eq_zero a ha := by
    set q := Ideal.Quotient.mkₐ k J
    set B := (CoordinateRing n k ⧸ J) ⊗[k] (CoordinateRing n k ⧸ J)
    let f : CoordinateRing n k →ₐ[k] B := Algebra.TensorProduct.includeLeft.comp q
    let g : CoordinateRing n k →ₐ[k] B := Algebra.TensorProduct.includeRight.comp q
    have hf : ∀ b ∈ J, evalAlgHom (algHomMulEquiv n k B (toConv f)) b = 0 := fun b hb ↦ by
      rw [algHomMulEquiv_apply, evalAlgHom_map_genericUnit]
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hb,
        map_zero]
    have hg : ∀ b ∈ J, evalAlgHom (algHomMulEquiv n k B (toConv g)) b = 0 := fun b hb ↦ by
      rw [algHomMulEquiv_apply, evalAlgHom_map_genericUnit]
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hb,
        map_zero]
    have h := hmul B _ _ hf hg a ha
    rw [← map_mul] at h
    rw [Algebra.TensorProduct.map_mkQ_restrictScalars_eq_zero_iff]
    have key : evalAlgHom (algHomMulEquiv n k B (toConv f * toConv g)) a =
        Algebra.TensorProduct.map q q (Coalgebra.comul a) := by
      rw [algHomMulEquiv_apply, evalAlgHom_map_genericUnit, ofConv_toConv,
        AlgHom.convMul_apply]
      induction Coalgebra.comul (R := k) a using TensorProduct.inductionOn with
      | tmul x y =>
        change (q x ⊗ₜ[k] 1) * (1 ⊗ₜ[k] q y) = q x ⊗ₜ[k] q y
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [← key]
    exact h
  antipode_mem a ha := by
    set q := Ideal.Quotient.mkₐ k J
    have hq : ∀ b ∈ J, evalAlgHom (algHomMulEquiv n k _ (toConv q)) b = 0 := fun b hb ↦ by
      rw [algHomMulEquiv_apply, evalAlgHom_map_genericUnit]
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hb]
    have h := hinv _ _ hq a ha
    rw [← evalAlgHom_comp_antipodeAlgHom, AlgHom.comp_apply, algHomMulEquiv_apply,
      evalAlgHom_map_genericUnit] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h

/-- The points of `V(I ⊔ span E)` are the points of `V(I)` satisfying the equations `E`. -/
theorem evalAlgHom_eq_zero_sup_span_iff {I : Ideal (CoordinateRing n k)}
    {E : Set (CoordinateRing n k)} {R : Type*} [CommRing R] [Algebra k R] {g : GL n R} :
    (∀ a ∈ I ⊔ Ideal.span E, evalAlgHom g a = 0) ↔
      (∀ a ∈ I, evalAlgHom g a = 0) ∧ ∀ e ∈ E, evalAlgHom g e = 0 := by
  refine ⟨fun h ↦ ⟨fun a ha ↦ h a (Ideal.mem_sup_left ha),
    fun e he ↦ h e (Ideal.mem_sup_right (Ideal.subset_span he))⟩, fun ⟨hI, hE⟩ a ha ↦ ?_⟩
  have hle : I ⊔ Ideal.span E ≤ RingHom.ker (evalAlgHom (k := k) g) :=
    sup_le (fun a ha ↦ hI a ha) (Ideal.span_le.2 fun e he ↦ hE e he)
  exact hle ha

/-- **Closed subgroups cut out by extra equations.** If `I` is a Hopf ideal and the solutions of
the equations `E` among the points of `V(I)` form a subgroup over every `k`-algebra `R`, then
`I ⊔ span E` is a Hopf ideal. -/
theorem isHopfIdeal_sup_span_of_forall (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    (E : Set (CoordinateRing n k)) (hone : ∀ e ∈ E, evalAlgHom (1 : GL n k) e = 0)
    (hmul : ∀ (R : Type u) [CommRing R] [Algebra k R] (g h : GL n R), g ∈ zeroLocus I R →
      h ∈ zeroLocus I R → (∀ e ∈ E, evalAlgHom g e = 0) → (∀ e ∈ E, evalAlgHom h e = 0) →
        ∀ e ∈ E, evalAlgHom (g * h) e = 0)
    (hinv : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : GL n R), g ∈ zeroLocus I R →
      (∀ e ∈ E, evalAlgHom g e = 0) → ∀ e ∈ E, evalAlgHom g⁻¹ e = 0) :
    (I ⊔ Ideal.span E).IsHopfIdeal k := by
  refine isHopfIdeal_of_forall (fun a ha ↦ ?_) (fun R _ _ g h hg hh ↦ ?_) (fun R _ _ g hg ↦ ?_)
  · exact evalAlgHom_eq_zero_sup_span_iff.2 ⟨fun a ha ↦ (zeroLocus I k).one_mem a ha, hone⟩ a ha
  · rw [evalAlgHom_eq_zero_sup_span_iff] at hg hh ⊢
    exact ⟨(zeroLocus I R).mul_mem hg.1 hh.1, hmul R g h hg.1 hh.1 hg.2 hh.2⟩
  · rw [evalAlgHom_eq_zero_sup_span_iff] at hg ⊢
    exact ⟨(zeroLocus I R).inv_mem hg.1, hinv R g hg.1 hg.2⟩

/-! ### Linear equations -/

/-- The linear equation `(B g C)_ij = 0` in the entries of `g`, for fixed matrices `B` and `C`
over `k`. -/
noncomputable def sandwichEquation (B C : Matrix n n k) (i j : n) : CoordinateRing n k :=
  ∑ a, ∑ b, algebraMap k _ (B i a * C b j) * coord n k a b

@[simp]
theorem evalAlgHom_sandwichEquation {R : Type*} [CommRing R] [Algebra k R] (B C : Matrix n n k)
    (i j : n) (g : GL n R) :
    evalAlgHom g (sandwichEquation B C i j) =
      (B.map (algebraMap k R) * (g : Matrix n n R) * C.map (algebraMap k R)) i j := by
  simp only [sandwichEquation, map_sum, map_mul, AlgHom.commutes, evalAlgHom_coord,
    Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

end Matrix.GeneralLinearGroup

namespace Subalgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {e : A}

/-- For an idempotent `e` of an `R`-algebra `A`, the subalgebra of the `a` with
`(1 - e) * a * e = 0`. For `A = End(V)` and `e` a projection onto `U`, these are the endomorphisms
preserving `U`. -/
def ofIsIdempotentElem (he : IsIdempotentElem e) : Subalgebra R A where
  carrier := {a | (1 - e) * a * e = 0}
  mul_mem' {a b} ha hb := by
    change (1 - e) * a * e = 0 at ha
    change (1 - e) * b * e = 0 at hb
    change (1 - e) * (a * b) * e = 0
    have hb' : b * e = e * b * e := by
      rw [sub_mul, sub_mul, one_mul, sub_eq_zero] at hb
      exact hb
    calc (1 - e) * (a * b) * e = (1 - e) * a * (e * b * e) := by
          rw [← hb']
          simp only [mul_assoc]
      _ = (1 - e) * a * e * (b * e) := by simp only [mul_assoc]
      _ = 0 := by rw [ha, zero_mul]
  add_mem' {a b} ha hb := by
    change (1 - e) * a * e = 0 at ha
    change (1 - e) * b * e = 0 at hb
    change (1 - e) * (a + b) * e = 0
    rw [mul_add, add_mul, ha, hb, add_zero]
  algebraMap_mem' r := by
    change (1 - e) * algebraMap R A r * e = 0
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, sub_mul, one_mul,
      he.eq, sub_self, smul_zero]

theorem mem_ofIsIdempotentElem (he : IsIdempotentElem e) {a : A} :
    a ∈ ofIsIdempotentElem (R := R) he ↔ (1 - e) * a * e = 0 :=
  Iff.rfl

end Subalgebra
