/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

universe u

namespace Polynomial

/-! Auxiliary CRT decomposition statements used by the root-block theorem.
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux)
-/

/-- The degree indices of a monic CRT factorization can be identified.

Proof: degree additivity for monic products gives equal finite cardinalities, and
`Fintype.equivOfCardEq` supplies the equivalence.
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux) -/
theorem adjoinRoot_crt_degree_equiv
    {A : Type u} [CommRing A] (I : Ideal A) [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic) (g h : (A ⧸ I)[X])
    (hg : g.Monic) (hh : h.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h) :
    Nonempty (Fin f.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree)) := by
  have hdeg : f.natDegree = g.natDegree + h.natDegree := by
    rw [← hf.natDegree_map (Ideal.Quotient.mk I), hfactor,
      hg.natDegree_mul hh]
  refine ⟨Fintype.equivOfCardEq ?_⟩
  simp only [Fintype.card_fin, Fintype.card_sum, hdeg]

/-- In the power basis, multiplication by the root is computed by monic remainders. -/
private theorem root_matrix_entry {R : Type*} [CommRing R]
    (p : R[X]) (hp : p.Monic) (i j : Fin p.natDegree) :
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp).basis (AdjoinRoot.root p) i j =
      (X ^ (j.val + 1) %ₘ p).coeff i.val := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (AdjoinRoot.powerBasisAux' hp).repr
    (AdjoinRoot.root p * (AdjoinRoot.powerBasis' hp).basis j) i = _
  rw [(AdjoinRoot.powerBasis' hp).basis_eq_pow]
  change (AdjoinRoot.powerBasisAux' hp).repr
    (AdjoinRoot.root p * AdjoinRoot.root p ^ j.val) i = _
  rw [← pow_succ']
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk]

/-- For a chosen degree identification, CRT supplies the conjugating matrix.

Proof: apply the Chinese remainder algebra equivalence, concatenate the power
bases, and take the coordinate matrix of this equivalence; its inverse gives the
conjugation identity.
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux-matrix) -/
theorem adjoinRoot_crt_matrix_for_degree_equiv
    {A : Type u} [CommRing A] (I : Ideal A) [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic) (g h : (A ⧸ I)[X])
    (hg : g.Monic) (hh : h.Monic) (hcoprime : IsCoprime g h)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h)
    (d : Fin f.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree)) :
    ∃ (U : (Matrix (Fin g.natDegree ⊕ Fin h.natDegree)
        (Fin g.natDegree ⊕ Fin h.natDegree) (A ⧸ I))ˣ),
      U.val * Matrix.reindex d d
          ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
            (AdjoinRoot.root f)).map (Ideal.Quotient.mk I)) * U⁻¹.val =
        Matrix.fromBlocks
          (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis
            (AdjoinRoot.root g)) 0 0
          (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hh).basis
            (AdjoinRoot.root h)) := by
  classical
  let R := A ⧸ I
  let p := f.map (Ideal.Quotient.mk I)
  let J : Ideal R[X] := Ideal.span {g}
  let K : Ideal R[X] := Ideal.span {h}
  have hJK : IsCoprime J K := (Ideal.isCoprime_span_singleton_iff g h).mpr hcoprime
  have hpJK : Ideal.span {p} = J * K := by
    change Ideal.span {p} = Ideal.span {g} * Ideal.span {h}
    rw [Ideal.span_singleton_mul_span_singleton]
    exact congrArg (fun q ↦ Ideal.span {q}) hfactor
  let E : AdjoinRoot p ≃+* AdjoinRoot g × AdjoinRoot h :=
    (Ideal.quotEquivOfEq hpJK).trans (Ideal.quotientMulEquivQuotientProd J K hJK)
  have hE (q : R[X]) : E (AdjoinRoot.mk p q) =
      (AdjoinRoot.mk g q, AdjoinRoot.mk h q) := by
    change ((Ideal.quotientMulEquivQuotientProd J K hJK)
      ((Ideal.quotEquivOfEq hpJK) (Ideal.Quotient.mk _ q))) = _
    rw [Ideal.quotEquivOfEq_mk]
    apply Prod.ext
    · rw [Ideal.quotientMulEquivQuotientProd_fst]
      rfl
    · rw [Ideal.quotientMulEquivQuotientProd_snd]
      rfl
  let e : AdjoinRoot p ≃ₐ[R] AdjoinRoot g × AdjoinRoot h :=
    AlgEquiv.ofRingEquiv (f := E) (fun a ↦ by
      change E (AdjoinRoot.mk p (C a)) =
        (AdjoinRoot.mk g (C a), AdjoinRoot.mk h (C a))
      exact hE (C a))
  have he : e (AdjoinRoot.root p) = (AdjoinRoot.root g, AdjoinRoot.root h) := hE X
  have hp : p.Monic := hf.map (Ideal.Quotient.mk I)
  let c : Fin p.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree) :=
    (finCongr (hf.natDegree_map (Ideal.Quotient.mk I))).trans d
  let b := (AdjoinRoot.powerBasis' hp).basis.reindex c
  let b' := (AdjoinRoot.powerBasis' hg).basis.prod (AdjoinRoot.powerBasis' hh).basis
  have hM : Algebra.leftMulMatrix b (AdjoinRoot.root p) =
      Matrix.reindex d d
        ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
          (AdjoinRoot.root f)).map (Ideal.Quotient.mk I)) := by
    ext i j
    simp only [b, Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
    rw [← Algebra.leftMulMatrix_eq_repr_mul, root_matrix_entry,
      ← Algebra.leftMulMatrix_eq_repr_mul, root_matrix_entry]
    change (X ^ ((d.symm j).val + 1) %ₘ p).coeff (d.symm i).val = _
    rw [← coeff_map, map_modByMonic _ hf, Polynomial.map_pow, Polynomial.map_X]
  let U : (Matrix (Fin g.natDegree ⊕ Fin h.natDegree)
      (Fin g.natDegree ⊕ Fin h.natDegree) R)ˣ :=
    { val := LinearMap.toMatrix b b' e.toLinearMap
      inv := LinearMap.toMatrix b' b e.symm.toLinearMap
      val_inv := by
        rw [← LinearMap.toMatrix_comp b' b b']
        simp [LinearMap.toMatrix_id]
      inv_val := by
        rw [← LinearMap.toMatrix_comp b b' b]
        simp [LinearMap.toMatrix_id] }
  refine ⟨U, ?_⟩
  rw [← hM]
  change LinearMap.toMatrix b b' e.toLinearMap *
      Algebra.leftMulMatrix b (AdjoinRoot.root p) *
      LinearMap.toMatrix b' b e.symm.toLinearMap = _
  rw [Algebra.leftMulMatrix_apply, ← LinearMap.toMatrix_comp b b b',
    ← LinearMap.toMatrix_comp b' b b']
  have hconj :
      (e.toLinearMap.comp (Algebra.lmul R (AdjoinRoot p) (AdjoinRoot.root p))).comp
        e.symm.toLinearMap =
      (Algebra.lmul R (AdjoinRoot g) (AdjoinRoot.root g)).prodMap
        (Algebra.lmul R (AdjoinRoot h) (AdjoinRoot.root h)) := by
    apply LinearMap.ext
    intro x
    change e (AdjoinRoot.root p * e.symm x) =
      (AdjoinRoot.root g * x.1, AdjoinRoot.root h * x.2)
    rw [map_mul, he, e.apply_symm_apply]
    rfl
  rw [hconj]
  exact LinearMap.toMatrix_prodMap (AdjoinRoot.powerBasis' hg).basis
    (AdjoinRoot.powerBasis' hh).basis _ _

end Polynomial
