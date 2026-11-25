/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.LinearAlgebra.IdempotentCharpoly
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Coprime.Basic
import WeilConjectures.RingTheory.AdjoinRootCRTMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-! # Reduction of determinant polynomials on the two CRT summands

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), reduction of characteristic polynomials.
(blueprint: lem-weil-pbc-adjoinRoot-idempotent-charpoly-map)
-/

@[expose] public section

universe u

namespace Polynomial

private theorem idempotentCharpoly_map {R S : Type*} [CommRing R] [CommRing S]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : R →+* S) (T P : Matrix n n R) :
    (Matrix.idempotentCharpoly T P).map φ =
      Matrix.idempotentCharpoly (T.map φ) (P.map φ) := by
  unfold Matrix.idempotentCharpoly
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  rw [map_add, map_sub, map_one, map_mul]
  change 1 - (C.mapMatrix P).map (Polynomial.map φ) +
    T.charmatrix.map (Polynomial.map φ) * (C.mapMatrix P).map (Polynomial.map φ) = _
  rw [← Matrix.charmatrix_map]
  congr 2 <;> ext i j <;> simp

private theorem idempotentCharpoly_reindex {R : Type*} [CommRing R]
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (d : n ≃ m) (T P : Matrix n n R) :
    Matrix.idempotentCharpoly (Matrix.reindex d d T) (Matrix.reindex d d P) =
      Matrix.idempotentCharpoly T P := by
  unfold Matrix.idempotentCharpoly
  rw [Matrix.charmatrix_reindex]
  have hC : Polynomial.C.mapMatrix (Matrix.reindex d d P) =
      Matrix.reindex d d (Polynomial.C.mapMatrix P) := rfl
  rw [hC]
  change (1 - Matrix.reindexAlgEquiv R[X] R[X] d (Polynomial.C.mapMatrix P) +
    Matrix.reindexAlgEquiv R[X] R[X] d T.charmatrix *
      Matrix.reindexAlgEquiv R[X] R[X] d (Polynomial.C.mapMatrix P)).det = _
  rw [← map_mul, ← map_one (Matrix.reindexAlgEquiv R[X] R[X] d), ← map_sub, ← map_add]
  exact Matrix.det_reindex_self d _

private theorem idempotentCharpoly_conj {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] (U : (Matrix n n R)ˣ)
    (T P : Matrix n n R) :
    Matrix.idempotentCharpoly (U.val * T * U⁻¹.val) (U.val * P * U⁻¹.val) =
      Matrix.idempotentCharpoly T P := by
  let V := Units.map (Polynomial.C.mapMatrix : Matrix n n R →+* Matrix n n R[X]).toMonoidHom U
  have hV : V.val * V⁻¹.val = 1 := Units.mul_inv V
  have hV' : V⁻¹.val * V.val = 1 := Units.inv_mul V
  have hscalar : V.val * Matrix.scalar n (X : R[X]) =
      Matrix.scalar n (X : R[X]) * V.val :=
    (Matrix.scalar_comm X (fun _ => Commute.all _ _) V.val).symm
  have hch : (U.val * T * U⁻¹.val).charmatrix =
      V.val * T.charmatrix * V⁻¹.val := by
    unfold Matrix.charmatrix
    simp only [map_mul]
    change Matrix.scalar n X - V.val * Polynomial.C.mapMatrix T * V⁻¹.val = _
    rw [mul_sub, sub_mul, hscalar]
    simp only [Matrix.mul_assoc, Units.mul_inv, mul_one]
  unfold Matrix.idempotentCharpoly
  rw [hch]
  simp only [map_mul]
  change (1 - V.val * Polynomial.C.mapMatrix P * V⁻¹.val +
    (V.val * T.charmatrix * V⁻¹.val) *
      (V.val * Polynomial.C.mapMatrix P * V⁻¹.val)).det = _
  have hmatrix : 1 - V.val * Polynomial.C.mapMatrix P * V⁻¹.val +
      (V.val * T.charmatrix * V⁻¹.val) *
        (V.val * Polynomial.C.mapMatrix P * V⁻¹.val) =
      V.val * (1 - Polynomial.C.mapMatrix P +
        T.charmatrix * Polynomial.C.mapMatrix P) * V⁻¹.val := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one,
      Matrix.mul_assoc, ← Matrix.mul_assoc V⁻¹.val V.val, hV', one_mul]
    rw [hV]
  rw [hmatrix, Matrix.det_units_conj]

private theorem idempotentCharpoly_blocks {R : Type*} [CommRing R]
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (T : Matrix n n R) (S : Matrix m m R) :
    Matrix.idempotentCharpoly (Matrix.fromBlocks T 0 0 S)
      (Matrix.fromBlocks 1 0 0 0) = T.charpoly ∧
    Matrix.idempotentCharpoly (Matrix.fromBlocks T 0 0 S)
      (1 - Matrix.fromBlocks 1 0 0 0) = S.charpoly := by
  have hP : Polynomial.C.mapMatrix (Matrix.fromBlocks 1 0 0 0 :
      Matrix (n ⊕ m) (n ⊕ m) R) = Matrix.fromBlocks 1 0 0 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have hone : (1 : Matrix (n ⊕ m) (n ⊕ m) R[X]) = Matrix.fromBlocks 1 0 0 1 := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have hQ : (1 : Matrix (n ⊕ m) (n ⊕ m) R[X]) -
      Matrix.fromBlocks 1 0 0 0 = Matrix.fromBlocks 0 0 0 1 := by
    rw [hone]
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  have hleft : (1 : Matrix (n ⊕ m) (n ⊕ m) R[X]) -
      Matrix.fromBlocks 1 0 0 0 +
        Matrix.fromBlocks T.charmatrix 0 0 S.charmatrix *
          Matrix.fromBlocks 1 0 0 0 = Matrix.fromBlocks T.charmatrix 0 0 1 := by
    rw [hQ, Matrix.fromBlocks_multiply]
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  have hright : (1 : Matrix (n ⊕ m) (n ⊕ m) R[X]) -
      (1 - Matrix.fromBlocks 1 0 0 0) +
        Matrix.fromBlocks T.charmatrix 0 0 S.charmatrix *
          (1 - Matrix.fromBlocks 1 0 0 0) = Matrix.fromBlocks 1 0 0 S.charmatrix := by
    rw [hQ, Matrix.fromBlocks_multiply, hone]
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  constructor
  · unfold Matrix.idempotentCharpoly
    rw [hP, Matrix.charmatrix_fromBlocks]
    simp only [Matrix.map_zero _ C_0, neg_zero]
    rw [hleft, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    rfl
  · unfold Matrix.idempotentCharpoly
    rw [map_sub, map_one, hP, Matrix.charmatrix_fromBlocks]
    simp only [Matrix.map_zero _ C_0, neg_zero]
    rw [hright, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    rfl

private theorem root_charpoly {R : Type*} [CommRing R] [Nontrivial R]
    (f : R[X]) (hf : f.Monic) :
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis (AdjoinRoot.root f)).charpoly =
      f := by
  have hmin : f = minpoly R (AdjoinRoot.root f) := by
    apply minpoly.unique' R (AdjoinRoot.root f) hf
    · rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    · intro q hq
      by_cases hzero : q = 0
      · exact Or.inl hzero
      · right
        intro hroot
        have hdeg := (AdjoinRoot.powerBasis' hf).dim_le_degree_of_root hzero hroot
        exact (not_le_of_gt hq) ((degree_eq_natDegree hf.ne_zero).symm ▸ hdeg)
  exact (charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hf)).trans hmin.symm

/-- The determinant polynomials reduce to the two prescribed CRT factors.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1).
(blueprint: lem-weil-pbc-adjoinRoot-idempotent-charpoly-map)

Proof: the power basis of the monic quotient is compatible with scalar extension
A→A/I, giving the quotient by the mapped polynomial. By the coprime factorization,
Chinese remainders identify it with the product of the quotients by g₀ and h₀.
Multiplication by the class of X becomes multiplication by X on both factors, and
the two residue hypotheses make multiplication by e the projection (1,0).
Multiplication by 1-e is its complementary projection. In the concatenation of the
power bases of the two quotients, `1-P+(X-T)P` is block diagonal with the
characteristic matrix for multiplication by X on the first factor and the identity
on the second. Its determinant is g₀, since the characteristic polynomial of
multiplication by X on a monic quotient is its defining polynomial. The complementary
projection gives h₀ in the same way. Determinants commute with coefficient reduction
and are invariant under change of basis, so these equalities hold for the original
power-basis matrices. For the zero quotient ring every polynomial equality holds;
for degree-zero factors the corresponding block is empty and its determinant is one.
No Jacobson hypothesis or idempotence before reduction is needed for this calculation. -/
theorem adjoinRoot_idempotentCharpoly_map
    {A : Type u} [CommRing A] (I : Ideal A)
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (e : AdjoinRoot f)
    (he₁ : AdjoinRoot.map (Ideal.Quotient.mk I) f g₀
      (hfactor.symm ▸ dvd_mul_right g₀ h₀) e = 1)
    (he₀ : AdjoinRoot.map (Ideal.Quotient.mk I) f h₀
      (hfactor.symm ▸ dvd_mul_left h₀ g₀) e = 0) :
    let b := (AdjoinRoot.powerBasis' hf).basis;
    let T := Algebra.leftMulMatrix b (AdjoinRoot.root f);
    let P := Algebra.leftMulMatrix b e;
    (Matrix.idempotentCharpoly T P).map (Ideal.Quotient.mk I) = g₀ ∧
      (Matrix.idempotentCharpoly T (1 - P)).map (Ideal.Quotient.mk I) = h₀ := by
  classical
  nontriviality A ⧸ I
  dsimp
  let Tg := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg₀).basis (AdjoinRoot.root g₀)
  let Th := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hh₀).basis (AdjoinRoot.root h₀)
  obtain ⟨d, U, hT, hP⟩ := adjoinRoot_crt_matrix I f hf g₀ h₀ hg₀ hh₀ hcoprime
    hfactor e he₁ he₀
  let b := (AdjoinRoot.powerBasis' hf).basis
  let T : Matrix (Fin f.natDegree) (Fin f.natDegree) A :=
    Algebra.leftMulMatrix b (AdjoinRoot.root f)
  let P : Matrix (Fin f.natDegree) (Fin f.natDegree) A := Algebra.leftMulMatrix b e
  let φ := Ideal.Quotient.mk I
  let T' := Matrix.reindex d d (T.map φ)
  let P' := Matrix.reindex d d (P.map φ)
  have hQ : U.val * (1 - P') * U⁻¹.val = 1 - Matrix.fromBlocks 1 0 0 0 := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv, hP]
  have hg := (idempotentCharpoly_blocks Tg Th).1
  have hh := (idempotentCharpoly_blocks Tg Th).2
  rw [root_charpoly g₀ hg₀] at hg
  rw [root_charpoly h₀ hh₀] at hh
  constructor
  · calc
      (Matrix.idempotentCharpoly T P).map φ =
          Matrix.idempotentCharpoly (T.map φ) (P.map φ) := idempotentCharpoly_map φ T P
      _ = Matrix.idempotentCharpoly T' P' := (idempotentCharpoly_reindex d _ _).symm
      _ = Matrix.idempotentCharpoly (U.val * T' * U⁻¹.val)
          (U.val * P' * U⁻¹.val) := (idempotentCharpoly_conj U T' P').symm
      _ = g₀ := by rw [hT, hP]; exact hg
  · calc
      (Matrix.idempotentCharpoly T (1 - P)).map φ =
          Matrix.idempotentCharpoly (T.map φ) ((1 - P).map φ) :=
        idempotentCharpoly_map φ T (1 - P)
      _ = Matrix.idempotentCharpoly T' (1 - P') := by
        have hmap : (1 - P).map φ = 1 - P.map φ := by
          change φ.mapMatrix (1 - P) = 1 - φ.mapMatrix P
          rw [map_sub, map_one]
        rw [hmap]
        have hr : Matrix.reindex d d ((1 : Matrix (Fin f.natDegree)
            (Fin f.natDegree) (A ⧸ I)) - P.map φ) = 1 - P' := by
          change (Matrix.reindexAlgEquiv (A ⧸ I) (A ⧸ I) d)
            (1 - (P.map φ : Matrix (Fin f.natDegree) (Fin f.natDegree) (A ⧸ I))) = _
          rw [map_sub, map_one]
          rfl
        rw [← hr]
        exact (idempotentCharpoly_reindex d (T.map φ)
          ((1 : Matrix (Fin f.natDegree) (Fin f.natDegree) (A ⧸ I)) - P.map φ)).symm
      _ = Matrix.idempotentCharpoly (U.val * T' * U⁻¹.val)
          (U.val * (1 - P') * U⁻¹.val) := (idempotentCharpoly_conj U T' (1 - P')).symm
      _ = h₀ := by rw [hT, hQ]; exact hh

end Polynomial
