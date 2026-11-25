/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.RingTheory.Coprime.Basic

import WeilConjectures.RingTheory.AdjoinRootCRTRootBlock
import WeilConjectures.RingTheory.AdjoinRootCRTLiftBlock

/-! # Simultaneous CRT coordinates for multiplication matrices

Source: Stacks Project, Tag 09XI, proof of (3) implies (1).
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix)
-/

@[expose] public section

universe u

namespace Polynomial

/-- Coefficient reduction and Chinese remainders simultaneously put multiplication
by the root and by a CRT lift in block coordinates.
Source: Stacks Project, Tag 09XI, proof of (3) implies (1), the decomposition of B/IB.
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix)

Proof: a monic quotient has the power basis, and coefficient reduction preserves
its degree over the nonzero residue ring. Reducing the coefficients of representatives
of degree less than deg f identifies its coordinate module with the power-basis
coordinate module of AdjoinRoot of the reduced polynomial. The CRT map to
AdjoinRoot g times AdjoinRoot h is an algebra equivalence: coprimality makes the
principal ideals comaximal, and their intersection is the ideal of g*h. Concatenate
the power bases of the two factors. Their dimensions add to deg f, so choose an
index equivalence d. The matrix of the resulting coordinate equivalence is a unit U.
The algebra equivalence takes the root to the pair of roots and e to (1,0), by
its two prescribed residues. Intertwining multiplication by these elements gives
the two conjugation identities. If either factor has degree zero, its quotient is
zero and its basis is empty; the same construction applies. No idempotence of e
in AdjoinRoot f is required, since only its residue is used. -/
theorem adjoinRoot_crt_matrix
    {A : Type u} [CommRing A] (I : Ideal A) [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic) (g h : (A ⧸ I)[X])
    (hg : g.Monic) (hh : h.Monic) (hcoprime : IsCoprime g h)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h)
    (e : AdjoinRoot f)
    (he₁ : AdjoinRoot.map (Ideal.Quotient.mk I) f g
      (hfactor.symm ▸ dvd_mul_right g h) e = 1)
    (he₀ : AdjoinRoot.map (Ideal.Quotient.mk I) f h
      (hfactor.symm ▸ dvd_mul_left h g) e = 0) :
    let b := (AdjoinRoot.powerBasis' hf).basis;
    let T := Algebra.leftMulMatrix b (AdjoinRoot.root f);
    let P := Algebra.leftMulMatrix b e;
    let Tg := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis (AdjoinRoot.root g);
    let Th := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hh).basis (AdjoinRoot.root h);
    ∃ (d : Fin f.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree))
      (U : (Matrix (Fin g.natDegree ⊕ Fin h.natDegree)
        (Fin g.natDegree ⊕ Fin h.natDegree) (A ⧸ I))ˣ),
      U.val * Matrix.reindex d d (T.map (Ideal.Quotient.mk I)) * U⁻¹.val =
        Matrix.fromBlocks Tg 0 0 Th ∧
      U.val * Matrix.reindex d d (P.map (Ideal.Quotient.mk I)) * U⁻¹.val =
        Matrix.fromBlocks 1 0 0 0 := by
  classical
  dsimp
  obtain ⟨d, U, hT⟩ := adjoinRoot_crt_matrix_root_block I f hf g h hg hh hcoprime hfactor
  refine ⟨d, U, hT, ?_⟩
  exact adjoinRoot_crt_matrix_lift_block I f hf g h hg hh hfactor e he₁ he₀ d U hT

end Polynomial
