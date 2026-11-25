/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.RingTheory.AdjoinRootCRTRootBlockAux

/-! # Simultaneous CRT coordinates for multiplication matrices

Source: Stacks Project, Tag 09XI, proof of (3) implies (1).
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix)
-/

@[expose] public section

universe u

namespace Polynomial

/-- Root multiplication has CRT block coordinates after coefficient reduction.
Source: Stacks Project, Tag 09XI, proof of (3) implies (1), the decomposition of B/IB.
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix-root-block)

Proof: write R = A/I and fbar = f.map (Ideal.Quotient.mk I). The leading coefficient
of a monic polynomial is one, so fbar has degree deg f over the nonzero ring R.
The power-basis multiplication matrix of the root reduces to that of the root in
AdjoinRoot fbar: divide each product of powers by f using monic division, reduce
its coefficients, and use uniqueness of the remainder modulo fbar. Since g and h
are coprime, their principal ideals are comaximal and their product, equal to
(g*h), is their intersection. The Chinese remainder algebra equivalence therefore
identifies AdjoinRoot fbar with AdjoinRoot g times AdjoinRoot h and takes the root
to the pair of roots. Concatenate the power bases of these two factors.
Monicity gives deg f = deg g + deg h, so choose the index equivalence d.
The matrix U of the CRT coordinate equivalence from the reindexed reduced power
basis to this concatenated basis is invertible, with inverse the matrix of the
inverse coordinate equivalence. Intertwining multiplication by the root, and
using the matrix-of-composition identity, yields the asserted conjugation.
If a factor is one, its quotient is zero and its power basis is empty; the same
argument applies. If f is one, both factors have degree zero and all matrices are
empty. No nontriviality of either factor quotient is required. -/
theorem adjoinRoot_crt_matrix_root_block
    {A : Type u} [CommRing A] (I : Ideal A) [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic) (g h : (A ⧸ I)[X])
    (hg : g.Monic) (hh : h.Monic) (hcoprime : IsCoprime g h)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h) :
    let b := (AdjoinRoot.powerBasis' hf).basis
    let T := Algebra.leftMulMatrix b (AdjoinRoot.root f)
    let Tg := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis (AdjoinRoot.root g)
    let Th := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hh).basis (AdjoinRoot.root h)
    ∃ (d : Fin f.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree))
      (U : (Matrix (Fin g.natDegree ⊕ Fin h.natDegree)
        (Fin g.natDegree ⊕ Fin h.natDegree) (A ⧸ I))ˣ),
      U.val * Matrix.reindex d d (T.map (Ideal.Quotient.mk I)) * U⁻¹.val =
        Matrix.fromBlocks Tg 0 0 Th := by
  obtain ⟨d⟩ := adjoinRoot_crt_degree_equiv I f hf g h hg hh hfactor
  obtain ⟨U, hU⟩ := adjoinRoot_crt_matrix_for_degree_equiv I f hf g h hg hh hcoprime hfactor d
  exact ⟨d, U, hU⟩

end Polynomial
