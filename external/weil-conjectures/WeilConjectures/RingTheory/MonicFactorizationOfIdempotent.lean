/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Group.Idempotent
import WeilConjectures.LinearAlgebra.IdempotentCharpolyMonic
import WeilConjectures.LinearAlgebra.IdempotentCharpolyMulComplement
import WeilConjectures.RingTheory.AdjoinRootIdempotentCharpolyMap
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Tactic.NoncommRing

/-!
# Monic factorization from a lifted idempotent

Source: Stacks Project, Tag 09XI, proof of (3) implies (1)
(blueprint: lem-weil-pbc-idempotent-splitting-monic-factorization).
-/

@[expose] public section

universe u

namespace Polynomial

/-- Stacks Project, Tag 09XI, proof of (3) implies (1): an idempotent of `A[X]/(f)`
lifting the Chinese remainder element `(1, 0)` yields a monic factorization lifting `g₀ * h₀`.
The two `AdjoinRoot.map` conditions are precisely its residues in the Chinese remainder
factors, so they express that its reduction is the specified idempotent of `B/IB`.
(blueprint: lem-weil-pbc-idempotent-splitting-monic-factorization)

Proof:
1. Use the power basis of `AdjoinRoot f`. Let T be the matrix of multiplication by X
   and P the matrix of multiplication by e. Idempotence of e gives P²=P, and P commutes
   with T; the same holds for the complementary projection 1-P.
2. Define g and h by the explicit determinants `Matrix.idempotentCharpoly T P` and
   `Matrix.idempotentCharpoly T (1-P)`. The Chinese remainder calculation in
   `adjoinRoot_idempotentCharpoly_map` identifies their reductions with g₀ and h₀.
3. Apply `Matrix.idempotentCharpoly_monic_of_map_monic` to both projections. This is
   the constant-rank argument over a Jacobson ideal, and proves g and h monic.
4. `Matrix.idempotentCharpoly_mul_complement` gives g*h=T.charpoly. The characteristic
   polynomial of multiplication by the power-basis generator is its minimal polynomial;
   `minpoly.unique'` and the power-basis degree bound identify this with f. In the zero
   ring the equality holds directly.
5. Assemble the monicity, product equality, and reduction equalities. -/
theorem exists_monic_factorization_of_idempotent
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (e : AdjoinRoot f) (he : IsIdempotentElem e)
    (he₁ : AdjoinRoot.map (Ideal.Quotient.mk I) f g₀
      (hfactor.symm ▸ dvd_mul_right g₀ h₀) e = 1)
    (he₀ : AdjoinRoot.map (Ideal.Quotient.mk I) f h₀
      (hfactor.symm ▸ dvd_mul_left h₀ g₀) e = 0) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ := by
  classical
  let b := (AdjoinRoot.powerBasis' hf).basis
  let T := Algebra.leftMulMatrix b (AdjoinRoot.root f)
  let P := Algebra.leftMulMatrix b e
  have hP : P * P = P := by
    dsimp [P]
    rw [← map_mul, he.eq]
  have hTP : T * P = P * T := by
    dsimp [T, P]
    rw [← map_mul, ← map_mul, mul_comm]
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hP]
  have hTQ : T * (1 - P) = (1 - P) * T := by
    noncomm_ring [hTP]
  obtain ⟨hgmap, hhmap⟩ := adjoinRoot_idempotentCharpoly_map
    I f hf g₀ h₀ hg₀ hh₀ hcoprime hfactor e he₁ he₀
  have hg : (Matrix.idempotentCharpoly T P).Monic :=
    Matrix.idempotentCharpoly_monic_of_map_monic I hI T P hP hTP (hgmap ▸ hg₀)
  have hh : (Matrix.idempotentCharpoly T (1 - P)).Monic :=
    Matrix.idempotentCharpoly_monic_of_map_monic I hI T (1 - P) hQ hTQ (hhmap ▸ hh₀)
  have hchar : T.charpoly = f := by
    nontriviality A
    have hmin : f = minpoly A (AdjoinRoot.root f) := by
      apply minpoly.unique' A (AdjoinRoot.root f) hf
      · rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      · intro q hq
        by_cases hzero : q = 0
        · exact Or.inl hzero
        · right
          intro hroot
          have hdeg := (AdjoinRoot.powerBasis' hf).dim_le_degree_of_root hzero hroot
          exact (not_le_of_gt hq) ((degree_eq_natDegree hf.ne_zero).symm ▸ hdeg)
    exact (charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hf)).trans hmin.symm
  refine ⟨Matrix.idempotentCharpoly T P, Matrix.idempotentCharpoly T (1 - P),
    hg, hh, ?_, hgmap, hhmap⟩
  exact hchar.symm.trans (Matrix.idempotentCharpoly_mul_complement T P hP hTP).symm

end Polynomial
