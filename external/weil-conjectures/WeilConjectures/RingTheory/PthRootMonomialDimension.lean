/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The reduced-monomial dimension bound for a root quotient

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4), first paragraph;
monic polynomial division.
-/

@[expose] public section

universe u

namespace Algebra

/-- The quotient adjoining roots is finite-dimensional, with dimension at most the
number of reduced monomials. No characteristic or independence hypothesis is required.

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4), first paragraph;
Algebra, monic division as in Tag 00G3.
(blueprint: lem-weil-pbc-pth-root-monomial-dimension).

Proof: Let q be the quotient map. Its relations give q(X_i)^p = q(C(a_i)). For a
monomial X^e, write each exponent e_i = p*d_i+r_i with 0 <= r_i < p. In the quotient
its image is the coefficient product of a_i^d_i times the image of X^r. Thus every
polynomial class is in the k-span of the images of the monomials indexed by
Fin n -> Fin p. There are p^n such monomials. The resulting surjective linear map
from the p^n-dimensional coordinate space to the quotient proves finiteness and
the dimension bound. The division algorithm uses p > 0, and works for arbitrary
coefficients, including zero. For n = 0 it says constants span the quotient. -/
theorem pthRootAlgebra_finite_finrank_le
    (k : Type u) [Field k] (p n : ℕ) (hp : 0 < p) (a : Fin n → k) :
    Module.Finite k (pthRootAlgebra p n k a) ∧
      Module.finrank k (pthRootAlgebra p n k a) ≤ p ^ n  := by
  classical
  let Q := pthRootAlgebra p n k a
  let I : Ideal (MvPolynomial (Fin n) k) := Ideal.span (Set.range (fun i : Fin n ↦
    (MvPolynomial.X i : MvPolynomial (Fin n) k) ^ p - MvPolynomial.C (a i)))
  let q : MvPolynomial (Fin n) k →+* Q := Ideal.Quotient.mk I
  let m : (Fin n → Fin p) → Q := fun r ↦ ∏ i, q (MvPolynomial.X i) ^ (r i).val
  let S : Submodule k Q := Submodule.span k (Set.range m)
  have hX (i : Fin n) : q (MvPolynomial.X i) ^ p = algebraMap k Q (a i) := by
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr
      (Ideal.subset_span ⟨i, rfl⟩ : MvPolynomial.X i ^ p - MvPolynomial.C (a i) ∈ I)
    change q (MvPolynomial.X i ^ p - MvPolynomial.C (a i)) = 0 at hz
    rw [map_sub, map_pow, sub_eq_zero] at hz
    exact hz
  have hm (e : Fin n →₀ ℕ) (c : k) : q (MvPolynomial.monomial e c) ∈ S := by
    let r : Fin n → Fin p := fun i ↦ ⟨e i % p, Nat.mod_lt _ hp⟩
    have heq : q (MvPolynomial.monomial e c) =
        (c * ∏ i, a i ^ (e i / p)) • m r := by
      rw [MvPolynomial.monomial_eq, map_mul]
      change algebraMap k Q c * q (∏ i ∈ e.support, MvPolynomial.X i ^ e i) = _
      rw [map_prod]
      have hall : (∏ i ∈ e.support, q (MvPolynomial.X i ^ e i)) =
          ∏ i : Fin n, q (MvPolynomial.X i ^ e i) := by
        apply Finset.prod_subset (Finset.subset_univ _)
        intro i _ hi
        simp [Finsupp.notMem_support_iff.mp hi]
      rw [hall]
      simp only [map_pow]
      have hred (i : Fin n) : q (MvPolynomial.X i) ^ e i =
          algebraMap k Q (a i ^ (e i / p)) * q (MvPolynomial.X i) ^ (e i % p) := by
        conv_lhs => rw [← Nat.div_add_mod (e i) p]
        rw [pow_add, pow_mul, hX, ← map_pow]
      simp_rw [hred]
      rw [Finset.prod_mul_distrib, ← map_prod]
      simp only [Algebra.smul_def, map_mul, m, r, mul_assoc]
    rw [heq]
    exact S.smul_mem _ (Submodule.subset_span ⟨r, rfl⟩)
  have hS : S = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    change q f ∈ S
    rw [f.as_sum, map_sum]
    exact Submodule.sum_mem _ (fun e _ ↦ hm e (f.coeff e))
  have hsurj : Function.Surjective (Fintype.linearCombination k m) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination k m).mp hS
  have hfin : Module.Finite k Q :=
    Module.Finite.of_surjective (Fintype.linearCombination k m) hsurj
  let := hfin
  refine ⟨hfin, ?_⟩
  have hle := LinearMap.finrank_le_finrank_of_surjective
    (f := Fintype.linearCombination k m) hsurj
  simpa using hle

end Algebra
