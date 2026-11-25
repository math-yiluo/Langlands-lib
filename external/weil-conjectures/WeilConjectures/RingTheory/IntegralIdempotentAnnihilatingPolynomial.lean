/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Group.Idempotent

/-!
# An annihilating polynomial for an integral lift of an idempotent

Source: Stacks Project, More on Algebra, Lemma Tag 09XG (lemma-helper-integral)
(blueprint: lem-weil-pbc-integral-idempotent-annihilating-polynomial).
-/

@[expose] public section

universe u v

namespace Polynomial

/-- An element of an integral algebra that is idempotent modulo the extended ideal has
an annihilating monic polynomial reducing to `X ^ d * (X - 1) ^ d` for some `d ≥ 1`.
Source: Stacks Project, More on Algebra, Lemma Tag 09XG (lemma-helper-integral).
(blueprint: lem-weil-pbc-integral-idempotent-annihilating-polynomial)

Proof: First put `z = b² - b`. Idempotence in the quotient says that `z` belongs to `IB`.
Apply `lem-weil-pbc-integral-extended-ideal-element-monic` (Stacks Tag 00H5, Mathlib's
`Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map`) to obtain a monic `g`
annihilating `z`, with all non-leading coefficients in `I`. Replace `g` uniformly
by `h = X * g`, with positive degree `d = g.natDegree + 1`. Put
`f = h.comp (X * (X - 1))`. Composition of monic polynomials makes `f` monic,
and evaluation gives `f(b) = h(z) = 0`. Reducing coefficients modulo `I`
sends `g` to `X ^ g.natDegree` and `h` to `X ^ d`; it commutes with composition,
giving `(X * (X - 1))^d = X^d * (X - 1)^d`. If `A` is the zero ring, its algebra
`B` is also the zero ring, and `d = 1`, `f = 1` satisfy all requirements. -/
theorem exists_monic_aeval_eq_zero_map_eq_of_isIdempotentElem_quotient
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (I : Ideal A) (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A B)) b)) :
    ∃ (d : ℕ) (f : A[X]), 1 ≤ d ∧ f.Monic ∧ aeval b f = 0 ∧
      f.map (Ideal.Quotient.mk I) = (X : (A ⧸ I)[X]) ^ d * (X - 1) ^ d := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    have hB : Subsingleton B := subsingleton_of_zero_eq_one
      (by simpa using congrArg (algebraMap A B) (Subsingleton.elim (0 : A) 1))
    exact ⟨1, 1, le_rfl, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | inr hA =>
    have hz : b ^ 2 - b ∈ I.map (algebraMap A B) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_pow, pow_two, hb.eq]
      simp
    obtain ⟨g, hg, hgz, hcoeff⟩ :=
      exists_monic_aeval_eq_zero_forall_mem_of_mem_map hz
    have hgmap : g.map (Ideal.Quotient.mk I) = X ^ g.natDegree := by
      ext i
      by_cases hi : i = g.natDegree
      · subst i
        simp [coeff_map, hg.coeff_natDegree]
      · simp only [coeff_map, coeff_X_pow, ite_eq_right hi]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcoeff i hi)
    have hq : (X * (X - 1) : A[X]).Monic :=
      monic_X.mul (by simpa using monic_X_sub_C (1 : A))
    have hqdeg : (X * (X - 1) : A[X]).natDegree ≠ 0 := by
      rw [monic_X.natDegree_mul (by simpa using monic_X_sub_C (1 : A))]
      simp only [natDegree_X]
      omega
    refine ⟨g.natDegree + 1, (X * g).comp (X * (X - 1)), by omega,
      (monic_X.mul hg).comp hq hqdeg, ?_, ?_⟩
    · have hqb : aeval b (X * (X - 1) : A[X]) = b ^ 2 - b := by
        simp only [aeval_mul, aeval_X, map_sub, map_one]
        ring
      rw [aeval_comp, hqb, aeval_mul, aeval_X, hgz, mul_zero]
    · simp only [map_comp, Polynomial.map_mul, map_X, Polynomial.map_sub,
        Polynomial.map_one, hgmap, mul_comm X (X ^ g.natDegree), ← pow_succ,
        X_pow_comp, mul_pow]

end Polynomial
