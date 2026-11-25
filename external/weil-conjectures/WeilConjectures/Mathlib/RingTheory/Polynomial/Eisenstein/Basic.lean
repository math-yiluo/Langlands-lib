/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# An Eisenstein polynomial over a discrete valuation ring

Let `E` be a discrete valuation ring with uniformiser `ϖ` and fraction field `K`, and let `c` be a
unit of `E`. For `n ≥ 2` the polynomial `Xⁿ + ϖc Xⁿ⁻¹ - ϖc` is Eisenstein at the maximal ideal,
hence irreducible over `K`
(`Polynomial.irreducible_map_X_pow_add_C_mul_X_pow_sub_C`). Its roots are the
inverses of the roots of the Artin–Schreier polynomial `Xⁿ - X - (ϖc)⁻¹`, which is how it is
used: an Artin–Schreier equation with a pole of order one has no solution over `K`.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace Polynomial

variable {E : Type*} [CommRing E] [IsDomain E] [IsDiscreteValuationRing E]

/-- For a uniformiser `ϖ` and a unit `c` of a discrete valuation ring `E` and `n ≥ 2`, the
polynomial `Xⁿ + ϖc Xⁿ⁻¹ - ϖc` is Eisenstein at the maximal ideal. -/
lemma isEisensteinAt_X_pow_add_C_mul_X_pow_sub_C {ϖ : E} (hϖ : Irreducible ϖ) (c : Eˣ) {n : ℕ}
    (hn : 2 ≤ n) :
    (X ^ n + (C (ϖ * c) * X ^ (n - 1) - C (ϖ * c))).IsEisensteinAt (maximalIdeal E) := by
  have hlt : (C (ϖ * c) * X ^ (n - 1) - C (ϖ * c) : E[X]).degree < (X ^ n : E[X]).degree := by
    rw [degree_X_pow]
    refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast Nat.sub_one_lt (by omega))
    · exact (degree_C_le).trans_lt (by exact_mod_cast (by omega : 0 < n))
  have hmon : (X ^ n + (C (ϖ * c) * X ^ (n - 1) - C (ϖ * c)) : E[X]).Monic :=
    (monic_X_pow n).add_of_left hlt
  have hdeg : (X ^ n + (C (ϖ * c) * X ^ (n - 1) - C (ϖ * c)) : E[X]).natDegree = n := by
    rw [natDegree_add_eq_left_of_degree_lt hlt, natDegree_X_pow]
  have hm : maximalIdeal E = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hϖm : ϖ * c ∈ maximalIdeal E :=
    hm ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  refine ⟨?_, fun {i} hi ↦ ?_, ?_⟩
  · rw [hmon.leadingCoeff]
    exact fun h ↦ (maximalIdeal.isMaximal E).ne_top ((Ideal.eq_top_iff_one _).2 h)
  · rw [hdeg] at hi
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul_X_pow, coeff_C, ite_eq_right hi.ne]
    refine Ideal.add_mem _ (Ideal.zero_mem _) (Ideal.sub_mem _ ?_ ?_) <;>
      split_ifs <;> first | exact hϖm | exact Ideal.zero_mem _
  · have h0 : (0 : ℕ) ≠ n - 1 := by omega
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul_X_pow, coeff_C, ite_eq_right h0,
      ite_eq_right (by omega : (0 : ℕ) ≠ n), ite_true, zero_add, zero_sub]
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    rintro ⟨z, hz⟩
    have : ϖ * (-(z * ϖ)) = ϖ * c := by linear_combination -hz
    have hc := mul_left_cancel₀ hϖ.ne_zero this
    refine (mem_maximalIdeal _).1 ?_ c.isUnit
    rw [← hc, hm]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self ϖ))

variable (K : Type*) [Field K] [Algebra E K] [IsFractionRing E K]

/-- **An Eisenstein polynomial over a discrete valuation ring.** For a uniformiser `ϖ` and a unit
`c` of a discrete valuation ring `E` and `n ≥ 2`, the polynomial `Xⁿ + ϖc Xⁿ⁻¹ - ϖc` is
irreducible over the fraction field of `E`. -/
theorem irreducible_map_X_pow_add_C_mul_X_pow_sub_C {ϖ : E} (hϖ : Irreducible ϖ) (c : Eˣ)
    {n : ℕ} (hn : 2 ≤ n) :
    Irreducible ((X ^ n + (C (ϖ * c) * X ^ (n - 1) - C (ϖ * c))).map (algebraMap E K)) := by
  have hlt : (C (ϖ * c) * X ^ (n - 1) - C (ϖ * c) : E[X]).degree < (X ^ n : E[X]).degree := by
    rw [degree_X_pow]
    refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast Nat.sub_one_lt (by omega))
    · exact (degree_C_le).trans_lt (by exact_mod_cast (by omega : 0 < n))
  have hmon : (X ^ n + (C (ϖ * c) * X ^ (n - 1) - C (ϖ * c)) : E[X]).Monic :=
    (monic_X_pow n).add_of_left hlt
  refine (hmon.irreducible_iff_irreducible_map_fraction_map).1 ?_
  refine (isEisensteinAt_X_pow_add_C_mul_X_pow_sub_C hϖ c hn).irreducible
    (maximalIdeal.isMaximal E).isPrime hmon.isPrimitive ?_
  rw [natDegree_add_eq_left_of_degree_lt hlt, natDegree_X_pow]
  omega


end Polynomial
