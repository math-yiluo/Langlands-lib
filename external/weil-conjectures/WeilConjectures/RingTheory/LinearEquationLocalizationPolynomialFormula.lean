/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
@[expose] public section
universe u
namespace MvPolynomial
/-- Formula for the eliminated variable in the localization equivalence.

The source is Stacks Project, Tag 07EU, `lemma-final-solve`, whose omitted
calculation gives this identity. Apply the inverse to the relation
`∑ j, fⱼ xⱼ = 1` in the quotient. The assumed inverse formulas replace each
free `xⱼ` by `X j`; isolating the `i` term gives
`fᵢ xᵢ = 1 - ∑ j ≠ i, fⱼ X j`. Multiplication by the inverse of `fᵢ` in
`Af` yields exactly the displayed expression. Algebra equivalence operations
preserve these coefficients and sums, so the computation holds in `Bf`.
(blueprint: theorem-finite-etale-covers-proper-henselian--2) -/
theorem linearEquationLocalizationPolynomialFormula (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) (i : Fin r) :
    let I : Ideal (MvPolynomial (Fin r) A) :=
      Ideal.span {(∑ j : Fin r, C (f j) * X j) - 1}
    let B := MvPolynomial (Fin r) A ⧸ I
    let q := Ideal.Quotient.mk I
    let Af := Localization.Away (f i)
    let Bf := Localization.Away (algebraMap A B (f i))
    let : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra
    let x : Fin r → Bf := fun j ↦ algebraMap B Bf (q (X j))
    ∀ e : MvPolynomial {j : Fin r // j ≠ i} Af ≃ₐ[Af] Bf,
      e.toAlgHom = aeval (fun j ↦ x j.1) →
      (∀ j : {j : Fin r // j ≠ i}, e.symm (x j.1) = X j) →
      e.symm (x i) = C (IsLocalization.Away.invSelf (S := Af) (f i)) *
          (1 - ∑ j : {j : Fin r // j ≠ i},
            C (algebraMap A Af (f j.1)) * X j) := by
  classical
  dsimp only
  intro e he hf
  let I : Ideal (MvPolynomial (Fin r) A) :=
    Ideal.span {(∑ j : Fin r, C (f j) * X j) - 1}
  let B := MvPolynomial (Fin r) A ⧸ I
  let Af := Localization.Away (f i)
  let Bf := Localization.Away (algebraMap A B (f i))
  let q := Ideal.Quotient.mk I
  let : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra
  let x : Fin r → Bf := fun j ↦ algebraMap B Bf (q (X j))
  have hcoeff (a : A) : algebraMap Af Bf (algebraMap A Af a) =
      algebraMap B Bf (q (C a)) := by
    change Localization.awayMap (algebraMap A B) (f i) (algebraMap A Af a) = _
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have hrel : (∑ j : Fin r, algebraMap Af Bf (algebraMap A Af (f j)) * x j) = 1 := by
    have hq : q ((∑ j : Fin r, C (f j) * X j) - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have h := congrArg (algebraMap B Bf) hq
    simpa only [map_sub, map_sum, map_mul, map_one, map_zero, ← hcoeff,
      sub_eq_zero, x] using h
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne
    (fun j ↦ algebraMap Af Bf (algebraMap A Af (f j)) * x j) i
  rw [hsplit] at hrel
  have hback := congrArg e.symm hrel
  have hc (a : Af) : e.symm (algebraMap Af Bf a) = C a :=
    e.symm.commutes a
  simp only [map_add, map_mul, map_sum, map_one, hc] at hback
  have hf' (j : {j : Fin r // j ≠ i}) : e.symm (x j.1) = X j := hf j
  simp_rw [hf'] at hback
  have hinv : C (IsLocalization.Away.invSelf (S := Af) (f i)) *
      C (algebraMap A Af (f i)) = (1 : MvPolynomial {j : Fin r // j ≠ i} Af) := by
    rw [← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  have hiso : C (algebraMap A Af (f i)) * e.symm (x i) =
      1 - ∑ j : {j : Fin r // j ≠ i}, C (algebraMap A Af (f j.1)) * X j :=
    eq_sub_of_add_eq hback
  rw [← hiso, ← mul_assoc, hinv, one_mul]
end MvPolynomial
