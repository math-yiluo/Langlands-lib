/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import WeilConjectures.RingTheory.FiniteGabberPolynomialRelation

/-!
# Gabber's polynomial for a finite algebra over a Zariski pair

Source: Stacks Project, More on Algebra, Lemma Tag 0EM0 (lemma-helper-finite)
(blueprint: lem-weil-pbc-zariski-pair-finite-gabber-polynomial).
-/

@[expose] public section

universe u v w z

open Polynomial
open scoped BigOperators

namespace Algebra

/-- A lift of `(1,0)` in a finite algebra over a Zariski pair is annihilated by a monic
polynomial of the form `X^d (X-1) + ∑ aⱼ X^j`, with `d ≥ 1` and `aⱼ ∈ I`.
The compatibility condition on `e` says that the quotient decomposition is one of
`A/I`-algebras, rather than merely of rings.
Source: Stacks Project, More on Algebra, Lemma Tag 0EM0 (lemma-helper-finite).
(blueprint: lem-weil-pbc-zariski-pair-finite-gabber-polynomial)

Proof (the ten steps of the DAG node):
1. Finiteness implies integrality (`lem-weil-pbc-finite-algebra-is-integral`). Lift the
idempotent `(1,0)` after an étale extension `A → A'` preserving `A/I`, using
`lem-weil-pbc-lift-idempotent-upstairs` (Tag 07M4).
2. Decompose `B ⊗[A] A'` using this lifted idempotent into finite factors `B'₁ × B'₂`.
The image of `b` is congruent to `1` in the first factor and `0` in the second.
3. The finite cokernel of `A' → B'₁` vanishes modulo `IA'`. Nakayama gives `g ∈ 1+IA'`
annihilating it (`lem-weil-pbc-nakayama-one-plus-ideal-annihilator`, Tag 00DV).
4. Localize at `g`, obtaining `A'' → B''₁` surjective and still `A/I ≅ A''/IA''`.
Flatness follows from `lem-weil-pbc-etale-algebra-flat`,
`lem-weil-pbc-localization-flat` and `lem-weil-pbc-flat-ring-map-comp`.
5. Choose `a' ∈ IA''` mapping to `b''₁-1` by this surjection.
6. By `lem-weil-pbc-finite-algebra-is-integral` and
`lem-weil-pbc-integral-extended-ideal-element-monic` (Tag 00H5), choose a monic
polynomial annihilating `b''₂` and reducing to a power of `X`. Multiply it by `X`
so that its degree `d` is at least one, including when the second factor is zero.
7. Multiply this polynomial by `X-1-a'`. It annihilates `b''` and yields
`(b''-1)b''^d ∈ ∑ⱼ IA'' b''^j`, with `0 ≤ j ≤ d`.
8. Every maximal ideal of `A` contains `I`, and its fibre in `A''` is nonzero since
`A/I ≅ A''/IA''`. Thus `A → A''` is faithfully flat by
`lem-weil-pbc-flat-faithfully-flat-maximal-ideals`.
9. Apply `lem-weil-pbc-faithfully-flat-universally-injective` (Tag 05CK) to
`B / ∑ⱼ I b^j`. The relation of step 7 descends to `(b-1)b^d = ∑ⱼ iⱼ b^j` over `A`.
10. Set `f = X^d(X-1) - ∑ⱼ iⱼ X^j`. It is monic, annihilates `b`, and has the required
coefficients `aⱼ = -iⱼ ∈ I`. -/
theorem exists_monic_aeval_eq_zero_gabber_polynomial
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (B₁ : Type w) (B₂ : Type z) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* (B₁ × B₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)))
    (h₁ : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B) (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (d : ℕ) (a : Fin (d + 1) → A) (f : A[X]),
      1 ≤ d ∧ (∀ j, a j ∈ I) ∧ f.Monic ∧ aeval b f = 0 ∧
        f = X ^ d * (X - 1) + ∑ j : Fin (d + 1), C (a j) * X ^ (j : ℕ) := by
  classical
  obtain ⟨S, f, hS, d, hd, hzero⟩ :=
    exists_gabber_relation_after_base_change I hI B₁ B₂ e he h₁ b hb
  let : Algebra A S := f.toAlgebra
  let : Module.FaithfullyFlat A S := hS
  let L : (Fin (d + 1) → I) →ₗ[A] B :=
    ∑ j : Fin (d + 1), (I.subtype.comp (LinearMap.proj j)).smulRight (b ^ (j : ℕ))
  have hq : (LinearMap.range L).mkQ ((b - 1) * b ^ d) = 0 :=
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := S)
      (B ⧸ LinearMap.range L)) (hzero.trans (map_zero _).symm)
  have hmem : (b - 1) * b ^ d ∈ LinearMap.range L := by
    simpa only [← (LinearMap.range L).ker_mkQ, LinearMap.mem_ker] using hq
  obtain ⟨c, hc⟩ := hmem
  let a : Fin (d + 1) → A := fun j ↦ -(c j : A)
  have ha : ∀ j, a j ∈ I := fun j ↦ I.neg_mem (c j).property
  have hrel : (b - 1) * b ^ d +
      ∑ j : Fin (d + 1), algebraMap A B (a j) * b ^ (j : ℕ) = 0 := by
    have hc' : ∑ j : Fin (d + 1), algebraMap A B (c j : A) * b ^ (j : ℕ) =
        (b - 1) * b ^ d := by
      simpa [L, LinearMap.sum_apply, Algebra.smul_def] using hc
    simp only [a, map_neg, neg_mul, Finset.sum_neg_distrib, hc', add_neg_cancel]
  refine ⟨d, a, X ^ d * (X - 1) + ∑ j : Fin (d + 1), C (a j) * X ^ (j : ℕ),
    hd, ha, ?_, ?_, rfl⟩
  · nontriviality A
    rw [mul_sub, mul_one, ← pow_succ, sub_eq_add_neg, add_assoc]
    apply monic_X_pow_add
    have hsum : (∑ j : Fin (d + 1), C (a j) * X ^ (j : ℕ)).degree ≤ (d : WithBot ℕ) := by
      apply (degree_sum_le _ _).trans
      apply Finset.sup_le
      intro j hj
      exact (degree_C_mul_X_pow_le _ _).trans
        (WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ j.isLt))
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · rw [degree_neg, degree_X_pow]
      exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d)
    · exact lt_of_le_of_lt hsum (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
  · rw [aeval_add, aeval_mul, aeval_X_pow, aeval_sub, aeval_X]
    simp only [map_one, map_pow, map_sum, map_mul, aeval_def]
    simp only [eval₂_C, eval₂_X]
    calc
      b ^ d * (b - 1) + ∑ x, (algebraMap A B) (a x) * b ^ (x : ℕ) =
          (b - 1) * b ^ d + ∑ x, (algebraMap A B) (a x) * b ^ (x : ℕ) := by ring
      _ = 0 := hrel

end Algebra
