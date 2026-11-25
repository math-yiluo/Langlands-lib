/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.BilinearForm
public import WeilConjectures.ZetaFunction.ClassicalFunctionalEquation
public import WeilConjectures.ZetaFunction.BettiSymmetry

/-!
# Duality reciprocity of the integral Frobenius factors

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over
`k₀ = 𝔽_q`, with integral Frobenius factors `P₀, …, P_{2d}`, Betti numbers `bᵢ = deg Pᵢ` and
determinant constants `Dᵢ = (-1)^{bᵢ} [T^{bᵢ}] Pᵢ`. Poincaré duality identifies the Frobenius
eigenvalues in degree `2d - i` with the `qᵈ / α` for the eigenvalues `α` in degree `i`; hence

`P_{2d-i}(q^{-d} T⁻¹) = (-1)^{bᵢ} T^{-bᵢ} Dᵢ⁻¹ Pᵢ(T)`,  `Dᵢ D_{2d-i} = q^{d bᵢ}`,

and `d χ` is even, `χ = ∑ᵢ (-1)ⁱ bᵢ`: for odd `d` the middle pairing is alternating
(blueprint `corollary-functional-equation`, `corollary-functional-equation--4`).

## Main statements

- `AlgebraicGeometry.Scheme.duality_reciprocity`: blueprint `corollary-functional-equation--4`.
- `AlgebraicGeometry.Scheme.reciprocity`: blueprint `corollary-functional-equation`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

namespace Scheme

variable {k₀ : Type u} [Field k₀] [Finite k₀]

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- The determinant constant of a polynomial is its leading coefficient up to the sign
`(-1)^{deg}`. -/
theorem weilDeterminantConstant_eq (P : Polynomial ℤ) :
    weilDeterminantConstant P = (-1) ^ P.natDegree * P.leadingCoeff :=
  rfl

/-- For odd `d`, the middle Betti number `dim H^d(X₀ ⊗ k̄, ℚ̄_ℓ)` is even: by Poincaré duality the
middle cup-product pairing is perfect and `(-1)^d`-symmetric, hence alternating
(`corollary-functional-equation--5`). -/
theorem even_finrank_cohomology_middle (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (hd : Odd d) :
    Even (Module.finrank (PadicAlgCl l)
      ((WeilSheaf.adicConstant k₀ l X).cohomology d).carrier) := by
  obtain ⟨T, -, -, -, hpair, -⟩ := WeilSheaf.poincareDuality k₀ l X d
  have h : (d : ℤ) + d = 2 * d := by ring
  obtain ⟨hperf, hcomm⟩ := hpair d d h
  let B : LinearMap.BilinForm (PadicAlgCl l)
      ((WeilSheaf.adicConstant k₀ l X).cohomology d).carrier :=
    T.pairing d d h
  refine LinearMap.BilinForm.even_finrank_of_isAlt (B := B) (fun x ↦ ?_) ?_
  · have hx := hcomm x x
    have hneg : (d : ℤ).negOnePow = -1 := Int.negOnePow_odd _ (by exact_mod_cast hd)
    rw [hneg, Units.neg_smul, one_smul] at hx
    have : (2 : PadicAlgCl l) * T.pairing d d h x x = 0 := by
      rw [two_mul]
      nth_rewrite 1 [hx]
      exact neg_add_cancel _
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  · exact ⟨LinearMap.separatingLeft_iff_ker_eq_bot.2
      (LinearMap.ker_eq_bot.2 (LinearMap.IsPerfPair.bijective_left B).1),
      LinearMap.separatingRight_iff_flip_ker_eq_bot.2
        (LinearMap.ker_eq_bot.2 (LinearMap.IsPerfPair.bijective_right B).1)⟩

/-- Blueprint `corollary-functional-equation--4` (duality reciprocity): for `X₀` smooth, proper and
geometrically connected of pure dimension `d`, a prime `ℓ ≠ p`, and the integral Frobenius
factors `P₀, …, P_{2d}`:

* Poincaré duality identifies the Frobenius eigenvalues in degree `2d - i` with the `qᵈ / α`,
  `α` running over the eigenvalues in degree `i`, with multiplicity;
* `bᵢ = b_{2d-i}` and `Dᵢ D_{2d-i} = q^{d bᵢ}`;
* `P_{2d-i}(q^{-d} t⁻¹) = (-1)^{bᵢ} t^{-bᵢ} Dᵢ⁻¹ Pᵢ(t)` for every `t ≠ 0` (the identity of Laurent
  polynomials, evaluated at all nonzero complex points);
* for odd `d` the middle Betti number `b_d` is even. -/
theorem duality_reciprocity (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    (∀ i j : ℤ, i + j = 2 * d →
      ((WeilSheaf.adicConstant k₀ l X).cohomology j).frobeniusEnd.charpoly.roots =
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.charpoly.roots.map
          fun α ↦ (Nat.card k₀ : PadicAlgCl l) ^ d / α) ∧
    (∀ i : Fin (2 * d + 1), (P i.rev).natDegree = (P i).natDegree) ∧
    (∀ i : Fin (2 * d + 1), weilDeterminantConstant (P i) * weilDeterminantConstant (P i.rev) =
      (Nat.card k₀ : ℤ) ^ (d * (P i).natDegree)) ∧
    (∀ (i : Fin (2 * d + 1)) (t : ℂ), t ≠ 0 →
      ((P i.rev).map (Int.castRingHom ℂ)).eval ((Nat.card k₀ : ℂ) ^ (-(d : ℤ)) * t⁻¹) =
        (-1) ^ (P i).natDegree * t ^ (-((P i).natDegree : ℤ)) *
          (weilDeterminantConstant (P i) : ℂ)⁻¹ * ((P i).map (Int.castRingHom ℂ)).eval t) ∧
    (Odd d → ∀ m : Fin (2 * d + 1), (m : ℕ) = d → Even (P m).natDegree) := by
  obtain ⟨hfact, hfe, -⟩ := isWeilFactorization_of_isIntegralFrobeniusFactor k₀ X d hP
  have hq : Nat.card k₀ ≠ 0 := Nat.card_pos.ne'
  obtain ⟨T, -, -, -, -, -, -, hrec, -⟩ := WeilSheaf.poincareDuality k₀ l X d
  refine ⟨fun i j h ↦ (hrec i j h).2, hfe.natDegree_rev, fun i ↦ ?_, fun i t ht ↦ ?_,
    fun hd m hm ↦ ?_⟩
  · have h := hfe.leadingCoeff_mul_leadingCoeff_rev hq hfact.coeff_zero_eq_one i
    rw [weilDeterminantConstant_eq, weilDeterminantConstant_eq, hfe.natDegree_rev i,
      ← h]
    ring_nf
    rw [(Nat.even_mul.2 (Or.inr even_two)).neg_one_pow, mul_one]
  · have h := hfe.eval_zpow_mul_inv hq hfact.coeff_zero_eq_one i.rev ht
    rw [Fin.rev_rev, hfe.natDegree_rev i] at h
    have hsign : ((-1 : ℂ) ^ (P i).natDegree)⁻¹ = (-1) ^ (P i).natDegree := by
      rw [← inv_pow, inv_neg, inv_one]
    rw [h, weilDeterminantConstant_eq]
    push_cast
    rw [mul_inv, hsign]
    have h1 : ((-1 : ℂ) ^ (P i).natDegree) * (-1) ^ (P i).natDegree = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination (t ^ (-((P i).natDegree : ℤ)) * ((P i).leadingCoeff : ℂ)⁻¹ *
      ((P i).map (Int.castRingHom ℂ)).eval t) * h1.symm
  · rw [natDegree_eq_finrank_of_isIntegralFrobeniusFactor k₀ X (hP m) l, hm]
    exact even_finrank_cohomology_middle k₀ X d l hd

/-- Blueprint `corollary-functional-equation` (duality reciprocity of the factors): for the integral
Frobenius factors `Pᵢ` of `X₀`, with `bᵢ = deg Pᵢ` and `Dᵢ = (-1)^{bᵢ} [T^{bᵢ}] Pᵢ`,

`P_{2d-i}(q^{-d} T⁻¹) = (-1)^{bᵢ} T^{-bᵢ} Dᵢ⁻¹ Pᵢ(T)` and `Dᵢ D_{2d-i} = q^{d bᵢ}`,

and `d χ` is even, `χ = ∑ᵢ (-1)ⁱ bᵢ`. -/
theorem reciprocity {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    (∀ (i : Fin (2 * d + 1)) (t : ℂ), t ≠ 0 →
      ((P i.rev).map (Int.castRingHom ℂ)).eval ((Nat.card k₀ : ℂ) ^ (-(d : ℤ)) * t⁻¹) =
        (-1) ^ (P i).natDegree * t ^ (-((P i).natDegree : ℤ)) *
          (weilDeterminantConstant (P i) : ℂ)⁻¹ * ((P i).map (Int.castRingHom ℂ)).eval t) ∧
    (∀ i : Fin (2 * d + 1), weilDeterminantConstant (P i) * weilDeterminantConstant (P i.rev) =
      (Nat.card k₀ : ℤ) ^ (d * (P i).natDegree)) ∧
    Even ((d : ℤ) * Polynomial.alternatingNatDegreeSum P) := by
  obtain ⟨l, hl, hne⟩ := exists_prime_ne_ringChar k₀
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (ringChar k₀ ≠ l) := ⟨hne⟩
  obtain ⟨-, hrev, hD, hL, hmid⟩ := duality_reciprocity k₀ X d l hP
  refine ⟨hL, hD, ?_⟩
  let m : Fin (2 * d + 1) := ⟨d, by omega⟩
  have hm : m.rev = m := Fin.ext (by simp only [Fin.val_rev, m]; omega)
  obtain ⟨k, hk⟩ := Polynomial.even_alternatingNatDegreeSum_sub_of_natDegree_rev hrev hm
  rcases Nat.even_or_odd d with hd | hd
  · obtain ⟨e, he⟩ := hd
    refine ⟨(e : ℤ) * Polynomial.alternatingNatDegreeSum P, ?_⟩
    rw [show (d : ℤ) = e + e by exact_mod_cast he]
    ring
  · obtain ⟨b, hb⟩ := hmid hd m rfl
    refine ⟨(d : ℤ) * k + (d : ℤ) * b, ?_⟩
    have hchi : Polynomial.alternatingNatDegreeSum P = k + k + b + b := by
      have : ((P m).natDegree : ℤ) = b + b := by exact_mod_cast hb
      omega
    rw [hchi]
    ring

end Scheme

end AlgebraicGeometry
