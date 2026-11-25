/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import WeilConjectures.Mathlib.Algebra.Polynomial.BigOperators
public import WeilConjectures.Mathlib.Data.Fin.Rev
public import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.ZetaFunction.BettiNumbers

/-!
# The functional equation in its classical form

Let `P 0, …, P_{2d} ∈ ℤ[T]` be a family of Weil factors, in the sense of
`AlgebraicGeometry.IsWeilFactorization`, of the zeta function of a smooth proper geometrically
integral scheme of dimension `d` over a finite field with `q` elements. Writing
`b i = deg (P i)`, `χ = ∑ᵢ (-1)ⁱ b i` for `Polynomial.alternatingNatDegreeSum P` and
`Dᵢ = (-1)^{b i} · [T^{b i}] P i` for the determinant constant of degree `i`, the *normalized
functional-equation sign* is

`ε = (-1)^χ · q^{-m} · ∏ᵢ (Dᵢ)^{(-1)ⁱ}`, where `2 m = d χ`,

and the classical functional equation reads

`Z (q^{-d} T⁻¹) = ε · q^{m} · T^χ · Z (T)`.

`AlgebraicGeometry.WeilFunctionalEquation` states the same thing as a matching of reciprocal
roots, which is how the Weil conjectures are stated in `WeilConjectures.Statement`; the present
file records the classical shape, as an identity of complex numbers at every point where the
factors do not vanish. The left-hand side is the alternating product
`Polynomial.alternatingProdEval` of the values of the complexified factors, which is the value
of the zeta function `Z` on the region where the product converges; that identification is not
stated in this repository, and no declaration here mentions `Z`.

That `d χ` is even, so that a half `m` exists, is
`TraceDatum.even_mul_alternatingNatDegreeSum_of_pairing`.

This file formalises the functional-equation subsection `corollary-functional-equation` of the
blueprint block on zeta functions and the Weil conjectures. The blueprint deduces it from the
Poincaré duality reciprocity relations of the Frobenius factors; here those relations are derived
directly from the matching of reciprocal roots in `AlgebraicGeometry.WeilFunctionalEquation`, via
`Polynomial.eval_inv_mul_inv_of_roots_eq_map_inv` and
`Polynomial.leadingCoeff_mul_leadingCoeff_of_roots_eq_map_inv`.

## Main definitions

- `AlgebraicGeometry.weilSign`: the normalized sign `ε`.

## Main statements

- `AlgebraicGeometry.WeilFunctionalEquation.eval_zpow_mul_inv`: reciprocity of the factors,
  `P i (q^{-d} t⁻¹) = t^{-b i} (lc P_{2d-i})⁻¹ P_{2d-i} (t)`.
- `AlgebraicGeometry.WeilFunctionalEquation.prod_determinant_sq`: `(∏ᵢ Dᵢ^{(-1)ⁱ})² = q^{d χ}`.
- `AlgebraicGeometry.weilSign_eq_one_or_eq_neg_one`: `ε = ±1`.
- `AlgebraicGeometry.WeilFunctionalEquation.alternatingProdEval_eq_prod_determinant`: the
  functional equation in determinant-constant form.
- `AlgebraicGeometry.WeilFunctionalEquation.alternatingProdEval_eq`: the classical functional
  equation.

## References

- [A. Weil, *Numbers of solutions of equations in finite fields*][weil1949]
- [J.-P. Serre, *Zeta and L functions*][serre1965]
-/

@[expose] public section

namespace AlgebraicGeometry

/-- The normalized functional-equation sign `ε = (-1)^χ q^{-m} ∏ᵢ (Dᵢ)^{(-1)ⁱ}` of a family of
Weil factors (blueprint `corollary-functional-equation--8`), where `χ` is
`Polynomial.alternatingNatDegreeSum P`, `Dᵢ = (-1)^{deg (P i)} · [T^{deg (P i)}] P i`, and `m` is
the half `d χ / 2` of the exponent appearing in the functional equation. The half is an
argument rather than the truncating integer division `d * χ / 2`, so that the definition carries
no junk value; that `d χ` is even is `TraceDatum.even_mul_alternatingNatDegreeSum_of_pairing`. -/
noncomputable def weilSign (q : ℕ) (m : ℤ) {n : ℕ} (P : Fin (n + 1) → Polynomial ℤ) : ℚ :=
  (-1) ^ Polynomial.alternatingNatDegreeSum P * (q : ℚ) ^ (-m) *
    ∏ i : Fin (n + 1),
      ((-1) ^ (P i).natDegree * ((P i).leadingCoeff : ℚ)) ^ ((-1 : ℤ) ^ (i : ℕ))

/-- **The determinant product rule.** For a family of normalized Weil factors satisfying the
functional equation, the leading coefficients in degrees `i` and `2 d - i` multiply to
`q ^ (d · b i)`, where `b i = deg (P i)`. Up to the signs `(-1)^{b i}`, which cancel, these
leading coefficients are the determinant constants `Dᵢ`, so this is `Dᵢ D_{2d-i} = q^{d b i}`. -/
theorem WeilFunctionalEquation.leadingCoeff_mul_leadingCoeff_rev {q d : ℕ} (hq : q ≠ 0)
    {P : Fin (2 * d + 1) → Polynomial ℤ} (h0 : ∀ i, (P i).coeff 0 = 1)
    (hfe : WeilFunctionalEquation q d P) (i : Fin (2 * d + 1)) :
    (P i).leadingCoeff * (P i.rev).leadingCoeff = (q : ℤ) ^ (d * (P i).natDegree) := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have h0' : ∀ j, ((P j).map (Int.castRingHom ℂ)).coeff 0 = 1 := fun j ↦ by simp [h0 j]
  have h := Polynomial.leadingCoeff_mul_leadingCoeff_of_roots_eq_map_inv (h0' i) (h0' i.rev)
    (pow_ne_zero d (Nat.cast_ne_zero.2 hq)) (hfe i)
  rw [Polynomial.leadingCoeff_map_of_injective hinj,
    Polynomial.leadingCoeff_map_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj, ← pow_mul] at h
  simp only [eq_intCast] at h
  exact_mod_cast h

/-- **Reciprocity of the Weil factors.** For a family of normalized Weil factors satisfying the
functional equation, `P i (q^{-d} t⁻¹) = t^{-b i} · (lc P_{2d-i})⁻¹ · P_{2d-i} (t)` for every
`t ≠ 0`, where `b i = deg (P i)`. -/
theorem WeilFunctionalEquation.eval_zpow_mul_inv {q d : ℕ} (hq : q ≠ 0)
    {P : Fin (2 * d + 1) → Polynomial ℤ} (h0 : ∀ i, (P i).coeff 0 = 1)
    (hfe : WeilFunctionalEquation q d P) (i : Fin (2 * d + 1)) {t : ℂ} (ht : t ≠ 0) :
    ((P i).map (Int.castRingHom ℂ)).eval ((q : ℂ) ^ (-(d : ℤ)) * t⁻¹) =
      t ^ (-((P i).natDegree : ℤ)) * ((P i.rev).leadingCoeff : ℂ)⁻¹ *
        ((P i.rev).map (Int.castRingHom ℂ)).eval t := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have h0' : ∀ j, ((P j).map (Int.castRingHom ℂ)).coeff 0 = 1 := fun j ↦ by simp [h0 j]
  have h := Polynomial.eval_inv_mul_inv_of_roots_eq_map_inv (h0' i) (h0' i.rev)
    (pow_ne_zero d (Nat.cast_ne_zero.2 hq)) (hfe i) ht
  rw [Polynomial.leadingCoeff_map_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj] at h
  rw [zpow_neg, zpow_natCast, h]
  rfl

/-- **The square of the determinant scalar** (blueprint `corollary-functional-equation`, first
claim). For a family of normalized Weil factors satisfying the functional equation, the
alternating product `Δ = ∏ᵢ Dᵢ^{(-1)ⁱ}` of the determinant constants
`Dᵢ = (-1)^{b i} · [T^{b i}] P i` satisfies `Δ² = q^{d χ}`, where
`χ = Polynomial.alternatingNatDegreeSum P`. -/
theorem WeilFunctionalEquation.prod_determinant_sq {q d : ℕ} (hq : 1 < q)
    {P : Fin (2 * d + 1) → Polynomial ℤ} (h0 : ∀ i, (P i).coeff 0 = 1)
    (hfe : WeilFunctionalEquation q d P) :
    (∏ i : Fin (2 * d + 1),
      ((-1) ^ (P i).natDegree * ((P i).leadingCoeff : ℚ)) ^ ((-1 : ℤ) ^ (i : ℕ))) ^ 2 =
      (q : ℚ) ^ ((d : ℤ) * Polynomial.alternatingNatDegreeSum P) := by
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set D : Fin (2 * d + 1) → ℚ := fun i ↦ (-1) ^ (P i).natDegree * ((P i).leadingCoeff : ℚ)
  have hD : ∀ i, D i * D i.rev = (q : ℚ) ^ (d * (P i).natDegree) := fun i ↦ by
    have h := hfe.leadingCoeff_mul_leadingCoeff_rev (by omega) h0 i
    simp only [D, hfe.natDegree_rev i]
    rw [show ((-1 : ℚ) ^ (P i).natDegree * (P i).leadingCoeff) *
        ((-1) ^ (P i).natDegree * (P i.rev).leadingCoeff) =
        ((-1) ^ (P i).natDegree * (-1) ^ (P i).natDegree) *
          ((P i).leadingCoeff * (P i.rev).leadingCoeff : ℤ) by push_cast; ring,
      ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    exact_mod_cast h
  have hrev : ∏ i : Fin (2 * d + 1), D i ^ ((-1 : ℤ) ^ (i : ℕ)) =
      ∏ i : Fin (2 * d + 1), D i.rev ^ ((-1 : ℤ) ^ (i : ℕ)) := by
    conv_lhs => rw [← Equiv.prod_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, Fin.neg_one_pow_rev]
  rw [sq]
  nth_rewrite 2 [hrev]
  rw [← Finset.prod_mul_distrib, Polynomial.alternatingNatDegreeSum, Finset.mul_sum,
    zpow_sum₀ hq0]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← mul_zpow, hD i, ← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

/-- **The corollary-functional-equation--9 sign is `±1`** (blueprint
`corollary-functional-equation`). For a family of normalized Weil factors satisfying the functional
equation, the normalized sign `ε` is `1` or `-1`: the determinant constants pair up under
`i ↦ 2 d - i` into powers of `q` by the reciprocity product rule, and those powers are exactly what
`q^{-m}` cancels. -/
theorem weilSign_eq_one_or_eq_neg_one {q d : ℕ} (hq : 1 < q) {m : ℤ}
    {P : Fin (2 * d + 1) → Polynomial ℤ} (h0 : ∀ i, (P i).coeff 0 = 1)
    (hfe : WeilFunctionalEquation q d P)
    (hm : (d : ℤ) * Polynomial.alternatingNatDegreeSum P = 2 * m) :
    weilSign q m P = 1 ∨ weilSign q m P = -1 := by
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine mul_self_eq_one_iff.1 ?_
  have h1 : ((-1 : ℚ) ^ Polynomial.alternatingNatDegreeSum P) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num
  have h2 : ((q : ℚ) ^ (-m)) ^ 2 * (q : ℚ) ^ (2 * m) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq0]
    ring_nf
    exact zpow_zero _
  rw [← sq, weilSign, mul_pow, mul_pow, hfe.prod_determinant_sq hq h0, hm, h1, one_mul, h2]

/-- **The functional equation in determinant-constant form** (blueprint
`corollary-functional-equation`, last claim). The alternating product of the values of a family of
normalized Weil factors satisfying the functional equation obeys
`Z (q^{-d} t⁻¹) = (-1)^χ t^χ (∏ᵢ Dᵢ^{(-1)ⁱ}) Z (t)` at every nonzero `t`, where
`Dᵢ = (-1)^{b i} · [T^{b i}] P i` and `χ = Polynomial.alternatingNatDegreeSum P`. -/
theorem WeilFunctionalEquation.alternatingProdEval_eq_prod_determinant {q d : ℕ} (hq : q ≠ 0)
    {P : Fin (2 * d + 1) → Polynomial ℤ} (h0 : ∀ i, (P i).coeff 0 = 1)
    (hfe : WeilFunctionalEquation q d P) {t : ℂ} (ht : t ≠ 0) :
    Polynomial.alternatingProdEval (fun i ↦ (P i).map (Int.castRingHom ℂ))
        ((q : ℂ) ^ (-(d : ℤ)) * t⁻¹) =
      (-1) ^ Polynomial.alternatingNatDegreeSum P * t ^ Polynomial.alternatingNatDegreeSum P *
        (∏ i : Fin (2 * d + 1),
          ((-1) ^ (P i).natDegree * ((P i).leadingCoeff : ℂ)) ^ ((-1 : ℤ) ^ (i : ℕ))) *
        Polynomial.alternatingProdEval (fun i ↦ (P i).map (Int.castRingHom ℂ)) t := by
  have key : ∀ i : Fin (2 * d + 1),
      ((P i.rev).map (Int.castRingHom ℂ)).eval ((q : ℂ) ^ (-(d : ℤ)) * t⁻¹) ^
          ((-1 : ℤ) ^ ((i.rev : ℕ) + 1)) =
        (-1) ^ ((-1 : ℤ) ^ (i : ℕ) * (P i).natDegree) *
          t ^ ((-1 : ℤ) ^ (i : ℕ) * (P i).natDegree) *
          ((-1) ^ (P i).natDegree * ((P i).leadingCoeff : ℂ)) ^ ((-1 : ℤ) ^ (i : ℕ)) *
          ((P i).map (Int.castRingHom ℂ)).eval t ^ ((-1 : ℤ) ^ ((i : ℕ) + 1)) := by
    intro i
    rw [hfe.eval_zpow_mul_inv hq h0 i.rev ht, Fin.rev_rev, hfe.natDegree_rev i, pow_succ,
      Fin.neg_one_pow_rev, ← pow_succ]
    have hc : ((P i).leadingCoeff : ℂ) ≠ 0 := by
      simpa using (Polynomial.leadingCoeff_ne_zero.2 fun h ↦ by simpa [h] using h0 i)
    rcases neg_one_pow_eq_or ℤ (i : ℕ) with h | h <;>
      simp only [pow_succ, h, zpow_neg, zpow_one, neg_mul, one_mul, neg_neg, zpow_natCast,
        mul_inv, inv_inv] <;>
      field_simp <;>
      simp [← pow_mul]
  rw [Polynomial.alternatingProdEval, Polynomial.alternatingProdEval,
    ← Equiv.prod_comp Fin.revPerm]
  simp only [Fin.revPerm_apply]
  rw [Finset.prod_congr rfl fun i _ ↦ key i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, ← zpow_sum₀ (neg_ne_zero.2 one_ne_zero),
    ← zpow_sum₀ ht, Polynomial.alternatingNatDegreeSum]

/-- **The classical functional equation** (blueprint `corollary-functional-equation`, and the main
claim of `corollary-functional-equation`). The alternating product of the values of a family of
normalized Weil factors satisfying the functional equation obeys
`Z (q^{-d} t⁻¹) = ε q^{m} t^χ Z (t)` at every nonzero `t` at which no factor vanishes, where
`2 m = d χ`.

Substituting the reciprocity relation of each factor and reindexing by `i ↦ 2 d - i` gives the
determinant-constant form `WeilFunctionalEquation.alternatingProdEval_eq_prod_determinant`, and
`(-1)^χ ∏ᵢ Dᵢ^{(-1)ⁱ} = ε q^m` by definition of `ε`. Neither the evenness `2 m = d χ` nor the
nonvanishing of the factors at `t` is needed for the identity itself. -/
theorem WeilFunctionalEquation.alternatingProdEval_eq {q d : ℕ} (hq : 1 < q) {m : ℤ}
    {P : Fin (2 * d + 1) → Polynomial ℤ} (h0 : ∀ i, (P i).coeff 0 = 1)
    (hfe : WeilFunctionalEquation q d P)
    (_hm : (d : ℤ) * Polynomial.alternatingNatDegreeSum P = 2 * m)
    (t : ℂ) (ht : t ≠ 0)
    (_hne : ∀ i, ((P i).map (Int.castRingHom ℂ)).eval t ≠ 0) :
    Polynomial.alternatingProdEval (fun i ↦ (P i).map (Int.castRingHom ℂ))
        ((q : ℂ) ^ (-(d : ℤ)) * t⁻¹) =
      (weilSign q m P : ℂ) * (q : ℂ) ^ m * t ^ Polynomial.alternatingNatDegreeSum P *
        Polynomial.alternatingProdEval (fun i ↦ (P i).map (Int.castRingHom ℂ)) t := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [hfe.alternatingProdEval_eq_prod_determinant (by omega) h0 ht, weilSign]
  push_cast
  have hqm : (q : ℂ) ^ (-m) * (q : ℂ) ^ m = 1 := by rw [← zpow_add₀ hq0]; simp
  linear_combination
    (-((-1) ^ Polynomial.alternatingNatDegreeSum P * t ^ Polynomial.alternatingNatDegreeSum P *
        (∏ i : Fin (2 * d + 1),
          ((-1) ^ (P i).natDegree * ((P i).leadingCoeff : ℂ)) ^ ((-1 : ℤ) ^ (i : ℕ))) *
        Polynomial.alternatingProdEval (fun i ↦ (P i).map (Int.castRingHom ℂ)) t)) * hqm

end AlgebraicGeometry

end
