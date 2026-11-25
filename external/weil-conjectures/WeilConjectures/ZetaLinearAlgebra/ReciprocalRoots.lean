/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.Mathlib.Algebra.Polynomial.Splits
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.ZetaLinearAlgebra.Fatou

/-!
# Ordinary roots, reciprocal roots and normalized integral fractions

Let `P` be a polynomial over a field with `P(0) = 1`. Its *ordinary roots* are its roots `β`;
they are nonzero. Its *reciprocal roots* are the nonzero `α` with `P(α⁻¹) = 0`; they are the
roots of the reversed polynomial `P.reverse`, and if `P` splits then
`P = ∏ (1 - α X)` over its reciprocal roots `α`, counted with multiplicity
(blueprint `definition-reciprocal-root--1`).

For an endomorphism `f` of a finite-dimensional vector space over an algebraically closed field,
the reciprocal roots of `det (1 - X f)` are the nonzero eigenvalues of `f`, with algebraic
multiplicity (blueprint `prose-19-08`).

Finally, we name the normalized reduced integral presentations `Z = A / B` of an integral power
series (blueprint `lemma-reduced-fractions-integer-coefficients--1`) and restate the integral Fatou
theorem in these terms (blueprint `lemma-reduced-fractions-integer-coefficients--1`).

## Main declarations

- `Polynomial.reverse_multiset_prod_one_sub_C_mul_X`: the reverse of `∏ (1 - a X)` is
  `∏ (X - a)` when no `a` vanishes.
- `Polynomial.ordinary_reciprocal_roots`: blueprint `definition-reciprocal-root--1`.
- `LinearMap.roots_reverse_charpolyRev`, `LinearMap.reciprocal_roots_eigenvalues`: blueprint
  `prose-19-08`.
- `PowerSeries.IsNormalizedIntegralFraction`: blueprint
`lemma-reduced-fractions-integer-coefficients--1`.
- `PowerSeries.existsUnique_isNormalizedIntegralFraction`: blueprint
  `lemma-reduced-fractions-integer-coefficients--1`.
-/

@[expose] public section

open Polynomial

namespace Polynomial

section CommRing

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The reverse of `∏ (1 - a X)` is `∏ (X - a)` when none of the `a` vanishes. -/
theorem reverse_multiset_prod_one_sub_C_mul_X {s : Multiset R} (hs : (0 : R) ∉ s) :
    ((s.map fun a ↦ 1 - C a * X).prod).reverse = (s.map fun a ↦ X - C a).prod := by
  rw [← reverse_multiset_prod_X_sub_C]
  refine reverse_reverse (natTrailingDegree_eq_zero_of_constantCoeff_ne_zero ?_)
  rw [map_multiset_prod, Multiset.map_map]
  refine Multiset.prod_ne_zero fun h ↦ ?_
  obtain ⟨a, ha, h0⟩ := Multiset.mem_map.1 h
  rw [Function.comp_apply, map_sub, constantCoeff_apply, constantCoeff_apply, coeff_X_zero,
    coeff_C_zero, zero_sub, neg_eq_zero] at h0
  exact hs (h0 ▸ ha)

end CommRing

variable {K : Type*} [Field K]

/-- A root of `P.reverse` is nonzero as soon as `P ≠ 0`. -/
theorem ne_zero_of_mem_roots_reverse {P : K[X]} {α : K} (h : α ∈ P.reverse.roots) : α ≠ 0 := by
  rintro rfl
  obtain ⟨hne, hroot⟩ := mem_roots'.1 h
  rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_zero_reverse, leadingCoeff_eq_zero,
    ← reverse_eq_zero] at hroot
  exact hne hroot

/-- The roots of `P.reverse` are the nonzero `α` with `P(α⁻¹) = 0`. -/
theorem mem_roots_reverse_iff {P : K[X]} (hP : P ≠ 0) {α : K} :
    α ∈ P.reverse.roots ↔ α ≠ 0 ∧ P.IsRoot α⁻¹ := by
  have key : α ≠ 0 → (α ∈ P.reverse.roots ↔ P.IsRoot α⁻¹) := fun hα ↦ by
    let : Invertible α⁻¹ := invertibleOfNonzero (inv_ne_zero hα)
    rw [mem_roots (reverse_eq_zero.not.2 hP), IsRoot, IsRoot, eval, eval]
    conv_lhs => rw [← inv_inv α, ← invOf_eq_inv α⁻¹]
    exact eval₂_reverse_eq_zero_iff _ _ _
  exact ⟨fun h ↦ ⟨ne_zero_of_mem_roots_reverse h, (key (ne_zero_of_mem_roots_reverse h)).1 h⟩,
    fun ⟨hα, h⟩ ↦ (key hα).2 h⟩

/-- Blueprints `definition-reciprocal-root--1` and `definition-reciprocal-root` (ordinary and
reciprocal roots): let `P` be a polynomial with `P(0) = 1`.
1. Its *ordinary roots* (the roots of `P`) are nonzero.
2. Its *reciprocal roots*, the nonzero `α` with `P(α⁻¹) = 0`, are the roots of `P.reverse`.
3. If `P` splits (e.g. over an algebraically closed field), the reciprocal roots are the
   inverses of the ordinary roots, with multiplicity, and `P = ∏ (1 - α X)`, the product running
   over the reciprocal roots counted with multiplicity. -/
theorem ordinary_reciprocal_roots {P : K[X]} (h0 : P.coeff 0 = 1) :
    (∀ β ∈ P.roots, β ≠ 0) ∧ (∀ α, α ∈ P.reverse.roots ↔ α ≠ 0 ∧ P.IsRoot α⁻¹) ∧
      (P.Splits → P.reverse.roots = P.roots.map (·⁻¹) ∧
        P = (P.reverse.roots.map fun α ↦ 1 - C α * X).prod) := by
  have hP : P ≠ 0 := fun h ↦ by simp [h] at h0
  have hz : ∀ β ∈ P.roots, β ≠ 0 := by
    rintro β hβ rfl
    have h := (mem_roots'.1 hβ).2
    rw [IsRoot, ← coeff_zero_eq_eval_zero, h0] at h
    exact one_ne_zero h
  refine ⟨hz, fun α ↦ mem_roots_reverse_iff hP, fun hs ↦ ?_⟩
  have hprod : P = ((P.roots.map (·⁻¹)).map fun α ↦ 1 - C α * X).prod := by
    rw [Multiset.map_map]
    exact eq_prod_one_sub_inv_roots hs h0
  have h0s : (0 : K) ∉ P.roots.map (·⁻¹) := by
    intro h
    obtain ⟨β, hβ, h⟩ := Multiset.mem_map.1 h
    exact hz β hβ (inv_eq_zero.1 h)
  have hrev : P.reverse.roots = P.roots.map (·⁻¹) := by
    conv_lhs => rw [hprod]
    rw [reverse_multiset_prod_one_sub_C_mul_X h0s, roots_multiset_prod_X_sub_C]
  exact ⟨hrev, hrev ▸ hprod⟩

end Polynomial

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [IsAlgClosed K] [DecidableEq K]

/-- The reciprocal roots of `det (1 - X f)` (the roots of its reverse) are the nonzero
eigenvalues of `f`, counted with algebraic multiplicity. -/
theorem roots_reverse_charpolyRev (f : Module.End K V) :
    f.charpolyRev.reverse.roots = f.charpoly.roots.filter (· ≠ 0) := by
  have h1 : ((f.charpoly.roots.filter fun a ↦ ¬a ≠ 0).map fun a ↦ 1 - C a * X).prod = 1 := by
    refine Multiset.prod_eq_one fun x hx ↦ ?_
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hx
    rw [not_not.1 (Multiset.mem_filter.1 ha).2, C_0, zero_mul, sub_zero]
  have hprod : f.charpolyRev =
      ((f.charpoly.roots.filter (· ≠ 0)).map fun a ↦ 1 - C a * X).prod := by
    conv_lhs => rw [charpolyRev_eq_prod_roots, ← Multiset.filter_add_not (· ≠ 0) f.charpoly.roots]
    rw [Multiset.map_add, Multiset.prod_add, h1, mul_one]
  rw [hprod, reverse_multiset_prod_one_sub_C_mul_X (fun h ↦ (Multiset.of_mem_filter h) rfl),
    roots_multiset_prod_X_sub_C]

omit [DecidableEq K] in
/-- Blueprint `prose-19-08`: for an invertible endomorphism `f` of a
finite-dimensional vector space over an algebraically closed field, the reciprocal roots of
`P = det (1 - X f)` (the roots of `P.reverse`) are exactly the eigenvalues of `f` (the roots of
its characteristic polynomial), counted with algebraic multiplicity, and
`det (1 - X f) = ∏ (1 - α X)` over them. -/
theorem reciprocal_roots_eigenvalues (f : Module.End K V) (hf : IsUnit f.det) :
    f.charpolyRev.reverse.roots = f.charpoly.roots ∧
      f.charpolyRev = (f.charpolyRev.reverse.roots.map fun α ↦ 1 - C α * X).prod := by
  classical
  have h : f.charpolyRev.reverse.roots = f.charpoly.roots := by
    rw [roots_reverse_charpolyRev, Multiset.filter_eq_self]
    exact fun a ha h ↦ zero_notMem_roots_charpoly hf (h ▸ ha)
  exact ⟨h, h ▸ charpolyRev_eq_prod_roots f⟩

end LinearMap

namespace PowerSeries

/-- Blueprints `lemma-reduced-fractions-integer-coefficients--1` and `definition-reciprocal-root`:
a *normalized reduced integral
presentation* of a power series `Z ∈ ℚ⟦X⟧` is a pair `A, B ∈ ℤ[X]` with `A(0) = B(0) = 1`, `A`
and `B` coprime in `ℚ[X]`, and `Z * B = A` as power series. -/
def IsNormalizedIntegralFraction (Z : ℚ⟦X⟧) (A B : ℤ[X]) : Prop :=
  A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
    IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
    Z * (B.map (Int.castRingHom ℚ) : ℚ⟦X⟧) = (A.map (Int.castRingHom ℚ) : ℚ⟦X⟧)

/-- For an integral power series `f`, the identity `Z * B = A` of
`IsNormalizedIntegralFraction` may be read in `ℤ⟦X⟧`. -/
theorem isNormalizedIntegralFraction_map_iff (f : ℤ⟦X⟧) (A B : ℤ[X]) :
    IsNormalizedIntegralFraction (map (Int.castRingHom ℚ) f) A B ↔
      A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
        IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
        f * (B : ℤ⟦X⟧) = (A : ℤ⟦X⟧) := by
  unfold IsNormalizedIntegralFraction
  rw [Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe, ← map_mul,
    (map_injective _ Int.cast_injective).eq_iff]

/-- Blueprint `lemma-reduced-fractions-integer-coefficients--1` (Fatou): a power series
`f ∈ 1 + X ℤ⟦X⟧` that is rational over `ℚ` has a unique normalized reduced integral presentation
`f = A / B`. This restates `PowerSeries.exists_unique_reduced_int_fraction`. -/
theorem existsUnique_isNormalizedIntegralFraction (f : ℤ⟦X⟧) (h₀ : constantCoeff f = 1)
    (h : ∃ A B : ℚ[X], B.coeff 0 = 1 ∧
      map (Int.castRingHom ℚ) f * (B : ℚ⟦X⟧) = (A : ℚ⟦X⟧)) :
    ∃! p : ℤ[X] × ℤ[X], IsNormalizedIntegralFraction (map (Int.castRingHom ℚ) f) p.1 p.2 := by
  simpa only [isNormalizedIntegralFraction_map_iff] using
    exists_unique_reduced_int_fraction f h₀ h

end PowerSeries
