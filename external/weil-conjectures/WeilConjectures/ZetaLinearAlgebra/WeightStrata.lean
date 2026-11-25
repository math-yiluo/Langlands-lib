/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.ZetaLinearAlgebra.Weights

/-!
# Weight strata of a rational polynomial

Let `R ∈ ℚ[T]` have constant coefficient `1`. Its complex roots split into the ones that are
universally pure of weight `w` — every conjugate has absolute value `q ^ (-w / 2)` — and the
others. This file shows that this partition of the roots comes from a factorisation of `R`
*over `ℚ`*: the corresponding factor is a product of irreducible rational factors of `R`, and is
the unique normalized complex factor with the given roots.

The point is that the *universal* purity condition is constant on each irreducible rational
factor `f` of `R`: `f` is, up to a scalar, the minimal polynomial of each of its complex roots.
So no Galois descent is needed — the stratum is a product of rational polynomials by
construction. This fails for purity under a single embedding: the roots of
`(1 - (1 + √2) T) (1 - (1 - √2) T) ∈ ℚ[T]` of a given absolute value do not cut out a rational
factor.

## Main results

- `Polynomial.weightFactor`, `Polynomial.coweightFactor` — the product of the normalized
  irreducible rational factors of `R` all of whose complex roots have absolute value
  `q ^ (-w / 2)`, and the product of the remaining ones.
- `Polynomial.weightFactor_mul_coweightFactor` — the two factors multiply back to `R`.
- `Polynomial.roots_map_weightFactor` — the complex roots of `R.weightFactor q w` are exactly
  the roots of `R` that are universally pure of weight `w`.
- `Polynomial.eq_map_weightFactor_of_isUniversallyPure` — a normalized complex factorisation of
  `R` separating the universally pure roots of weight `w` from the others has
  `(R.weightFactor q w).map (algebraMap ℚ ℂ)` as its pure part.
-/

@[expose] public section

open scoped Polynomial

open UniqueFactorizationMonoid

namespace Polynomial

/-! ### Products of normalized irreducible factors -/

variable {q w : ℕ} {R : ℚ[X]}

private lemma coeff_zero_ne_zero_of_mem_normalizedFactors (hR : R.coeff 0 = 1) {f : ℚ[X]}
    (hf : f ∈ normalizedFactors R) : f.coeff 0 ≠ 0 := by
  obtain ⟨g, hg⟩ := dvd_of_mem_normalizedFactors hf
  intro h0
  rw [hg, mul_coeff_zero, h0, zero_mul] at hR
  exact zero_ne_one hR

/-- Rescaling each element of `s` to constant coefficient `1` only changes the product of `s` by
a scalar. -/
private lemma prod_map_normalize (s : Multiset ℚ[X]) :
    (s.map fun f => C (f.coeff 0)⁻¹ * f).prod
      = C ((s.map fun f => (f.coeff 0)⁻¹).prod) * s.prod := by
  rw [Multiset.prod_map_mul, Multiset.map_id', map_multiset_prod, Multiset.map_map]
  rfl

/-- A product of polynomials rescaled to constant coefficient `1` has constant coefficient
`1`. -/
private lemma coeff_zero_prod_map_normalize {s : Multiset ℚ[X]} (hs : ∀ f ∈ s, f.coeff 0 ≠ 0) :
    ((s.map fun f => C (f.coeff 0)⁻¹ * f).prod).coeff 0 = 1 := by
  have h : constantCoeff ((s.map fun f => C (f.coeff 0)⁻¹ * f).prod) = 1 := by
    rw [map_multiset_prod]
    refine Multiset.prod_eq_one ?_
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.1 hp
    simp [inv_mul_cancel₀ (hs f hf)]
  simpa using h

/-- The complex roots of a product of polynomials rescaled to constant coefficient `1` are the
complex roots of the factors, with multiplicity. -/
private lemma roots_map_prod_map_normalize {s : Multiset ℚ[X]} (hs : ∀ f ∈ s, f.coeff 0 ≠ 0) :
    (((s.map fun f => C (f.coeff 0)⁻¹ * f).prod).map (algebraMap ℚ ℂ)).roots
      = s.bind fun f => (f.map (algebraMap ℚ ℂ)).roots := by
  have hne : ∀ f ∈ s, f ≠ 0 := fun f hf h0 => hs f hf (by simp [h0])
  have hc : (s.map fun f => (f.coeff 0)⁻¹).prod ≠ 0 := by
    refine Multiset.prod_ne_zero ?_
    intro h0
    obtain ⟨f, hf, hf0⟩ := Multiset.mem_map.1 h0
    exact hs f hf (inv_eq_zero.1 hf0)
  have hmap : s.prod.map (algebraMap ℚ ℂ) = (s.map fun f => f.map (algebraMap ℚ ℂ)).prod := by
    simpa using map_multiset_prod (mapRingHom (algebraMap ℚ ℂ)) s
  have h0mem : (0 : ℂ[X]) ∉ s.map fun f => f.map (algebraMap ℚ ℂ) := by
    intro h0
    obtain ⟨f, hf, hf0⟩ := Multiset.mem_map.1 h0
    exact hne f hf ((Polynomial.map_eq_zero_iff (algebraMap ℚ ℂ).injective).1 hf0)
  rw [prod_map_normalize, Polynomial.map_mul, map_C,
    roots_C_mul _ ((map_ne_zero_iff (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective).2 hc), hmap,
    roots_multiset_prod _ h0mem, Multiset.bind_map]

/-! ### The weight strata -/

open scoped Classical in
/-- The product of the irreducible factors of `R` (with multiplicity, normalized to constant
coefficient `1`) all of whose complex roots have absolute value `q ^ (-w / 2)`. -/
noncomputable def weightFactor (q w : ℕ) (R : ℚ[X]) : ℚ[X] :=
  (((normalizedFactors R).filter fun f =>
      ∀ z ∈ (f.map (algebraMap ℚ ℂ)).roots, ‖z‖ = (q : ℝ) ^ (-(w : ℝ) / 2)).map
    fun f => C (f.coeff 0)⁻¹ * f).prod

open scoped Classical in
/-- The complementary factor to `Polynomial.weightFactor`: the product of the irreducible factors
of `R` (with multiplicity, normalized to constant coefficient `1`) having a complex root whose
absolute value is not `q ^ (-w / 2)`. -/
noncomputable def coweightFactor (q w : ℕ) (R : ℚ[X]) : ℚ[X] :=
  (((normalizedFactors R).filter fun f =>
      ¬ ∀ z ∈ (f.map (algebraMap ℚ ℂ)).roots, ‖z‖ = (q : ℝ) ^ (-(w : ℝ) / 2)).map
    fun f => C (f.coeff 0)⁻¹ * f).prod

/-- The weight-`w` factor of a normalized polynomial is normalized. -/
theorem coeff_zero_weightFactor (hR : R.coeff 0 = 1) : (R.weightFactor q w).coeff 0 = 1 := by
  classical
  exact coeff_zero_prod_map_normalize fun f hf =>
    coeff_zero_ne_zero_of_mem_normalizedFactors hR (Multiset.mem_of_mem_filter hf)

/-- The complementary weight-`w` factor of a normalized polynomial is normalized. -/
theorem coeff_zero_coweightFactor (hR : R.coeff 0 = 1) : (R.coweightFactor q w).coeff 0 = 1 := by
  classical
  exact coeff_zero_prod_map_normalize fun f hf =>
    coeff_zero_ne_zero_of_mem_normalizedFactors hR (Multiset.mem_of_mem_filter hf)


/-- Splitting the irreducible factors of a normalized polynomial `R` according to any predicate
gives a factorisation of `R` into two normalized rational polynomials. -/
private lemma prod_filter_mul_prod_filter_not (hR : R.coeff 0 = 1) (P : ℚ[X] → Prop)
    [DecidablePred P] :
    ((((normalizedFactors R).filter P).map fun f => C (f.coeff 0)⁻¹ * f).prod) *
      ((((normalizedFactors R).filter fun f => ¬ P f).map fun f => C (f.coeff 0)⁻¹ * f).prod)
      = R := by
  have hR0 : R ≠ 0 := fun h => by rw [h] at hR; simp at hR
  have hs : ∀ f ∈ normalizedFactors R, f.coeff 0 ≠ 0 := fun f hf =>
    coeff_zero_ne_zero_of_mem_normalizedFactors hR hf
  set A := (normalizedFactors R).filter P with hA
  set B := (normalizedFactors R).filter fun f => ¬ P f with hB
  have hAB : A.prod * B.prod = (normalizedFactors R).prod := by
    rw [hA, hB, ← Multiset.prod_add, Multiset.filter_add_not]
  have hsA : ∀ f ∈ A, f.coeff 0 ≠ 0 := by
    intro f hf
    rw [hA, Multiset.mem_filter] at hf
    exact hs f hf.1
  have hsB : ∀ f ∈ B, f.coeff 0 ≠ 0 := by
    intro f hf
    rw [hB, Multiset.mem_filter] at hf
    exact hs f hf.1
  have hA1 : ((A.map fun f => C (f.coeff 0)⁻¹ * f).prod).coeff 0 = 1 :=
    coeff_zero_prod_map_normalize hsA
  have hB1 : ((B.map fun f => C (f.coeff 0)⁻¹ * f).prod).coeff 0 = 1 :=
    coeff_zero_prod_map_normalize hsB
  obtain ⟨u, hu⟩ := prod_normalizedFactors hR0
  obtain ⟨v, -, hvC⟩ := isUnit_iff.1 u.isUnit
  have hRN : (normalizedFactors R).prod * C v = R := by rw [hvC]; exact hu
  have hNv : v * (normalizedFactors R).prod.coeff 0 = 1 := by
    rw [mul_comm, ← coeff_C_zero (a := v), ← mul_coeff_zero, hRN, hR]
  have hN0 : (normalizedFactors R).prod.coeff 0 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hNv; exact zero_ne_one hNv
  rw [prod_map_normalize] at hA1 hB1
  rw [prod_map_normalize, prod_map_normalize]
  rw [mul_mul_mul_comm, ← C_mul, hAB]
  have hd : ((A.map fun f => (f.coeff 0)⁻¹).prod) * ((B.map fun f => (f.coeff 0)⁻¹).prod)
      * (normalizedFactors R).prod.coeff 0 = 1 := by
    rw [mul_coeff_zero, coeff_C_zero] at hA1 hB1
    rw [← hAB, mul_coeff_zero]
    calc _ = ((A.map fun f => (f.coeff 0)⁻¹).prod * A.prod.coeff 0) *
            ((B.map fun f => (f.coeff 0)⁻¹).prod * B.prod.coeff 0) := by ring
      _ = 1 := by rw [hA1, hB1, mul_one]
  have : ((A.map fun f => (f.coeff 0)⁻¹).prod) * ((B.map fun f => (f.coeff 0)⁻¹).prod) = v :=
    mul_right_cancel₀ hN0 (hd.trans hNv.symm)
  rw [this, mul_comm]
  exact hRN

/-- **The weight factorisation.** A normalized rational polynomial is the product of its
weight-`w` factor and the complementary factor. -/
theorem weightFactor_mul_coweightFactor (hR : R.coeff 0 = 1) :
    R.weightFactor q w * R.coweightFactor q w = R := by
  classical
  exact prod_filter_mul_prod_filter_not hR _

/-- The weight-`w` factor of a normalized rational polynomial divides it. -/
theorem weightFactor_dvd (hR : R.coeff 0 = 1) : R.weightFactor q w ∣ R :=
  ⟨R.coweightFactor q w, (weightFactor_mul_coweightFactor hR).symm⟩

/-- The complementary weight-`w` factor of a normalized rational polynomial divides it. -/
theorem coweightFactor_dvd (hR : R.coeff 0 = 1) : R.coweightFactor q w ∣ R :=
  Dvd.intro_left _ (weightFactor_mul_coweightFactor hR)


/-! ### The roots of the weight factor -/

/-- Universal purity of weight `w` is constant on the complex roots of an irreducible rational
factor `f` of `R`: such an `f` is, up to a scalar, the minimal polynomial of each of its roots. -/
private lemma isUniversallyPureOfWeight_iff_of_mem_normalizedFactors {f : ℚ[X]}
    (hf : f ∈ normalizedFactors R) {z : ℂ} (hz : z ∈ (f.map (algebraMap ℚ ℂ)).roots) :
    _root_.IsUniversallyPureOfWeight q w z ↔
      ∀ y ∈ (f.map (algebraMap ℚ ℂ)).roots, ‖y‖ = (q : ℝ) ^ (-(w : ℝ) / 2) := by
  classical
  have hirr : Irreducible f := irreducible_of_normalized_factor f hf
  have hmonic : f.Monic := by
    have h := normalize_normalized_factor f hf
    rw [← h]
    exact monic_normalize hirr.ne_zero
  have hfz : (aeval z) f = 0 := by
    have h1 : (f.map (algebraMap ℚ ℂ)).IsRoot z := (mem_roots'.1 hz).2
    simpa [IsRoot, eval_map_algebraMap] using h1
  have hmin : f = minpoly ℚ z := minpoly.eq_of_irreducible_of_monic hirr hfz hmonic
  constructor
  · rintro ⟨-, h⟩ y hy
    exact h y (by rw [← hmin]; exact hy)
  · intro h
    exact ⟨⟨f, hirr.ne_zero, hfz⟩, by rw [← hmin]; exact h⟩

open scoped Classical in
/-- **The weight stratum.** The complex roots of the weight-`w` factor of `R` are exactly the
complex roots of `R` that are universally pure of weight `w`. -/
theorem roots_map_weightFactor (hR : R.coeff 0 = 1) :
    ((R.weightFactor q w).map (algebraMap ℚ ℂ)).roots =
      (R.map (algebraMap ℚ ℂ)).roots.filter (_root_.IsUniversallyPureOfWeight q w) := by
  have hs : ∀ f ∈ normalizedFactors R, f.coeff 0 ≠ 0 := fun f hf =>
    coeff_zero_ne_zero_of_mem_normalizedFactors hR hf
  have hpure : ∀ z ∈ ((R.weightFactor q w).map (algebraMap ℚ ℂ)).roots,
      _root_.IsUniversallyPureOfWeight q w z := by
    intro z hz
    rw [weightFactor, roots_map_prod_map_normalize
      (fun f hf => hs f (Multiset.mem_of_mem_filter hf))] at hz
    obtain ⟨f, hf, hzf⟩ := Multiset.mem_bind.1 hz
    rw [Multiset.mem_filter] at hf
    exact (isUniversallyPureOfWeight_iff_of_mem_normalizedFactors hf.1 hzf).2 hf.2
  have hnpure : ∀ z ∈ ((R.coweightFactor q w).map (algebraMap ℚ ℂ)).roots,
      ¬ _root_.IsUniversallyPureOfWeight q w z := by
    intro z hz
    rw [coweightFactor, roots_map_prod_map_normalize
      (fun f hf => hs f (Multiset.mem_of_mem_filter hf))] at hz
    obtain ⟨f, hf, hzf⟩ := Multiset.mem_bind.1 hz
    rw [Multiset.mem_filter] at hf
    exact fun hcon =>
      hf.2 ((isUniversallyPureOfWeight_iff_of_mem_normalizedFactors hf.1 hzf).1 hcon)
  have hR0 : R ≠ 0 := fun h => by rw [h] at hR; simp at hR
  have hne : (R.weightFactor q w).map (algebraMap ℚ ℂ) *
      (R.coweightFactor q w).map (algebraMap ℚ ℂ) ≠ 0 := by
    rw [← Polynomial.map_mul, weightFactor_mul_coweightFactor hR]
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).2 hR0
  have hmap : R.map (algebraMap ℚ ℂ) = (R.weightFactor q w).map (algebraMap ℚ ℂ) *
      (R.coweightFactor q w).map (algebraMap ℚ ℂ) := by
    rw [← Polynomial.map_mul, weightFactor_mul_coweightFactor hR]
  have hroots : (R.map (algebraMap ℚ ℂ)).roots =
      ((R.weightFactor q w).map (algebraMap ℚ ℂ)).roots +
        ((R.coweightFactor q w).map (algebraMap ℚ ℂ)).roots := by
    rw [hmap, roots_mul hne]
  rw [hroots, Multiset.filter_add, Multiset.filter_eq_self.2 hpure,
    Multiset.filter_eq_nil.2 hnpure, add_zero]

/-- **Uniqueness of the weight stratum.** If a normalized rational polynomial `R` factors over
`ℂ` into two normalized factors, the first with all roots universally pure of weight `w` and the
second with no such root, then the first factor is the image of `R.weightFactor q w`. -/
theorem eq_map_weightFactor_of_isUniversallyPure (hR : R.coeff 0 = 1) (S T : ℂ[X])
    (hS : S.coeff 0 = 1) (hT : T.coeff 0 = 1) (hST : S * T = R.map (algebraMap ℚ ℂ))
    (hSpure : ∀ z ∈ S.roots, _root_.IsUniversallyPureOfWeight q w z)
    (hTpure : ∀ z ∈ T.roots, ¬ _root_.IsUniversallyPureOfWeight q w z) :
    S = (R.weightFactor q w).map (algebraMap ℚ ℂ) := by
  classical
  have hS0 : S ≠ 0 := fun h => by rw [h] at hS; simp at hS
  have hT0 : T ≠ 0 := fun h => by rw [h] at hT; simp at hT
  have hroots : S.roots = ((R.weightFactor q w).map (algebraMap ℚ ℂ)).roots := by
    rw [roots_map_weightFactor hR, ← hST, roots_mul (mul_ne_zero hS0 hT0), Multiset.filter_add,
      Multiset.filter_eq_self.2 hSpure, Multiset.filter_eq_nil.2 hTpure, add_zero]
  refine eq_of_coeff_zero_eq_one_of_roots_eq hS ?_ hroots
  rw [coeff_map, coeff_zero_weightFactor hR, map_one]

end Polynomial
