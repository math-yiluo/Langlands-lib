/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.ZetaLinearAlgebra.NormalizedGauss
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Purity of a polynomial, and disjointness of distinct weights

Fix a prime power `q`. A polynomial `P ∈ ℂ[X]` with constant coefficient `1` is *pure of weight
`w`* if every complex root `z` of `P` satisfies `‖z‖ = q ^ (-w / 2)`, i.e. every reciprocal root
of `P` has absolute value `q ^ (w / 2)`. This is the shape in which the Riemann hypothesis part
of the Weil conjectures is stated in `AlgebraicGeometry.WeilRiemannHypothesis`.

The `≤` half of purity is the *mixedness* condition `Polynomial.IsMixedOfWeightLE`, which is
what Deligne's weight estimate provides before Poincaré duality is used; the weight index is
`w : ℕ` throughout, matching `Polynomial.IsPureOfWeight`.

A strictly stronger notion is needed downstream: a scalar `z` is *universally pure of weight `w`*
if it is algebraic over `ℚ` and *every* conjugate of `z` — every complex root of its minimal
polynomial over `ℚ` — has absolute value `q ^ (-w / 2)`; a polynomial is universally pure of
weight `w` if all of its roots are. Universal purity is a condition on the minimal polynomial
alone, so unlike purity it does not depend on the choice of a complex embedding.

## Main results

- `Polynomial.IsPureOfWeight`, `Polynomial.IsMixedOfWeightLE`, `IsUniversallyPureOfWeight`,
  `Polynomial.IsUniversallyPureOfWeight` — the purity and mixedness notions, for a polynomial
  and for a scalar.
- `Polynomial.IsPureOfWeight.isMixedOfWeightLE`, `Polynomial.isPureOfWeight_iff` — purity is
  mixedness of weight at most `w` together with the matching upper bound on the root norms.
- `Polynomial.IsUniversallyPureOfWeight.isPureOfWeight` — universal purity implies purity.
- `Polynomial.IsPureOfWeight.disjoint_roots` — polynomials pure of distinct weights have no
  common root.
- `IsUniversallyPureOfWeight.weight_unique` — a scalar is universally pure of at most one weight.
- `Polynomial.isCoprime_prod_odd_prod_even` — for a family `P i` with `P i` pure of weight `i`,
  the product of the odd-indexed factors and the product of the even-indexed factors are coprime.
- `Polynomial.prod_odd_eq_map_and_prod_even_eq_map` — identification of the two parity factors:
  if the parity products cross-multiply against a coprime normalized rational fraction `A / B`,
  then the odd product is `A` and the even product is `B`.
- `Polynomial.isAlgebraic_of_mem_roots_of_prod_mul_eq` — in that situation every root of every
  `P i` is algebraic over `ℚ`.
- `Polynomial.eq_of_isPureOfWeight_of_prod_mul_eq` — **weight separation determines the
  factors**: two families of pure polynomials of weights `0, 1, …, r` with the same alternating
  product are equal.
-/

@[expose] public section

open scoped Polynomial

/-- `P` is pure of weight `w` for `q` if `P (0) = 1` and every complex root `z` of `P`
satisfies `‖z‖ = q ^ (-w / 2)`; equivalently every reciprocal root has absolute value
`q ^ (w / 2)` (blueprint `definition-reciprocal-root`). -/
def Polynomial.IsPureOfWeight (q w : ℕ) (P : Polynomial ℂ) : Prop :=
  P.coeff 0 = 1 ∧ ∀ z ∈ P.roots, ‖z‖ = (q : ℝ) ^ (-(w : ℝ) / 2)

/-- `P` is *mixed of weight at most `w`* for `q` if `P (0) = 1` and every complex root `z` of
`P` satisfies `q ^ (-w / 2) ≤ ‖z‖`; equivalently every reciprocal root of `P` has absolute
value at most `q ^ (w / 2)`. This is the `≤` half of `Polynomial.IsPureOfWeight` and the
conclusion of Deligne's weight estimate. -/
def Polynomial.IsMixedOfWeightLE (q w : ℕ) (P : Polynomial ℂ) : Prop :=
  P.coeff 0 = 1 ∧ ∀ z ∈ P.roots, (q : ℝ) ^ (-(w : ℝ) / 2) ≤ ‖z‖

/-- `z : ℂ` is *universally* pure of weight `w`: it is algebraic over `ℚ` and every
conjugate of `z` — every complex root of its minimal polynomial over `ℚ` — has absolute
value `q ^ (-w/2)`. This is strictly stronger than purity under one embedding (blueprint
`definition-reciprocal-root`). -/
def IsUniversallyPureOfWeight (q w : ℕ) (z : ℂ) : Prop :=
  IsAlgebraic ℚ z ∧ ∀ y ∈ ((minpoly ℚ z).map (algebraMap ℚ ℂ)).roots,
    ‖y‖ = (q : ℝ) ^ (-(w : ℝ) / 2)

/-- Every reciprocal root of `P` is universally pure of weight `w` (blueprint
`definition-reciprocal-root`). -/
def Polynomial.IsUniversallyPureOfWeight (q w : ℕ) (P : Polynomial ℂ) : Prop :=
  P.coeff 0 = 1 ∧ ∀ z ∈ P.roots, _root_.IsUniversallyPureOfWeight q w z

/-- Two weights giving the same absolute value are equal: `q ^ (-v / 2) = q ^ (-w / 2)` forces
`v = w` when `1 < q`. -/
private theorem weight_eq_of_norm_eq {q v w : ℕ} (hq : 1 < q) {z : ℂ}
    (hv : ‖z‖ = (q : ℝ) ^ (-(v : ℝ) / 2)) (hw : ‖z‖ = (q : ℝ) ^ (-(w : ℝ) / 2)) : v = w := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hq1 : (q : ℝ) ≠ 1 := by exact_mod_cast hq.ne'
  have h : -(v : ℝ) / 2 = -(w : ℝ) / 2 := (Real.rpow_right_inj hq0 hq1).1 (hv ▸ hw)
  have : (v : ℝ) = w := by linarith
  exact_mod_cast this

/-- A complex number algebraic over `ℚ` is a root of (the complex image of) its own minimal
polynomial, hence one of its own conjugates. -/
private theorem mem_roots_map_minpoly {z : ℂ} (hz : IsAlgebraic ℚ z) :
    z ∈ ((minpoly ℚ z).map (algebraMap ℚ ℂ)).roots := by
  have hne : (minpoly ℚ z).map (algebraMap ℚ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).2 (minpoly.ne_zero hz.isIntegral)
  rw [Polynomial.mem_roots hne]
  simp [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]

namespace Polynomial

/-- Universal purity of weight `w` implies purity of weight `w`. -/
theorem IsUniversallyPureOfWeight.isPureOfWeight {q w : ℕ} {P : Polynomial ℂ}
    (hP : P.IsUniversallyPureOfWeight q w) : P.IsPureOfWeight q w := by
  refine ⟨hP.1, fun z hz ↦ ?_⟩
  obtain ⟨halg, hy⟩ := hP.2 z hz
  exact hy z (mem_roots_map_minpoly halg)

/-- A polynomial that is pure of some weight is nonzero: its constant coefficient is `1`. -/
theorem IsPureOfWeight.ne_zero {q w : ℕ} {P : Polynomial ℂ} (hP : P.IsPureOfWeight q w) :
    P ≠ 0 := by
  rintro rfl
  simpa using hP.1

/-- A polynomial that is mixed of some weight is nonzero: its constant coefficient is `1`. -/
theorem IsMixedOfWeightLE.ne_zero {q w : ℕ} {P : Polynomial ℂ} (hP : P.IsMixedOfWeightLE q w) :
    P ≠ 0 := by
  rintro rfl
  simpa using hP.1

/-- Purity of weight `w` implies mixedness of weight at most `w`. -/
theorem IsPureOfWeight.isMixedOfWeightLE {q w : ℕ} {P : Polynomial ℂ}
    (hP : P.IsPureOfWeight q w) : P.IsMixedOfWeightLE q w :=
  ⟨hP.1, fun z hz ↦ (hP.2 z hz).ge⟩

/-- Purity of weight `w` is mixedness of weight at most `w` together with the matching upper
bound on the norms of the roots. -/
theorem isPureOfWeight_iff {q w : ℕ} {P : Polynomial ℂ} :
    P.IsPureOfWeight q w ↔
      P.IsMixedOfWeightLE q w ∧ ∀ z ∈ P.roots, ‖z‖ ≤ (q : ℝ) ^ (-(w : ℝ) / 2) := by
  refine ⟨fun h ↦ ⟨h.isMixedOfWeightLE, fun z hz ↦ (h.2 z hz).le⟩, ?_⟩
  rintro ⟨⟨h0, hge⟩, hle⟩
  exact ⟨h0, fun z hz ↦ le_antisymm (hle z hz) (hge z hz)⟩

/-- Polynomials that are pure of distinct weights have no common root. -/
theorem IsPureOfWeight.disjoint_roots {q v w : ℕ} (hq : 1 < q) {P Q : Polynomial ℂ}
    (hP : P.IsPureOfWeight q v) (hQ : Q.IsPureOfWeight q w) (hvw : v ≠ w) :
    ∀ z ∈ P.roots, z ∉ Q.roots :=
  fun z hzP hzQ ↦ hvw (weight_eq_of_norm_eq hq (hP.2 z hzP) (hQ.2 z hzQ))

/-- Polynomials that are pure of distinct weights are coprime: over `ℂ` coprimality of the
two nonzero polynomials is exactly the absence of a common root. -/
theorem IsPureOfWeight.isCoprime {q v w : ℕ} (hq : 1 < q) {P Q : Polynomial ℂ}
    (hP : P.IsPureOfWeight q v) (hQ : Q.IsPureOfWeight q w) (hvw : v ≠ w) : IsCoprime P Q := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K := ℂ) (p := P) (q := Q)]
  intro a
  by_contra hcon
  simp only [not_or, not_not] at hcon
  exact hP.disjoint_roots hq hQ hvw a ((mem_roots hP.ne_zero).2 (by simpa using hcon.1))
    ((mem_roots hQ.ne_zero).2 (by simpa using hcon.2))

/-- The constant coefficient of a product of polynomials that are pure of some weight is `1`. -/
theorem coeff_zero_prod_eq_one {ι : Type*} {q : ℕ} {w : ι → ℕ} {P : ι → Polynomial ℂ}
    {s : Finset ι} (hP : ∀ i ∈ s, (P i).IsPureOfWeight q (w i)) :
    (∏ i ∈ s, P i).coeff 0 = 1 := by
  rw [coeff_zero_prod]
  exact Finset.prod_eq_one fun i hi ↦ (hP i hi).1

/-- For a family `P i` with `P i` pure of weight `i`, the product of the odd-indexed factors and
the product of the even-indexed factors are coprime. -/
theorem isCoprime_prod_odd_prod_even {q r : ℕ} (hq : 1 < q) {P : Fin (r + 1) → Polynomial ℂ}
    (hP : ∀ i, (P i).IsPureOfWeight q i.1) :
    IsCoprime (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P i)
      (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P i) := by
  refine IsCoprime.prod_left fun i hi ↦ IsCoprime.prod_right fun j hj ↦ ?_
  simp only [Finset.mem_filter] at hi hj
  exact (hP i).isCoprime hq (hP j) fun h ↦ (Nat.not_odd_iff_even.2 hj.2) (h ▸ hi.2)

/-- The product of the odd-indexed factors has constant coefficient `1`. -/
theorem coeff_zero_prod_odd_eq_one {q r : ℕ} {P : Fin (r + 1) → Polynomial ℂ}
    (hP : ∀ i, (P i).IsPureOfWeight q i.1) :
    (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P i).coeff 0 = 1 :=
  coeff_zero_prod_eq_one fun i _ ↦ hP i

/-- The product of the even-indexed factors has constant coefficient `1`. -/
theorem coeff_zero_prod_even_eq_one {q r : ℕ} {P : Fin (r + 1) → Polynomial ℂ}
    (hP : ∀ i, (P i).IsPureOfWeight q i.1) :
    (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P i).coeff 0 = 1 :=
  coeff_zero_prod_eq_one fun i _ ↦ hP i

/-- **Identification of the two parity factors**. If the parity products of a family of pure
polynomials of distinct weights cross-multiply against a coprime normalized rational fraction
`A / B`, then the odd-indexed product is `A` and the even-indexed product is `B`: no reciprocal
root cancels between odd and even indices. -/
theorem prod_odd_eq_map_and_prod_even_eq_map {q r : ℕ} (hq : 1 < q) {P : Fin (r + 1) → ℂ[X]}
    (hP : ∀ i, (P i).IsPureOfWeight q i.1) {A B : ℚ[X]} (hAB : IsCoprime A B)
    (hA : A.coeff 0 = 1)
    (h : (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P i) *
        B.map (algebraMap ℚ ℂ) =
      (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P i) * A.map (algebraMap ℚ ℂ)) :
    (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P i) = A.map (algebraMap ℚ ℂ) ∧
      (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P i) = B.map (algebraMap ℚ ℂ) :=
  eq_of_coeff_zero_eq_one_of_isCoprime (by rw [coeff_map, hA, map_one])
    (coeff_zero_prod_odd_eq_one hP) ((isCoprime_map _).2 hAB)
    (isCoprime_prod_odd_prod_even hq hP) h

/-- **Algebraicity of every reciprocal root**: under the hypotheses identifying the two parity
factors, every root of every `P i` is a root of the complex image of `A` or of `B`, hence is
algebraic over `ℚ`. -/
theorem isAlgebraic_of_mem_roots_of_prod_mul_eq {q r : ℕ} (hq : 1 < q) {P : Fin (r + 1) → ℂ[X]}
    (hP : ∀ i, (P i).IsPureOfWeight q i.1) {A B : ℚ[X]} (hAB : IsCoprime A B)
    (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (h : (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P i) *
        B.map (algebraMap ℚ ℂ) =
      (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P i) * A.map (algebraMap ℚ ℂ))
    {i : Fin (r + 1)} {z : ℂ} (hz : z ∈ (P i).roots) : IsAlgebraic ℚ z := by
  obtain ⟨hO, hE⟩ := prod_odd_eq_map_and_prod_even_eq_map hq hP hAB hA h
  have hroot : (P i).eval z = 0 := (mem_roots (hP i).ne_zero).1 hz
  have key : ∀ (s : Finset (Fin (r + 1))) (C : ℚ[X]), C.coeff 0 = 1 → i ∈ s →
      (∏ j ∈ s, P j) = C.map (algebraMap ℚ ℂ) → IsAlgebraic ℚ z := by
    intro s C hC his hs
    refine ⟨C, fun h0 ↦ by simp [h0] at hC, ?_⟩
    have hzero : (C.map (algebraMap ℚ ℂ)).eval z = 0 := by
      rw [← hs, eval_prod]
      exact Finset.prod_eq_zero his hroot
    rwa [eval_map_algebraMap] at hzero
  rcases Nat.even_or_odd i.1 with he | ho
  · exact key _ B hB (by simp [he]) hE
  · exact key _ A hA (by simp [ho]) hO

/-- **Weight separation determines the factors.** Two families `P i` and `P' i` of complex
polynomials, each with `P i` and `P' i` pure of weight `i`, that have the same alternating
product — the cross-multiplication `(∏_odd P) (∏_even P') = (∏_odd P') (∏_even P)` — are equal.
Indeed a root of absolute value `q ^ (-i / 2)` can only come from the degree-`i` member of
either family, so the two root multisets in degree `i` agree. -/
theorem eq_of_isPureOfWeight_of_prod_mul_eq {q r : ℕ} (hq : 1 < q) {P P' : Fin (r + 1) → ℂ[X]}
    (hP : ∀ i, (P i).IsPureOfWeight q i.1) (hP' : ∀ i, (P' i).IsPureOfWeight q i.1)
    (h : (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P i) *
        (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P' i) =
      (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P' i) *
        (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P i)) :
    P = P' := by
  classical
  funext j
  set N : ℂ → Prop := fun z ↦ ‖z‖ = (q : ℝ) ^ (-(j.1 : ℝ) / 2) with hN
  have hprod_ne : ∀ (Q : Fin (r + 1) → ℂ[X]), (∀ i, (Q i).IsPureOfWeight q i.1) →
      ∀ s : Finset (Fin (r + 1)), ∏ i ∈ s, Q i ≠ 0 :=
    fun Q hQ s ↦ Finset.prod_ne_zero_iff.2 fun i _ ↦ (hQ i).ne_zero
  have hfilter_sum : ∀ (s : Finset (Fin (r + 1))) (g : Fin (r + 1) → Multiset ℂ),
      Multiset.filter N (∑ i ∈ s, g i) = ∑ i ∈ s, Multiset.filter N (g i) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.filter_add, ih]
  -- filtering the roots of a product of pure factors by the weight-`j` norm keeps exactly the
  -- roots of the degree-`j` factor
  have key : ∀ (Q : Fin (r + 1) → ℂ[X]), (∀ i, (Q i).IsPureOfWeight q i.1) →
      ∀ s : Finset (Fin (r + 1)),
      Multiset.filter N (∏ i ∈ s, Q i).roots = if j ∈ s then (Q j).roots else 0 := by
    intro Q hQ s
    have hbind : (s.val.bind fun i ↦ (Q i).roots) = ∑ i ∈ s, (Q i).roots := rfl
    rw [roots_prod _ _ (hprod_ne Q hQ s), hbind, hfilter_sum]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ s) ↦
      show Multiset.filter N (Q i).roots = if i = j then (Q j).roots else 0 by
        by_cases hij : i = j
        · subst hij
          rw [ite_eq_left rfl, Multiset.filter_eq_self.2 fun z hz ↦ (hQ i).2 z hz]
        · rw [ite_eq_right hij, Multiset.filter_eq_nil.2 fun z hz hcon ↦
            hij (Fin.ext (weight_eq_of_norm_eq hq ((hQ i).2 z hz) hcon))]]
    exact Finset.sum_ite_eq' s j _
  have hroots := congrArg Polynomial.roots h
  rw [roots_mul (mul_ne_zero (hprod_ne P hP _) (hprod_ne P' hP' _)),
    roots_mul (mul_ne_zero (hprod_ne P' hP' _) (hprod_ne P hP _))] at hroots
  have hfil := congrArg (Multiset.filter N) hroots
  rw [Multiset.filter_add, Multiset.filter_add, key P hP, key P' hP', key P' hP', key P hP]
    at hfil
  refine eq_of_coeff_zero_eq_one_of_roots_eq (hP j).1 (hP' j).1 ?_
  rcases Nat.even_or_odd j.1 with he | ho
  · have hoddj : j ∉ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1 := by
      simp [Nat.not_odd_iff_even.2 he]
    have hevenj : j ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1 := by simp [he]
    rw [ite_eq_right hoddj, ite_eq_left hevenj, ite_eq_right hoddj, ite_eq_left hevenj,
      zero_add, zero_add] at hfil
    exact hfil.symm
  · have hoddj : j ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1 := by simp [ho]
    have hevenj : j ∉ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1 := by
      simp [Nat.not_even_iff_odd.2 ho]
    rw [ite_eq_left hoddj, ite_eq_right hevenj, ite_eq_left hoddj, ite_eq_right hevenj,
      add_zero, add_zero] at hfil
    exact hfil


/-- The weight-`i` part of the roots of a product of pure polynomials of pairwise distinct
weights: if `P j` is pure of weight `j` for `j ∈ S` and `i ∈ S`, the roots of `∏_{j ∈ S} P j` of
absolute value `q^{-i/2}` are the roots of `P i`. -/
theorem roots_prod_filter_norm_eq {q : ℕ} (hq : 1 < q) {S : Finset ℕ}
    {P : ℕ → Polynomial ℂ} (hP : ∀ j ∈ S, (P j).IsPureOfWeight q j) {i : ℕ} (hi : i ∈ S) :
    (∏ j ∈ S, P j).roots.filter (fun z ↦ ‖z‖ = (q : ℝ) ^ (-(i : ℝ) / 2)) = (P i).roots := by
  classical
  rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun j hj ↦ (hP j hj).ne_zero),
    Multiset.filter_bind, ← Finset.insert_erase hi, Finset.insert_val_of_notMem
      (Finset.notMem_erase i S), Multiset.cons_bind,
    Multiset.filter_eq_self.2 fun z hz ↦ (hP i hi).2 z hz]
  convert add_zero (P i).roots
  refine Multiset.eq_zero_of_forall_notMem fun z hz ↦ ?_
  obtain ⟨j, hj, hz⟩ := Multiset.mem_bind.1 hz
  obtain ⟨hz, hzi⟩ := Multiset.mem_filter.1 hz
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hzj := (hP j (Finset.mem_of_mem_erase hj)).2 z hz
  exact hji (weight_eq_of_norm_eq hq hzj hzi)

end Polynomial

/-- A complex number is universally pure of at most one weight. (No hypothesis `z ≠ 0` is
needed: `0` is a root of its own minimal polynomial `X` and `‖(0 : ℂ)‖ = 0` is never a power
of `q`, so `0` is universally pure of no weight at all.) -/
theorem IsUniversallyPureOfWeight.weight_unique {q v w : ℕ} (hq : 1 < q) {z : ℂ}
    (hv : IsUniversallyPureOfWeight q v z) (hw : IsUniversallyPureOfWeight q w z) : v = w :=
  weight_eq_of_norm_eq hq (hv.2 z (mem_roots_map_minpoly hv.1))
    (hw.2 z (mem_roots_map_minpoly hv.1))
