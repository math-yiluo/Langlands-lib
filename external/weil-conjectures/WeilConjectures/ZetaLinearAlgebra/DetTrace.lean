/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.PowerSeries.Exp
public import WeilConjectures.EulerProductAux
public import WeilConjectures.Mathlib.Algebra.Polynomial.Splits
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Derivative
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Log

/-!
# The determinant-trace identity

Let `K` be a field, `V` a finite dimensional `K`-vector space and `F : V →ₗ[K] V`. The
reciprocal characteristic polynomial `LinearMap.charpolyRev F = det (1 - t F)`, viewed as a
formal power series, satisfies the classical identity

`det (1 - t F)⁻¹ = exp (∑_{n ≥ 1} tr (F ^ n) t ^ n / n)`,

which is the linear algebra input to the cohomological factorisation of a zeta function. This
file proves it in two forms: a logarithmic derivative form, valid over any field, and the
exponential form above, over a field of characteristic zero.

The proof reduces to an algebraically closed field, where `det (1 - t F) = ∏ (1 - λ t)` and
`tr (F ^ n) = ∑ λ ^ n` are both expressed through the multiset of roots of the characteristic
polynomial, so that everything follows from the single factor case
`t * (1 - λ t)' = - (∑_{n ≥ 1} λ ^ n t ^ n) (1 - λ t)`.

It also records the *trace series* of a Frobenius module, the generating series whose
exponential is `det (1 - t F)⁻¹`, and the alternating determinant of a finite graded family
of Frobenius modules, which is the local factor of an Euler product.

## Main definitions

- `LinearMap.traceSeries`: the trace series `∑_{n ≥ 1} tr (F ^ n) t ^ n / n` of an
  endomorphism.
- `LinearMap.alternatingTraceSeries`: the alternating sum of the trace series over a finite
  graded family.
- `LinearMap.alternatingCharpolyRevProd`: the alternating determinant
  `∏_i det (1 - t ^ e F_i ∣ W_i) ^ ((-1) ^ i)` of a finite graded family.

## Main results

- `PowerSeries.X_mul_derivative_coe_of_coeff_zero_eq_one`: the logarithmic derivative of a split
  polynomial `Q` with `Q (0) = 1` is `- ∑_{n ≥ 1} (∑ z⁻ⁿ) tⁿ`, summed over the roots `z` of `Q`.
- `LinearMap.X_mul_derivative_charpolyRev`: the logarithmic derivative form
  `t * (det (1 - t F))' = - (∑_{n ≥ 1} tr (F ^ n) t ^ n) * det (1 - t F)`, together with its
  matrix counterpart `Matrix.X_mul_derivative_charpolyRev`.
- `LinearMap.inv_charpolyRev_eq_exp`: the exponential form
  `det (1 - t F)⁻¹ = exp (∑_{n ≥ 1} tr (F ^ n) t ^ n / n)`, over a field of characteristic
  zero. It is stated in the same shape as
  `AlgebraicGeometry.Scheme.Hom.zetaSeries`, so that the two can be compared directly.
- `LinearMap.coeff_alternatingTraceSeries`: the coefficients
  `(∑_i (-1) ^ i tr (F i ^ n)) / n` of the alternating trace series.
- `LinearMap.logOf_charpolyRev`: the logarithmic form
  `log det (1 - t F) = - ∑_{n ≥ 1} tr (F ^ n) t ^ n / n`, over a field of characteristic zero.
-/

@[expose] public section

open PowerSeries

namespace PowerSeries

variable {K : Type*} [Field K]

/-- The geometric series `∑_{n ≥ 1} λ ^ n t ^ n` times `1 - λ t` is `λ t`. -/
private theorem mk_pow_mul_one_sub (l : K) :
    (mk fun n ↦ if n = 0 then 0 else l ^ n) * (1 - C l * X) = C l * X := by
  have key : ∀ f : K⟦X⟧, f * (1 - C l * X) = f - C l * (X * f) := by
    intro f; ring
  rw [key]
  ext n
  match n with
  | 0 => simp
  | (m + 1) =>
    rw [map_sub, coeff_mk, coeff_C_mul, coeff_succ_X_mul, coeff_mk, coeff_C_mul,
      ite_eq_right (Nat.succ_ne_zero m)]
    match m with
    | 0 => simp
    | (k + 1) =>
      rw [ite_eq_right (Nat.succ_ne_zero k)]
      simp [pow_succ, coeff_X, mul_comm]

private theorem derivative_one_sub_C_mul_X (l : K) :
    derivative (R := K) (1 - C l * X : K⟦X⟧) = -C l := by
  rw [map_sub, Derivation.map_one_eq_zero, Derivation.leibniz, derivative_X, derivative_C,
    smul_zero, add_zero, smul_eq_mul, mul_one, zero_sub]

/-- The logarithmic derivative of a finite product `∏ (1 - λ t)` is
`- ∑_{n ≥ 1} (∑ λ ^ n) t ^ n`. -/
private theorem X_mul_derivative_multiset_prod (s : Multiset K) :
    X * derivative (R := K) (s.map fun l ↦ (1 - C l * X : K⟦X⟧)).prod =
      (-mk fun n ↦ if n = 0 then 0 else (s.map (· ^ n)).sum) *
        (s.map fun l ↦ (1 - C l * X : K⟦X⟧)).prod := by
  induction s using Multiset.induction with
  | empty =>
    have hz : (mk fun _ : ℕ ↦ (0 : K)) = 0 := by ext; simp
    simp [hz]
  | cons a s ih =>
    have hsplit : (mk fun n ↦ if n = 0 then 0 else ((a ::ₘ s).map (· ^ n)).sum) =
        (mk fun n ↦ if n = 0 then 0 else a ^ n) +
          (mk fun n ↦ if n = 0 then 0 else (s.map (· ^ n)).sum) := by
      ext n
      simp only [coeff_mk, map_add, Multiset.map_cons, Multiset.sum_cons]
      split <;> simp
    have h4 : X * derivative (R := K) (1 - C a * X : K⟦X⟧) =
        (-mk fun n ↦ if n = 0 then 0 else a ^ n) * (1 - C a * X) := by
      rw [neg_mul, mk_pow_mul_one_sub, derivative_one_sub_C_mul_X]
      ring
    rw [hsplit, Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
    linear_combination (1 - C a * X : K⟦X⟧) * ih +
      (s.map fun l ↦ (1 - C l * X : K⟦X⟧)).prod * h4

/-- The image in `K⟦X⟧` of a product of polynomials `1 - λ t`. -/
private theorem coe_multiset_prod_one_sub (s : Multiset K) :
    (((s.map fun l ↦ (1 - Polynomial.C l * Polynomial.X)).prod : Polynomial K) : K⟦X⟧) =
      (s.map fun l ↦ (1 - C l * X : K⟦X⟧)).prod := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
  simp

/-- The logarithmic derivative of a split polynomial `Q` with `Q (0) = 1` is minus the generating
series of the power sums of its reciprocal roots:
`t * Q' = - (∑_{n ≥ 1} (∑_z z⁻ⁿ) tⁿ) * Q`, the inner sum running over the roots `z` of `Q`. -/
theorem X_mul_derivative_coe_of_coeff_zero_eq_one {Q : Polynomial K} (hQ : Q.Splits)
    (h0 : Q.coeff 0 = 1) :
    X * derivative (R := K) (Q : K⟦X⟧) =
      (-mk fun n ↦ if n = 0 then 0 else (Q.roots.map fun z ↦ z⁻¹ ^ n).sum) * (Q : K⟦X⟧) := by
  have h : (Q : K⟦X⟧) = ((Q.roots.map (·⁻¹)).map fun l ↦ (1 - C l * X : K⟦X⟧)).prod := by
    conv_lhs => rw [Polynomial.eq_prod_one_sub_inv_roots hQ h0]
    rw [← coe_multiset_prod_one_sub, Multiset.map_map]
    rfl
  have hs : ∀ n, (Q.roots.map fun z ↦ z⁻¹ ^ n) = (Q.roots.map (·⁻¹)).map (· ^ n) := fun n ↦ by
    rw [Multiset.map_map]
    rfl
  simp only [hs]
  rw [h]
  exact X_mul_derivative_multiset_prod _

end PowerSeries

namespace Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem X_mul_derivative_charpolyRev_of_isAlgClosed [IsAlgClosed K] (A : Matrix ι ι K) :
    X * derivative (R := K) (A.charpolyRev : K⟦X⟧) =
      (-mk fun n ↦ if n = 0 then 0 else (A ^ n).trace) * (A.charpolyRev : K⟦X⟧) := by
  simp only [Matrix.trace_pow_eq_sum_pow_roots_charpoly]
  rw [Matrix.charpolyRev_eq_prod_one_sub_smul, coe_multiset_prod_one_sub]
  exact X_mul_derivative_multiset_prod _

/-- The logarithmic derivative of the reciprocal characteristic polynomial `det (1 - t A)` of a
square matrix is minus the generating series of the traces of the powers of `A`. -/
theorem X_mul_derivative_charpolyRev (A : Matrix ι ι K) :
    X * derivative (R := K) (A.charpolyRev : K⟦X⟧) =
      (-mk fun n ↦ if n = 0 then 0 else (A ^ n).trace) * (A.charpolyRev : K⟦X⟧) := by
  set φ := algebraMap K (AlgebraicClosure K)
  have hinj : Function.Injective φ := (algebraMap K (AlgebraicClosure K)).injective
  apply PowerSeries.map_injective φ hinj
  have hcp : Polynomial.map φ A.charpolyRev = (A.map φ).charpolyRev := by
    rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, Matrix.charpoly_map,
      Polynomial.reverse_map hinj]
  have htr : PowerSeries.map φ (mk fun n ↦ if n = 0 then 0 else (A ^ n).trace)
      = mk fun n ↦ if n = 0 then 0 else ((A.map φ) ^ n).trace := by
    ext n
    rw [coeff_map, coeff_mk, coeff_mk]
    split
    · exact map_zero φ
    · rw [AddMonoidHom.map_trace, Matrix.map_pow]
  rw [map_mul, map_X, map_derivative, map_mul, map_neg, htr, ← Polynomial.polynomial_map_coe,
    hcp]
  exact X_mul_derivative_charpolyRev_of_isAlgClosed _

end Matrix

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The determinant-trace identity**, in logarithmic derivative form: the logarithmic
derivative of the reciprocal characteristic polynomial `det (1 - t F)` of an endomorphism `F`
of a finite dimensional vector space is minus the generating series of the traces of the
powers of `F`, i.e. `t * (det (1 - t F))' = - (∑_{n ≥ 1} tr (F ^ n) t ^ n) * det (1 - t F)`. -/
theorem X_mul_derivative_charpolyRev (F : Module.End K V) :
    X * derivative (R := K) (F.charpolyRev : K⟦X⟧) =
      (-PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (F ^ n)) *
        (F.charpolyRev : K⟦X⟧) := by
  classical
  set b := Module.finBasis K V
  have htr : ∀ n : ℕ, LinearMap.trace K V (F ^ n) = ((toMatrix b b F) ^ n).trace := by
    intro n
    rw [LinearMap.toMatrix_pow, LinearMap.trace_eq_matrix_trace K b]
  simp only [htr]
  rw [← LinearMap.charpolyRev_toMatrix b F]
  exact Matrix.X_mul_derivative_charpolyRev _

/-- **The determinant-trace identity**, exponential form:
`det (1 - t F)⁻¹ = exp (∑_{n ≥ 1} tr (F ^ n) t ^ n / n)` for an endomorphism `F` of a finite
dimensional vector space over a field of characteristic zero
(blueprint: `lemma-logarithm-determinant`, `lemma-logarithm-determinant--1`). -/
theorem inv_charpolyRev_eq_exp [CharZero K] (F : Module.End K V) :
    (F.charpolyRev : K⟦X⟧)⁻¹ =
      (PowerSeries.exp K).subst
        (PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (F ^ n) / n) := by
  have hlogP := X_mul_derivative_charpolyRev F
  set P : K⟦X⟧ := (F.charpolyRev : K⟦X⟧) with hP
  set T : K⟦X⟧ := PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (F ^ n)
    with hT
  set g : K⟦X⟧ := PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (F ^ n) / n
    with hg
  have hsubst : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hg])
  have hP1 : PowerSeries.constantCoeff P = 1 := by
    rw [hP, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, eval_charpolyRev]
  have hmul : P * P⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hP1]; exact one_ne_zero)
  have hlogPinv : X * derivative (R := K) P⁻¹ = T * P⁻¹ := by
    rw [PowerSeries.derivative_inv']
    linear_combination (-(P⁻¹ ^ 2)) * hlogP + (T * P⁻¹) * hmul
  have hXg : X * derivative (R := K) g = T := by
    ext n
    match n with
    | 0 => simp [hg, hT]
    | m + 1 =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, hg, hT,
        PowerSeries.coeff_mk, PowerSeries.coeff_mk, ite_eq_right m.succ_ne_zero,
        ite_eq_right m.succ_ne_zero]
      have hm : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      push_cast
      rw [div_mul_cancel₀ _ hm]
  have hlogE : X * derivative (R := K) ((PowerSeries.exp K).subst g) =
      T * (PowerSeries.exp K).subst g := by
    rw [PowerSeries.derivative_subst hsubst, PowerSeries.derivative_exp,
      mul_comm (PowerSeries.subst g (PowerSeries.exp K)), ← mul_assoc, hXg]
  have hEconst : PowerSeries.constantCoeff ((PowerSeries.exp K).subst g) = 1 := by
    have h0 : PowerSeries.coeff 0 ((PowerSeries.exp K).subst g) = 1 := by
      rw [PowerSeries.coeff_subst' (hb := hsubst), finsum_eq_single _ 0
        fun d hd ↦ by simp [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, zero_pow hd, hg]]
      simp [PowerSeries.coeff_exp]
    simpa using h0
  have hconst : PowerSeries.constantCoeff P⁻¹ =
      PowerSeries.constantCoeff ((PowerSeries.exp K).subst g) := by
    rw [PowerSeries.constantCoeff_inv, hP1, hEconst, inv_one]
  have hT0 : PowerSeries.constantCoeff T = 0 := by rw [hT]; simp
  ext n
  exact PowerSeries.coeff_eq_of_X_mul_derivative_eq hlogPinv hlogE hconst hT0
    (m := n) (fun i _ ↦ rfl) n le_rfl

/-- The *trace series*

`tr_F(T) = ∑_{n ≥ 1} tr (F ^ n ∣ V) T ^ n / n`

of an endomorphism `F` of a finite dimensional vector space. Its companion identity
`exp (tr_F(T)) = det (1 - T F)⁻¹` is `LinearMap.inv_charpolyRev_eq_exp`, proved above
(blueprint: `lemma-logarithm-determinant`). -/
noncomputable def traceSeries (F : Module.End K V) : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (F ^ n) / n

omit [FiniteDimensional K V] in
/-- The `n`-th coefficient of the trace series is `tr (F ^ n) / n`, and `0` for `n = 0`. -/
theorem coeff_traceSeries (F : Module.End K V) (n : ℕ) :
    PowerSeries.coeff n (traceSeries F) =
      if n = 0 then 0 else LinearMap.trace K V (F ^ n) / n := by
  rw [traceSeries, PowerSeries.coeff_mk]

omit [FiniteDimensional K V] in
/-- The trace series has no constant term: it lies in `T K⟦T⟧` (blueprint:
`theorem-weil-conjectures-smooth-proper-schemes--7`). -/
@[simp]
theorem constantCoeff_traceSeries (F : Module.End K V) :
    PowerSeries.constantCoeff (traceSeries F) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_traceSeries, ite_eq_left rfl]

/-- **The determinant-trace identity**, logarithmic form: the formal logarithm of
`det (1 - t F)` is minus the trace series,
`log det (1 - t F) = - ∑_{n ≥ 1} tr (F ^ n) t ^ n / n`, for an endomorphism `F` of a finite
dimensional vector space over a field of characteristic zero. No semisimplicity is assumed
(blueprint: `lemma-logarithm-determinant--1`, `lemma-logarithm-determinant`). -/
theorem logOf_charpolyRev [CharZero K] (F : Module.End K V) :
    PowerSeries.logOf (F.charpolyRev : K⟦X⟧) = -traceSeries F := by
  set P : K⟦X⟧ := (F.charpolyRev : K⟦X⟧) with hP
  set T : K⟦X⟧ := PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (F ^ n)
    with hT
  have hP1 : PowerSeries.constantCoeff P = 1 := by
    rw [hP, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, eval_charpolyRev]
  have hP0 : P ≠ 0 := fun h ↦ by simp [h] at hP1
  have hlogP : X * derivative (R := K) P = -T * P := X_mul_derivative_charpolyRev F
  have hXg : X * derivative (R := K) (traceSeries F) = T := by
    ext n
    match n with
    | 0 => simp [hT]
    | m + 1 =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, traceSeries, hT,
        PowerSeries.coeff_mk, PowerSeries.coeff_mk, ite_eq_right m.succ_ne_zero,
        ite_eq_right m.succ_ne_zero]
      have hm : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      push_cast
      rw [div_mul_cancel₀ _ hm]
  refine PowerSeries.derivative.ext ?_ ?_
  · refine mul_left_cancel₀ (mul_ne_zero hP0 PowerSeries.X_ne_zero) ?_
    rw [map_neg]
    linear_combination X * PowerSeries.mul_derivative_logOf hP1 + hlogP + P * hXg
  · rw [PowerSeries.constantCoeff_logOf hP1, map_neg, traceSeries]
    simp

variable {W : ℤ → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  [∀ i, FiniteDimensional K (W i)]

/-- The alternating trace series

`str_F(T) = ∑_{n ≥ 1} (∑_i (-1) ^ i tr (F i ^ n ∣ W i)) T ^ n / n`

of a finite graded family `(W i, F i)` of Frobenius modules, indexed by a finite set `s` of
integers: the alternating sum of the individual trace series `LinearMap.traceSeries (F i)`,
the sign being the parity of the degree `i` via `Int.negOnePow`
(blueprint: `lemma-logarithm-determinant`). -/
noncomputable def alternatingTraceSeries (s : Finset ℤ) (F : ∀ i, Module.End K (W i)) : K⟦X⟧ :=
  ∑ i ∈ s, (i.negOnePow : ℤ) • traceSeries (F i)

omit [∀ i, FiniteDimensional K (W i)] in
/-- The `n`-th coefficient of the alternating trace series is
`(∑_i (-1) ^ i tr (F i ^ n ∣ W i)) / n`, and `0` for `n = 0`: the two descriptions
`∑_{n ≥ 1} (∑_i (-1) ^ i tr (F i ^ n)) T ^ n / n = ∑_i (-1) ^ i tr_{F i}(T)` of the
alternating trace series agree (blueprint: `theorem-weil-conjectures-smooth-proper-schemes--7`). -/
theorem coeff_alternatingTraceSeries (s : Finset ℤ) (F : ∀ i, Module.End K (W i)) (n : ℕ) :
    PowerSeries.coeff n (alternatingTraceSeries s F) =
      if n = 0 then 0
      else (∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace K (W i) (F i ^ n)) / n := by
  rw [alternatingTraceSeries, map_sum]
  split_ifs with hn
  · simp [hn]
  · rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PowerSeries.coeff_smul, coeff_traceSeries, ite_eq_right hn, zsmul_eq_mul, zsmul_eq_mul,
      div_eq_mul_inv, mul_assoc]

omit [∀ i, FiniteDimensional K (W i)] in
/-- The alternating trace series has no constant term: it lies in `T K⟦T⟧` (blueprint:
`theorem-weil-conjectures-smooth-proper-schemes--7`). -/
@[simp]
theorem constantCoeff_alternatingTraceSeries (s : Finset ℤ) (F : ∀ i, Module.End K (W i)) :
    PowerSeries.constantCoeff (alternatingTraceSeries s F) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_alternatingTraceSeries,
    ite_eq_left rfl]

/-- The alternating determinant

`∏_i det (1 - T ^ e F i ∣ W i) ^ ((-1) ^ i)`

of a finite graded family `(W i, F i)` of Frobenius modules, indexed by a finite set `s` of
integers. For `e = 1` and `W i = H_c^i` this is the cohomological side of an Euler product,
and for `e` the degree of a closed point and `W i` the cohomology of a stalk its inverse is
the local factor at that point. -/
noncomputable def alternatingCharpolyRevProd (s : Finset ℤ) (F : ∀ i, Module.End K (W i))
    (e : ℕ) : K⟦X⟧ :=
  ∏ i ∈ s, if Even i then ((F i).charpolyRev.comp (Polynomial.X ^ e) : K⟦X⟧)
    else ((F i).charpolyRev.comp (Polynomial.X ^ e) : K⟦X⟧)⁻¹

end LinearMap
