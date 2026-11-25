/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

/-!
# Rationality of a power series and the span of the shifts of its coefficients

Let `K` be a field. A power series `f ∈ K⟦X⟧` is *rational* if it admits a *normalized
fraction*, that is a pair of polynomials `A B : K[X]` with `B.coeff 0 = 1` and
`f * B = A` in `K⟦X⟧`. This file proves that this happens exactly when the `K`-span of the
iterated left shifts of the coefficient sequence of `f` is finite-dimensional.

The criterion is the engine of the Hankel descent theorem (rationality descends along a
field extension) and of the integral Fatou theorem; both are developed elsewhere.

## Main definitions

- `seqShift`: the left shift `a ↦ (n ↦ a (n + 1))` on sequences `ℕ → R`, as a linear map.
- `shiftSpan`: the span of the iterated left shifts of a sequence, with `shiftSpan_le` as its
  universal property.

## Main statements

- `PowerSeries.mul_eq_mul_of_mul_coe_eq`: two normalized fractions for the same power
  series cross-multiply, and `PowerSeries.eq_of_mul_eq_mul`: conversely, cross-multiplying
  fractions represent the same power series. Together they say that the Taylor expansion
  map from normalized fractions to power series is faithful.
- `PowerSeries.sum_coeff_mul_coeff_eq_zero`: a normalized fraction `f * B = A` makes the
  coefficient sequence of `f` satisfy the linear recurrence given by `B` in all degrees
  beyond `A.natDegree`.
- `finiteDimensional_shiftSpan_of_recurrence`: a sequence that eventually satisfies a
  linear recurrence has finite-dimensional shift span.
- `PowerSeries.exists_monic_sum_coeff_mul_eq_zero_of_finiteDimensional_shiftSpan`: a sequence
  with finite-dimensional shift span satisfies the linear recurrence given by the characteristic
  polynomial of the shift operator on the span (Cayley–Hamilton).
- `PowerSeries.exists_normalized_fraction_of_finiteDimensional_shiftSpan`: conversely, a
  finite-dimensional shift span produces a normalized fraction, by Cayley–Hamilton applied
  to the shift operator on the span; the denominator is the reversed characteristic
  polynomial.
- `PowerSeries.exists_normalized_fraction_iff_finiteDimensional_shiftSpan`: the criterion.
-/

open Finset

open scoped Polynomial PowerSeries

section Shift

variable (R : Type*) [Semiring R]

/-- The left shift `a ↦ (n ↦ a (n + 1))` on sequences indexed by `ℕ`, as a linear map. -/
def seqShift : (ℕ → R) →ₗ[R] (ℕ → R) := LinearMap.funLeft R R (· + 1)

@[simp]
lemma seqShift_apply (a : ℕ → R) (n : ℕ) : seqShift R a n = a (n + 1) := rfl

lemma iterate_seqShift_apply (m : ℕ) (a : ℕ → R) (n : ℕ) :
    (⇑(seqShift R))^[m] a n = a (n + m) := by
  induction m generalizing a with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, ih, seqShift_apply, ← add_assoc]

/-- The *shift span* of a sequence `a : ℕ → R`: the `R`-span of all its iterated left shifts
`(a (n + m))ₙ`, `m ≥ 0` (blueprint `definition-reciprocal-root`). -/
def shiftSpan (a : ℕ → R) : Submodule R (ℕ → R) :=
  Submodule.span R (Set.range fun m : ℕ => (⇑(seqShift R))^[m] a)

variable {R}

lemma iterate_seqShift_mem_shiftSpan (a : ℕ → R) (m : ℕ) :
    (⇑(seqShift R))^[m] a ∈ shiftSpan R a :=
  Submodule.subset_span ⟨m, rfl⟩

lemma self_mem_shiftSpan (a : ℕ → R) : a ∈ shiftSpan R a :=
  iterate_seqShift_mem_shiftSpan a 0

/-- The shift span of `a` is contained in any submodule containing all the shifts of `a`. -/
lemma shiftSpan_le {a : ℕ → R} {p : Submodule R (ℕ → R)}
    (h : ∀ m, (⇑(seqShift R))^[m] a ∈ p) : shiftSpan R a ≤ p :=
  Submodule.span_le.2 <| by rintro _ ⟨m, rfl⟩; exact h m

/-- The shift span of `a` is stable under the shift. -/
lemma seqShift_mem_shiftSpan (a : ℕ → R) {x : ℕ → R} (hx : x ∈ shiftSpan R a) :
    seqShift R x ∈ shiftSpan R a :=
  shiftSpan_le (p := (shiftSpan R a).comap (seqShift R)) (fun m => by
    simpa only [Submodule.mem_comap, ← Function.iterate_succ_apply'] using
      iterate_seqShift_mem_shiftSpan a (m + 1)) hx

end Shift

variable {K : Type*} [Field K]

/-- If a sequence eventually satisfies a linear recurrence of order `d`, then the span of
its shifts is finite-dimensional: all shifts from the `N`-th on lie in the span of the `d`
preceding ones. -/
theorem finiteDimensional_shiftSpan_of_recurrence {a c : ℕ → K} {d N : ℕ} (hd : 1 ≤ d)
    (h : ∀ n, max N d ≤ n → a n = -∑ i ∈ Finset.Icc 1 d, c i * a (n - i)) :
    FiniteDimensional K (shiftSpan K a) := by
  set g : ℕ → (ℕ → K) := fun m => (⇑(seqShift K))^[m] a with hg
  set W : Submodule K (ℕ → K) := Submodule.span K (g '' Set.Iio (N + d)) with hW
  have hWfd : FiniteDimensional K W :=
    FiniteDimensional.span_of_finite K ((Set.finite_Iio _).image g)
  have key : ∀ m, g m ∈ W := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases lt_or_ge m (N + d) with hm | hm
      · exact Submodule.subset_span ⟨m, hm, rfl⟩
      · have hdm : d ≤ m := le_trans (Nat.le_add_left d N) hm
        have hgm : g m = -∑ i ∈ Finset.Icc 1 d, c i • g (m - i) := by
          funext n
          have hn : max N d ≤ n + m := by omega
          simp only [hg, iterate_seqShift_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul]
          rw [h (n + m) hn]
          refine congrArg Neg.neg (Finset.sum_congr rfl fun i hi => ?_)
          have hi' : i ≤ m := le_trans (Finset.mem_Icc.1 hi).2 hdm
          have : n + m - i = n + (m - i) := by omega
          rw [this]
        rw [hgm]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
        have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
        exact ih _ (by omega)
  have hle : shiftSpan K a ≤ W := Submodule.span_le.2 (by rintro _ ⟨m, rfl⟩; exact key m)
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

namespace PowerSeries

/-- The `n`-th coefficient of `B * f`, for a polynomial `B` of degree at most `d ≤ n`. -/
lemma coeff_coe_mul {R : Type*} [CommSemiring R] (B : R[X]) (f : R⟦X⟧) {d n : ℕ}
    (hBd : B.natDegree ≤ d) (hdn : d ≤ n) :
    coeff n ((B : R⟦X⟧) * f) = ∑ i ∈ range (d + 1), B.coeff i * coeff (n - i) f := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (f := fun i j => coeff i (B : R⟦X⟧) * coeff j f)]
  simp only [Polynomial.coeff_coe]
  refine (Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hdn))
    fun i _ hi => ?_).symm
  simp only [Finset.mem_range, not_lt] at hi
  rw [B.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

variable {f g : K⟦X⟧} {A B A' B' : K[X]}

lemma isUnit_coe_of_coeff_zero_eq_one (hB : B.coeff 0 = 1) : IsUnit (B : K⟦X⟧) := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hB]
  exact isUnit_one

/-- Two fractions representing the same power series cross-multiply. -/
theorem mul_eq_mul_of_mul_coe_eq (h : f * (B : K⟦X⟧) = (A : K⟦X⟧))
    (h' : f * (B' : K⟦X⟧) = (A' : K⟦X⟧)) : A * B' = A' * B := by
  refine Polynomial.coe_injective K ?_
  rw [Polynomial.coe_mul, Polynomial.coe_mul, ← h, ← h']
  ring

/-- Two normalized fractions that cross-multiply represent the same power series: the
Taylor expansion map is faithful. -/
theorem eq_of_mul_eq_mul (hB : B.coeff 0 = 1) (hB' : B'.coeff 0 = 1)
    (h : f * (B : K⟦X⟧) = (A : K⟦X⟧)) (h' : g * (B' : K⟦X⟧) = (A' : K⟦X⟧))
    (hAB : A * B' = A' * B) : f = g := by
  have hu : IsUnit ((B : K⟦X⟧) * (B' : K⟦X⟧)) :=
    (isUnit_coe_of_coeff_zero_eq_one hB).mul (isUnit_coe_of_coeff_zero_eq_one hB')
  refine hu.mul_right_cancel ?_
  calc f * ((B : K⟦X⟧) * (B' : K⟦X⟧)) = ((A * B' : K[X]) : K⟦X⟧) := by
        rw [Polynomial.coe_mul, ← h]; ring
    _ = ((A' * B : K[X]) : K⟦X⟧) := by rw [hAB]
    _ = g * ((B : K⟦X⟧) * (B' : K⟦X⟧)) := by rw [Polynomial.coe_mul, ← h']; ring

/-- A normalized fraction `f * B = A` makes the coefficients of `f` satisfy the linear
recurrence given by `B`, in every degree beyond the degree of `A`. -/
theorem sum_coeff_mul_coeff_eq_zero (h : f * (B : K⟦X⟧) = (A : K⟦X⟧)) {n : ℕ}
    (hn : A.natDegree < n) (hd : B.natDegree ≤ n) :
    ∑ i ∈ range (B.natDegree + 1), B.coeff i * coeff (n - i) f = 0 := by
  rw [← coeff_coe_mul B f le_rfl hd, mul_comm, h, Polynomial.coeff_coe,
    A.coeff_eq_zero_of_natDegree_lt hn]

/-- If the span of the shifts of a sequence `a` is finite-dimensional, then `a` satisfies the
linear recurrence given by a monic polynomial in all degrees: by Cayley–Hamilton, the
characteristic polynomial of the shift operator on the span kills `a`. -/
theorem exists_monic_sum_coeff_mul_eq_zero_of_finiteDimensional_shiftSpan (a : ℕ → K)
    [FiniteDimensional K (shiftSpan K a)] :
    ∃ p : K[X], p.Monic ∧ ∀ n, ∑ j ∈ range (p.natDegree + 1), p.coeff j * a (n + j) = 0 := by
  set S : shiftSpan K a →ₗ[K] shiftSpan K a :=
    (seqShift K).restrict (fun _ hx => seqShift_mem_shiftSpan a hx) with hS
  refine ⟨S.charpoly, LinearMap.charpoly_monic S, fun n => ?_⟩
  set p : K[X] := S.charpoly with hp
  -- Cayley–Hamilton, read off on the element `a` of the span
  have hpow : ∀ (i : ℕ) (x : shiftSpan K a),
      (((S ^ i) x : shiftSpan K a) : ℕ → K) = (⇑(seqShift K))^[i] (x : ℕ → K) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply, hS,
        LinearMap.coe_restrict_apply]
  have hpow' : ∀ i : ℕ,
      (((S ^ i) ⟨a, self_mem_shiftSpan a⟩ : shiftSpan K a) : ℕ → K)
        = (⇑(seqShift K))^[i] a := fun i => hpow i _
  have h0 : (Polynomial.aeval S) p = 0 := LinearMap.aeval_self_charpoly S
  have h1 : ∑ j ∈ range (p.natDegree + 1),
      p.coeff j • (S ^ j) (⟨a, self_mem_shiftSpan a⟩ : shiftSpan K a) = 0 := by
    have := congrArg (fun T : Module.End K (shiftSpan K a) => T ⟨a, self_mem_shiftSpan a⟩) h0
    simpa only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] using this
  have h2 := congrArg (fun v : shiftSpan K a => (v : ℕ → K) n) h1
  simpa only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, hpow', iterate_seqShift_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    using h2

/-- If the span of the shifts of the coefficient sequence of `f` is finite-dimensional,
then `f` admits a normalized fraction: the denominator is the reverse of the
characteristic polynomial of the shift operator on the span. -/
theorem exists_normalized_fraction_of_finiteDimensional_shiftSpan (a : ℕ → K)
    [FiniteDimensional K (shiftSpan K a)] :
    ∃ A B : K[X], B.coeff 0 = 1 ∧ mk a * (B : K⟦X⟧) = (A : K⟦X⟧) := by
  obtain ⟨p, hpm, key⟩ := exists_monic_sum_coeff_mul_eq_zero_of_finiteDimensional_shiftSpan a
  -- the reversed characteristic polynomial kills all coefficients in degrees `≥ p.natDegree`
  have hzero : ∀ n, p.natDegree ≤ n → coeff n (mk a * (p.reverse : K⟦X⟧)) = 0 := by
    intro n hn
    set F : ℕ → K := fun j => p.coeff j * a (n - p.natDegree + j) with hF
    rw [mul_comm, coeff_coe_mul _ _ p.reverse_natDegree_le hn]
    have hstep : ∀ i ∈ range (p.natDegree + 1),
        p.reverse.coeff i * coeff (n - i) (mk a) = F (p.natDegree - i) := by
      intro i hi
      have hir : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Polynomial.coeff_reverse, Polynomial.revAt_le hir, coeff_mk, hF]
      congr 2
      omega
    have hre : ∑ i ∈ range (p.natDegree + 1), F (p.natDegree - i)
        = ∑ j ∈ range (p.natDegree + 1), F j := by
      simpa using Finset.sum_range_reflect F (p.natDegree + 1)
    rw [Finset.sum_congr rfl hstep, hre, hF]
    exact key (n - p.natDegree)
  refine ⟨trunc p.natDegree (mk a * (p.reverse : K⟦X⟧)), p.reverse, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_reverse, hpm.leadingCoeff]
  · refine PowerSeries.ext fun n => ?_
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with h
    · rfl
    · exact hzero n (not_lt.1 h)

/-- **Rationality criterion**: a power series over a field admits a normalized fraction
`f * B = A` with `B.coeff 0 = 1` if and only if the span of the shifts of its coefficient
sequence is finite-dimensional. -/
theorem exists_normalized_fraction_iff_finiteDimensional_shiftSpan (f : K⟦X⟧) :
    (∃ A B : K[X], B.coeff 0 = 1 ∧ f * (B : K⟦X⟧) = (A : K⟦X⟧)) ↔
      FiniteDimensional K (shiftSpan K fun n => coeff n f) := by
  constructor
  · rintro ⟨A, B, hB0, hAB⟩
    set d : ℕ := max B.natDegree 1 with hd
    refine finiteDimensional_shiftSpan_of_recurrence (a := fun n => coeff n f)
      (c := fun i => B.coeff i) (d := d) (N := A.natDegree + 1) (by omega) fun n hn => ?_
    show coeff n f = -∑ i ∈ Finset.Icc 1 d, B.coeff i * coeff (n - i) f
    have hsum := sum_coeff_mul_coeff_eq_zero hAB (n := n) (by omega) (by omega)
    have hIcc : Finset.Icc 1 B.natDegree = Finset.Ico 1 (B.natDegree + 1) := by
      ext i; simp
    have hshrink : ∑ i ∈ Finset.Icc 1 d, B.coeff i * coeff (n - i) f
        = ∑ i ∈ Finset.Icc 1 B.natDegree, B.coeff i * coeff (n - i) f := by
      refine (Finset.sum_subset
        (Finset.Icc_subset_Icc_right (show B.natDegree ≤ d by omega)) fun i hi hi' => ?_).symm
      rw [Finset.mem_Icc] at hi
      have hlt : B.natDegree < i := by
        by_contra hcon
        exact hi' (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
      rw [B.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]
    have hpeel : ∑ i ∈ range (B.natDegree + 1), B.coeff i * coeff (n - i) f
        = ∑ i ∈ Finset.Icc 1 B.natDegree, B.coeff i * coeff (n - i) f
          + B.coeff 0 * coeff (n - 0) f := by
      rw [Finset.sum_range_succ' (fun i => B.coeff i * coeff (n - i) f) B.natDegree, hIcc,
        Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm 1 i]
    rw [hpeel, hB0, one_mul, Nat.sub_zero] at hsum
    rw [hshrink]
    exact eq_neg_of_add_eq_zero_right hsum
  · intro h
    have hmk : mk (fun n => coeff n f) = f := PowerSeries.ext fun n => by simp
    obtain ⟨A, B, hB0, hAB⟩ :=
      exists_normalized_fraction_of_finiteDimensional_shiftSpan (fun n => coeff n f)
    rw [hmk] at hAB
    exact ⟨A, B, hB0, hAB⟩

end PowerSeries
