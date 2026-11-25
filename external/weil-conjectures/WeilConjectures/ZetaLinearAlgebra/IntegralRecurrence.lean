/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import WeilConjectures.ZetaLinearAlgebra.ShiftSpan

@[expose] public section

/-!
# Integral rational presentation of an integral power series

Let `a : ℕ → ℤ` be a sequence of integers and let `aQ : ℕ → ℚ` be its coefficientwise image.
The `ℤ`-span `intShiftSpan a` of the iterated left shifts of `aQ` is a shift-stable lattice
inside the `ℚ`-span `shiftSpan ℚ aQ`. If the latter is finite-dimensional, then finitely many
coordinates separate it (`Submodule.exists_finset_eq_of_forall_apply_eq`), so the lattice
embeds into a finite free `ℤ`-module and is therefore itself finite and free.
Cayley–Hamilton for the shift operator on the lattice then produces a *monic* integral
polynomial annihilating the sequence, and its reverse is an integral denominator for the
power series `∑ a n Xⁿ`.

The upshot is that a power series with integer coefficients that is rational over `ℚ` already
admits a normalized fraction with *integer* numerator and denominator. The coprimality of that
fraction (Gauss' lemma) and the uniqueness of the reduced fraction are developed elsewhere.

## Main definitions

- `intSeqShift`: the left shift on rational sequences, viewed as a `ℤ`-linear map.
- `intShiftSpan`: the integral shift lattice, the `ℤ`-span of the iterated shifts of `aQ`.

## Main statements

- `finite_intShiftSpan` and `free_intShiftSpan`: if `shiftSpan ℚ aQ` is finite-dimensional,
  the integral shift lattice is a finite free `ℤ`-module.
- `exists_monic_sum_coeff_mul_eq_zero`: the integral Cayley–Hamilton recurrence, i.e. a monic
  integral polynomial `C` with `∑ i, C.coeff i * a (n + i) = 0` for all `n`.
- `PowerSeries.exists_int_normalized_fraction`: an integral power series that is rational over
  `ℚ` admits a normalized fraction with integral numerator and denominator.
-/

open Finset

open scoped Polynomial PowerSeries

/-- The left shift `x ↦ (n ↦ x (n + 1))` on rational sequences, as a `ℤ`-linear map. -/
def intSeqShift : (ℕ → ℚ) →ₗ[ℤ] (ℕ → ℚ) := LinearMap.funLeft ℤ ℚ (· + 1)

@[simp]
lemma intSeqShift_apply (x : ℕ → ℚ) (n : ℕ) : intSeqShift x n = x (n + 1) := rfl

lemma coe_intSeqShift : ⇑intSeqShift = ⇑(seqShift ℚ) := rfl


lemma iterate_intSeqShift_apply (m : ℕ) (x : ℕ → ℚ) (n : ℕ) :
    (⇑intSeqShift)^[m] x n = x (n + m) :=
  iterate_seqShift_apply ℚ m x n

/-- The *integral shift lattice* of a sequence `a : ℕ → ℤ`: the `ℤ`-span of the iterated left
shifts of the rational sequence `n ↦ (a n : ℚ)`. -/
def intShiftSpan (a : ℕ → ℤ) : Submodule ℤ (ℕ → ℚ) :=
  Submodule.span ℤ (Set.range fun m : ℕ => (⇑intSeqShift)^[m] fun n => (a n : ℚ))

lemma iterate_intSeqShift_mem_intShiftSpan (a : ℕ → ℤ) (m : ℕ) :
    (⇑intSeqShift)^[m] (fun n => (a n : ℚ)) ∈ intShiftSpan a :=
  Submodule.subset_span ⟨m, rfl⟩

lemma self_mem_intShiftSpan (a : ℕ → ℤ) : (fun n => (a n : ℚ)) ∈ intShiftSpan a :=
  iterate_intSeqShift_mem_intShiftSpan a 0

/-- The integral shift lattice sits inside the rational shift span. -/
lemma intShiftSpan_le_restrictScalars (a : ℕ → ℤ) :
    intShiftSpan a ≤ (shiftSpan ℚ fun n => (a n : ℚ)).restrictScalars ℤ := by
  have h : Submodule.span ℤ (Set.range fun m : ℕ => (⇑intSeqShift)^[m] fun n => (a n : ℚ))
      ≤ (shiftSpan ℚ fun n => (a n : ℚ)).restrictScalars ℤ := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact iterate_seqShift_mem_shiftSpan _ m
  exact h

/-- The integral shift lattice is stable under the shift. -/
lemma intSeqShift_mem_intShiftSpan (a : ℕ → ℤ) {x : ℕ → ℚ} (hx : x ∈ intShiftSpan a) :
    intSeqShift x ∈ intShiftSpan a := by
  have h : Submodule.span ℤ (Set.range fun m : ℕ => (⇑intSeqShift)^[m] fun n => (a n : ℚ))
      ≤ (intShiftSpan a).comap intSeqShift := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    simpa only [SetLike.mem_coe, Submodule.mem_comap, ← Function.iterate_succ_apply'] using
      iterate_intSeqShift_mem_intShiftSpan a (m + 1)
  exact h hx

/-- Every element of the integral shift lattice has integral values. -/
lemma exists_int_eq_of_mem_intShiftSpan {a : ℕ → ℤ} {x : ℕ → ℚ}
    (hx : x ∈ intShiftSpan a) (n : ℕ) :
    ∃ z : ℤ, x n = z := by
  have hx' : x ∈ Submodule.span ℤ
      (Set.range fun m : ℕ => (⇑intSeqShift)^[m] fun k => (a k : ℚ)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    exact ⟨a (n + m), by simp [iterate_intSeqShift_apply]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, hu⟩ := hy
    obtain ⟨v, hv⟩ := hz
    exact ⟨u + v, by simp [hu, hv]⟩
  | smul c y _ hy =>
    obtain ⟨u, hu⟩ := hy
    exact ⟨c * u, by simp [hu]⟩

/-- If the rational shift span of `a` is finite-dimensional, the integral shift lattice is a
finitely generated `ℤ`-module: finitely many coordinates separate the rational span, and on
those coordinates the lattice takes integral values. -/
theorem finite_intShiftSpan (a : ℕ → ℤ)
    (h : FiniteDimensional ℚ (shiftSpan ℚ fun n => (a n : ℚ))) :
    Module.Finite ℤ (intShiftSpan a) := by
  obtain ⟨J, hJ⟩ :=
    Submodule.exists_finset_eq_of_forall_apply_eq (shiftSpan ℚ fun n => (a n : ℚ))
  set ι : (J → ℤ) →ₗ[ℤ] (J → ℚ) := (Algebra.linearMap ℤ ℚ).compLeft J
  have hιinj : Function.Injective ι := fun y z hyz =>
    funext fun j => Int.cast_injective (congrFun hyz j)
  have : IsNoetherian ℤ (LinearMap.range ι) :=
    isNoetherian_of_linearEquiv (LinearEquiv.ofInjective ι hιinj)
  set φ : intShiftSpan a →ₗ[ℤ] (J → ℚ) :=
    (LinearMap.funLeft ℤ ℚ fun j : J => (j : ℕ)).comp (intShiftSpan a).subtype
  have hmem : ∀ x : intShiftSpan a, φ x ∈ LinearMap.range ι := by
    intro x
    choose y hy using fun j : J => exists_int_eq_of_mem_intShiftSpan x.2 (j : ℕ)
    exact ⟨y, funext fun j => (hy j).symm⟩
  refine Module.Finite.of_injective (LinearMap.codRestrict _ φ hmem) fun x z hxz => ?_
  refine Subtype.ext (hJ _ (intShiftSpan_le_restrictScalars a x.2) _
    (intShiftSpan_le_restrictScalars a z.2) fun j hj => ?_)
  exact congrFun (congrArg Subtype.val hxz) ⟨j, hj⟩

/-- If the rational shift span of `a` is finite-dimensional, the integral shift lattice is a
free `ℤ`-module of finite rank. -/
theorem free_intShiftSpan (a : ℕ → ℤ)
    (h : FiniteDimensional ℚ (shiftSpan ℚ fun n => (a n : ℚ))) :
    Module.Free ℤ (intShiftSpan a) :=
  have := finite_intShiftSpan a h
  inferInstance

/-- **Integral Cayley–Hamilton recurrence**: if the rational shift span of an integral
sequence `a` is finite-dimensional, then `a` satisfies a linear recurrence whose coefficients
are those of a *monic* integral polynomial, namely the characteristic polynomial of the shift
operator on the integral shift lattice. -/
theorem exists_monic_sum_coeff_mul_eq_zero (a : ℕ → ℤ)
    (h : FiniteDimensional ℚ (shiftSpan ℚ fun n => (a n : ℚ))) :
    ∃ C : ℤ[X], C.Monic ∧
      ∀ n, ∑ i ∈ range (C.natDegree + 1), C.coeff i * a (n + i) = 0 := by
  have := finite_intShiftSpan a h
  have := free_intShiftSpan a h
  set S : intShiftSpan a →ₗ[ℤ] intShiftSpan a :=
    intSeqShift.restrict (fun _ hx => intSeqShift_mem_intShiftSpan a hx) with hS
  set C : ℤ[X] := S.charpoly with hC
  refine ⟨C, LinearMap.charpoly_monic S, fun n => ?_⟩
  have hpow : ∀ (i : ℕ) (x : intShiftSpan a),
      (((S ^ i) x : intShiftSpan a) : ℕ → ℚ) = (⇑intSeqShift)^[i] (x : ℕ → ℚ) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply, hS,
        LinearMap.coe_restrict_apply]
  have h0 : (Polynomial.aeval S) C = 0 := LinearMap.aeval_self_charpoly S
  have h1 : ∑ j ∈ range (C.natDegree + 1),
      C.coeff j • (S ^ j) (⟨fun k => (a k : ℚ), self_mem_intShiftSpan a⟩ : intShiftSpan a)
        = 0 := by
    have := congrArg (fun T : Module.End ℤ (intShiftSpan a) =>
      T (⟨fun k => (a k : ℚ), self_mem_intShiftSpan a⟩ : intShiftSpan a)) h0
    simpa only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] using this
  have h2 := congrArg (fun v : intShiftSpan a => (v : ℕ → ℚ) n) h1
  simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply,
    zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, hpow, iterate_intSeqShift_apply,
    ZeroMemClass.coe_zero, Pi.zero_apply] at h2
  exact_mod_cast h2

namespace PowerSeries

/-- An integral power series that admits a normalized fraction over `ℚ` admits one with
integral numerator and denominator; moreover the numerator has the same constant term as the
power series. -/
theorem exists_int_normalized_fraction' (f : ℤ⟦X⟧)
    (h : ∃ A B : ℚ[X], B.coeff 0 = 1 ∧
      map (Int.castRingHom ℚ) f * (B : ℚ⟦X⟧) = (A : ℚ⟦X⟧)) :
    ∃ A B : ℤ[X], B.coeff 0 = 1 ∧ A.coeff 0 = coeff 0 f ∧
      f * (B : ℤ⟦X⟧) = (A : ℤ⟦X⟧) := by
  have hfd : FiniteDimensional ℚ (shiftSpan ℚ fun n => ((coeff n f : ℤ) : ℚ)) := by
    have h' := (exists_normalized_fraction_iff_finiteDimensional_shiftSpan
      (map (Int.castRingHom ℚ) f)).1 h
    have hseq : (fun n => coeff n (map (Int.castRingHom ℚ) f))
        = fun n => ((coeff n f : ℤ) : ℚ) := by
      funext n
      simp
    rwa [hseq] at h'
  obtain ⟨C, hCm, hrec⟩ := exists_monic_sum_coeff_mul_eq_zero (fun n => coeff n f) hfd
  have hB0 : C.reverse.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_reverse, hCm.leadingCoeff]
  have hzero : ∀ n, C.natDegree ≤ n → coeff n (f * (C.reverse : ℤ⟦X⟧)) = 0 := by
    intro n hn
    set F : ℕ → ℤ := fun j => C.coeff j * coeff (n - C.natDegree + j) f with hF
    rw [mul_comm, coeff_coe_mul _ _ C.reverse_natDegree_le hn]
    have hstep : ∀ i ∈ range (C.natDegree + 1),
        C.reverse.coeff i * coeff (n - i) f = F (C.natDegree - i) := by
      intro i hi
      have hir : i ≤ C.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hidx : n - i = n - C.natDegree + (C.natDegree - i) := by omega
      simp only [hF, Polynomial.coeff_reverse, Polynomial.revAt_le hir]
      rw [hidx]
    have hre : ∑ i ∈ range (C.natDegree + 1), F (C.natDegree - i)
        = ∑ j ∈ range (C.natDegree + 1), F j := by
      simpa using Finset.sum_range_reflect F (C.natDegree + 1)
    rw [Finset.sum_congr rfl hstep, hre, hF]
    exact hrec (n - C.natDegree)
  refine ⟨trunc (C.natDegree + 1) (f * (C.reverse : ℤ⟦X⟧)), C.reverse, hB0, ?_, ?_⟩
  · rw [coeff_trunc, ite_eq_left (Nat.succ_pos _), coeff_zero_eq_constantCoeff, map_mul,
      ← coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, hB0, mul_one]
  · refine PowerSeries.ext fun n => ?_
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hlt
    · rfl
    · exact hzero n (by omega)

/-- **Integral rational presentation**: a power series with integer coefficients that admits a
normalized fraction over `ℚ` already admits one over `ℤ`, that is a pair of integral
polynomials `A`, `B` with `B.coeff 0 = 1` and `f * B = A`. -/
theorem exists_int_normalized_fraction (f : ℤ⟦X⟧)
    (h : ∃ A B : ℚ[X], B.coeff 0 = 1 ∧
      map (Int.castRingHom ℚ) f * (B : ℚ⟦X⟧) = (A : ℚ⟦X⟧)) :
    ∃ A B : ℤ[X], B.coeff 0 = 1 ∧ f * (B : ℤ⟦X⟧) = (A : ℤ⟦X⟧) := by
  obtain ⟨A, B, hB0, -, hAB⟩ := exists_int_normalized_fraction' f h
  exact ⟨A, B, hB0, hAB⟩

end PowerSeries
