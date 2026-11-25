/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.DetTrace
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Reality of a Frobenius module through the traces of the powers of its Frobenius

For an endomorphism `F` of a finite dimensional vector space over a field `K` of characteristic
zero, Newton's identities express the coefficients `c_n` of the reverse characteristic
polynomial `det (1 - t F) = ∑ c_n tⁿ` through the traces `tr (Fᵐ)`, and conversely:

`n c_n = - ∑_{i + j = n, i ≥ 1} tr (F ^ i) c_j`.

Hence the coefficients of `det (1 - t F)` lie in a subfield `S` of `K` if and only if all the
traces `tr (Fᵐ)` do. Applied to the subfield of elements of `K` with real image under
`ι : K →+* ℂ`, a Frobenius module is `ι`-real if and only if the traces of all powers of its
Frobenius have real `ι`-image.

## Main statements

- `LinearMap.natCast_mul_coeff_charpolyRev`: Newton's identities for `det (1 - t F)`.
- `LinearMap.forall_coeff_charpolyRev_mem_iff`: the coefficients of `det (1 - t F)` lie in a
  subfield if and only if the traces of the powers of `F` do.
- `RingHom.realSubfield`: the elements with real `ι`-image.
- `FrobeniusModule.isReal_iff_forall_trace_pow`: a Frobenius module is `ι`-real if and only if
  the traces of all powers of its Frobenius have real `ι`-image.
-/

@[expose] public section

universe u v

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Newton's identities** for the reverse characteristic polynomial
`det (1 - t F) = ∑ c_n tⁿ`: `n c_n = - ∑_{i + j = n} t_i c_j`, with `t_i = tr (F ^ i)` for
`i ≥ 1` and `t_0 = 0`. This is the coefficient of `tⁿ` in the logarithmic derivative identity
`LinearMap.X_mul_derivative_charpolyRev`. -/
theorem natCast_mul_coeff_charpolyRev (F : Module.End K V) (n : ℕ) :
    (n : K) * F.charpolyRev.coeff n =
      -∑ p ∈ Finset.antidiagonal n,
        (if p.1 = 0 then 0 else LinearMap.trace K V (F ^ p.1)) * F.charpolyRev.coeff p.2 := by
  have h := congrArg (PowerSeries.coeff n) (X_mul_derivative_charpolyRev F)
  rw [neg_mul, map_neg, PowerSeries.coeff_mul n (PowerSeries.mk _)] at h
  simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
  rw [← h]
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, Polynomial.coeff_coe]
    push_cast
    ring

/-- Over a field of characteristic zero, the coefficients of the reverse characteristic
polynomial `det (1 - t F)` lie in a subfield `S` if and only if the traces of all powers of `F`
do, by Newton's identities `LinearMap.natCast_mul_coeff_charpolyRev`. -/
theorem forall_coeff_charpolyRev_mem_iff [CharZero K] (F : Module.End K V) (S : Subfield K) :
    (∀ n, F.charpolyRev.coeff n ∈ S) ↔ ∀ m, LinearMap.trace K V (F ^ m) ∈ S := by
  have hN (n : ℕ) := natCast_mul_coeff_charpolyRev F n
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one] at hN
  constructor
  · intro hc m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    rcases m with _ | m
    · rw [pow_zero, LinearMap.trace_one]
      exact natCast_mem S _
    · have h := hN (m + 1)
      rw [Finset.sum_range_succ, ite_eq_right (Nat.succ_ne_zero m), Nat.sub_self,
        coeff_zero_charpolyRev, mul_one] at h
      have hrest : ∑ k ∈ Finset.range (m + 1),
          (if k = 0 then 0 else LinearMap.trace K V (F ^ k)) * F.charpolyRev.coeff (m + 1 - k) ∈
            S := by
        refine S.sum_mem fun k hk ↦ S.mul_mem ?_ (hc _)
        split_ifs
        · exact S.zero_mem
        · exact ih k (Finset.mem_range.1 hk)
      have : LinearMap.trace K V (F ^ (m + 1)) =
          -(((m + 1 : ℕ) : K) * F.charpolyRev.coeff (m + 1)) -
            ∑ k ∈ Finset.range (m + 1),
              (if k = 0 then 0 else LinearMap.trace K V (F ^ k)) *
                F.charpolyRev.coeff (m + 1 - k) := by
        rw [h]
        ring
      rw [this]
      exact S.sub_mem (S.neg_mem (S.mul_mem (natCast_mem S _) (hc _))) hrest
  · intro ht n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases n with _ | n
    · rw [coeff_zero_charpolyRev]
      exact S.one_mem
    · have hrest : ((n + 1 : ℕ) : K) * F.charpolyRev.coeff (n + 1) ∈ S := by
        rw [hN]
        refine S.neg_mem (S.sum_mem fun k hk ↦ ?_)
        split_ifs with hk0
        · rw [zero_mul]
          exact S.zero_mem
        · exact S.mul_mem (ht k) (ih _ (by grind))
      have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
      have := S.mul_mem (S.inv_mem (natCast_mem S (n + 1))) hrest
      rwa [← mul_assoc, inv_mul_cancel₀ hn, one_mul] at this

end LinearMap

namespace RingHom

variable {K : Type v} [Field K]

/-- The subfield of the elements of `K` whose image under `ι : K →+* ℂ` is real, i.e. fixed by
complex conjugation. -/
def realSubfield (ι : K →+* ℂ) : Subfield K :=
  ((starRingEnd ℂ).comp ι).eqLocusField ι

theorem mem_realSubfield {ι : K →+* ℂ} {z : K} :
    z ∈ ι.realSubfield ↔ starRingEnd ℂ (ι z) = ι z :=
  Iff.rfl

end RingHom

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- A Frobenius module is `ι`-real, i.e. the `ι`-image of its local polynomial `det (1 - t F)`
has real coefficients, if and only if the traces `tr (Fᵐ)` of all powers of its Frobenius have
real `ι`-image: apply `LinearMap.forall_coeff_charpolyRev_mem_iff` to the subfield of elements
of `K` whose `ι`-image is fixed by complex conjugation. -/
theorem isReal_iff_forall_trace_pow (ι : K →+* ℂ) (M : FrobeniusModule.{u, v} K) :
    M.IsReal ι ↔ ∀ m : ℕ,
      starRingEnd ℂ (ι (LinearMap.trace K M.carrier (M.frobeniusEnd ^ m))) =
        ι (LinearMap.trace K M.carrier (M.frobeniusEnd ^ m)) :=
  have : CharZero K := ι.charZero
  LinearMap.forall_coeff_charpolyRev_mem_iff M.frobeniusEnd ι.realSubfield

end FrobeniusModule
