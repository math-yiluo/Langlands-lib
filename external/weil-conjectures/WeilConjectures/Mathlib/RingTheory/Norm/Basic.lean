/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.NormTrace

/-!
# Norms in finite free algebras

Let `B` be an `A`-algebra which is finite free as an `A`-module.

## Main results

- `Algebra.isUnit_norm_iff`: `Algebra.norm A b` is a unit iff `b` is a unit.
- `Algebra.norm_ne_zero_of_mem_nonZeroDivisors`: if `A` is a domain, the norm of a
  non-zero-divisor is nonzero.
- `Algebra.norm_mem_iff_exists_isPrime`: for a prime `p` of `A`, the norm of `h` lies in `p`
  iff `h` lies in some prime of `B` over `p`. In other words, the zero locus of the norm of `h`
  is the image of the zero locus of `h` in `Spec B`.
-/

@[expose] public section

open Module

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- In a finite free algebra, the norm of `b` is a unit iff `b` is a unit. -/
theorem isUnit_norm_iff [Module.Free A B] [Module.Finite A B] {b : B} :
    IsUnit (Algebra.norm A b) ↔ IsUnit b := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det]
  refine ⟨fun h ↦ ?_, fun h ↦ h.map (Algebra.lmul A B)⟩
  obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).mp h).2 1
  exact IsUnit.of_mul_eq_one c hc

/-- Over a domain, the norm of a non-zero-divisor of a finite free algebra is nonzero. -/
theorem norm_ne_zero_of_mem_nonZeroDivisors [IsDomain A] [Module.Free A B] [Module.Finite A B]
    {h : B} (hh : h ∈ nonZeroDivisors B) : Algebra.norm A h ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis A B
  rw [Algebra.norm_eq_matrix_det b]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hv' : b.repr (h * b.equivFun.symm v) = 0 := by
    ext i
    rw [← Algebra.leftMulMatrix_mulVec_repr, ← b.equivFun_apply, b.equivFun.apply_symm_apply]
    exact congrFun hv i
  rw [LinearEquiv.map_eq_zero_iff, mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff hh,
    LinearEquiv.map_eq_zero_iff] at hv'
  exact hv0 hv'

/-- In a finite free algebra, the norm of `h` lies in a prime `p` iff `h` lies in some prime
lying over `p`: localise at `p`, where the norm is a non-unit iff `h` is a non-unit, i.e.
`h` lies in a maximal ideal, and go up. -/
theorem norm_mem_iff_exists_isPrime [Module.Free A B] [Module.Finite A B] (p : Ideal A)
    [p.IsPrime] (h : B) : Algebra.norm A h ∈ p ↔
      ∃ q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = p ∧ h ∈ q := by
  classical
  let Bₚ := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  let b := (Module.Free.chooseBasis A B).localizationLocalization (Localization.AtPrime p)
    p.primeCompl Bₚ
  have : Module.Free (Localization.AtPrime p) Bₚ := .of_basis b
  have : Module.Finite (Localization.AtPrime p) Bₚ := .of_basis b
  rw [← not_iff_not, ← Ideal.mem_primeCompl_iff,
    ← IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p,
    ← Algebra.norm_localization A p.primeCompl (Sₘ := Bₚ), isUnit_norm_iff]
  have hdisj (q : Ideal B) (hq : q.comap (algebraMap A B) ≤ p) :
      Disjoint (Algebra.algebraMapSubmonoid B p.primeCompl : Set B) q := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ haq
    exact ha (hq haq)
  refine ⟨fun hu ⟨q, hq, hqp, hhq⟩ ↦ ?_, fun hn ↦ ?_⟩
  · have := IsLocalization.isPrime_of_isPrime_disjoint _ Bₚ q hq (hdisj q hqp.le)
    exact this.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hhq) hu)
  · by_contra hu
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {algebraMap B Bₚ h})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hle' : (M.comap (algebraMap B Bₚ)).comap (algebraMap A B) ≤ p := by
      intro a ha
      by_contra hap
      refine hM.ne_top (M.eq_top_of_isUnit_mem ha ?_)
      exact IsLocalization.map_units Bₚ (⟨algebraMap A B a, a, hap, rfl⟩ :
        Algebra.algebraMapSubmonoid B p.primeCompl)
    obtain ⟨Q, hQ, hQp, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p _ hle'
    exact hn ⟨Q, hQp, hQ', hQ (hle (Ideal.mem_span_singleton_self _))⟩

end Algebra
