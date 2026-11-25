/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Finite subalgebras with prescribed fraction field

Source: Stacks Project, More on Algebra, Tag 07PR, proof, finite algebra model paragraph
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v w

namespace MvPolynomial

/-- For `A = k[[x₁, …, xₙ]][y₁, …, yₘ]` in positive characteristic, `A` is a domain and
any finite extension `M` of its fraction field has a finite `A`-subalgebra with fraction
field `M`. The scalar tower identifies the structural map `A → M` with `A → K → M`.
Source: Stacks Project, More on Algebra, Tag 07PR, proof, finite algebra model paragraph
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof (the source asserts the model's existence; Mathlib supplies denominator clearing):
1. The power-series no-zero-divisor instance and polynomial domain instance prove that
   A is a domain. The complement of the zero prime is the non-zero-divisor submonoid,
   so the given localization K is its fraction field.
2. Mathlib's `FiniteDimensional.exists_is_basis_integral` supplies a finite K-basis e
   of M consisting of elements integral over A. This theorem scales a finite basis by
   a common nonzero denominator and does not require separability or a Dedekind domain.
3. Construct B as `Algebra.adjoin A (Set.range e)`. It is finite over A by
   `Algebra.finite_adjoin_of_finite_of_isIntegral`.
4. For z in M, `IsLocalization.exist_integer_multiples_of_finite` clears the finite
   family of coordinates `e.repr z`: there is a nonzero d in A and numerators a_i in A
   with a_i = d * (e.repr z)_i in K. The basis expansion then gives
   d * z = sum_i a_i * e_i in B. The scalar tower and the two injective field-fraction
   maps show that d remains nonzero in M.
5. Both d * z and d belong to B, and z = (d * z) / d. -/
theorem exists_finite_subalgebra_fraction_field
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (n m : ℕ)
    (K : Type v) [Field K]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    [IsLocalization.AtPrime K
      (⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))]
    (M : Type w) [Field M] [Algebra K M]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) M]
    [IsScalarTower (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K M]
    [Module.Finite K M] :
    IsDomain (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) ∧
      ∃ B : Subalgebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) M,
        Module.Finite (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) B ∧
          ∀ z : M, ∃ b s : B, (s : M) ≠ 0 ∧ z = (b : M) / (s : M) := by
  classical
  let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
  let : IsDomain (MvPowerSeries (Fin n) k) := NoZeroDivisors.to_isDomain _
  have hA : IsDomain A := inferInstance
  have : IsFractionRing A K := by
    simpa only [IsLocalization.AtPrime, Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization.AtPrime K (⊥ : Ideal A))
  have _hp := hp
  refine ⟨hA, ?_⟩
  obtain ⟨t, e, he⟩ := FiniteDimensional.exists_is_basis_integral A K M
  let B := Algebra.adjoin A (Set.range e)
  have hB : Module.Finite A B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range e)
      (by rintro _ ⟨i, rfl⟩; exact he i)
  refine ⟨B, hB, ?_⟩
  intro z
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors A) (fun i => e.repr z i)
  choose a ha using hd
  have hd0 : (d : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hdm : algebraMap A M d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K M]
    exact (map_ne_zero (algebraMap K M)).mpr
      ((map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hd0)
  have hdz : (d : A) • z ∈ B := by
    rw [← e.sum_repr z, Finset.smul_sum]
    apply B.sum_mem
    intro i _
    rw [← smul_assoc, ← ha i, algebraMap_smul]
    exact B.smul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (a i)
  refine ⟨⟨(d : A) • z, hdz⟩, ⟨algebraMap A M d, B.algebraMap_mem d⟩, hdm, ?_⟩
  change z = ((d : A) • z) / algebraMap A M d
  rw [Algebra.smul_def, mul_div_cancel_left₀ _ hdm]

end MvPolynomial
