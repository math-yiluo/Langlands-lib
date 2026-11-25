/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # Coefficient stages for an arbitrary nonzero nonunit

Source: Zheng, Construction 4.1, printed p. 21; Serre, Local Fields, Chapter II, §2.
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace Padic

/-- Nonzero nonunits define finite, prime-power-torsion coefficient stages and a complete
adic topology. Unlike a choice of uniformizer, the parameter may have any positive valuation.
Source: Zheng, Construction 4.1, printed p. 21; Serre, Local Fields, Chapter II, §2
(blueprint: lem-pur-nonunit-coefficient-stages).

Proof: write t as a unit times a positive power of a uniformizer pi. Its principal ideal
is therefore a positive power of the maximal ideal. Finite residue fields and induction on
ideal powers give finite quotients. Since l belongs to the maximal ideal, l to the power
r(n+1) belongs to (t)^(n+1). All quotient transitions are surjective on representatives.
The maximal-adic topology is complete by the finite-module completeness theorem applied
to O itself. A positive ideal power defines the same topology, so it remains complete. -/
theorem nonunit_coefficient_stages
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (t : coefficientExtensionIntegers l E) (ht : t ≠ 0) (hunit : ¬ IsUnit t) :
    (∀ n : ℕ, Finite (coefficientExtensionIntegers l E ⧸
      (Ideal.span ({t} : Set (coefficientExtensionIntegers l E))) ^ (n + 1))) ∧
    (∀ n : ℕ, ∃ a : ℕ,
      (l ^ a : coefficientExtensionIntegers l E ⧸
        (Ideal.span ({t} : Set (coefficientExtensionIntegers l E))) ^ (n + 1)) = 0) ∧
    (∀ {m n : ℕ} (h : m ≤ n), Function.Surjective
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) :
        (coefficientExtensionIntegers l E ⧸
          (Ideal.span ({t} : Set (coefficientExtensionIntegers l E))) ^ (n + 1)) →+*
        (coefficientExtensionIntegers l E ⧸
          (Ideal.span ({t} : Set (coefficientExtensionIntegers l E))) ^ (m + 1)))) ∧
    IsAdicComplete (Ideal.span ({t} : Set (coefficientExtensionIntegers l E)))
      (coefficientExtensionIntegers l E) := by
  let R := coefficientExtensionIntegers l E
  let J := coefficientExtensionMaximalIdeal l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsLocalRing R := h.2.2.2.1
  let : IsDiscreteValuationRing R := h.2.2.2.2.2.2.2.1
  have hJ : J = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  let pi := coefficientExtensionUniformizer l E
  have hpi : Ideal.span ({pi} : Set R) = J :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hirr : Irreducible pi :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mpr (hJ.symm.trans hpi.symm)
  obtain ⟨r, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hirr
  have hr : 0 < r := by
    by_contra hn
    have hz : r = 0 := by omega
    apply hunit
    rw [hv, hz, pow_zero, mul_one]
    exact v.isUnit
  have htJ : Ideal.span ({t} : Set R) = J ^ r := by
    rw [hv, Ideal.span_singleton_mul_left_unit v.isUnit, ← Ideal.span_singleton_pow, hpi]
  have : Finite (R ⧸ J) := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hl : (l : R) ∈ J := by
    apply h.2.1 _ |>.mpr
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  refine ⟨?_, ?_, fun _ ↦ Ideal.Quotient.factor_surjective _, ?_⟩
  · intro n
    rw [htJ, ← pow_mul]
    exact Ideal.finite_quotient_pow (hpi ▸ Submodule.fg_span_singleton pi) _
  · intro n
    refine ⟨r * (n + 1), ?_⟩
    have hmem : (l : R) ^ (r * (n + 1)) ∈ (Ideal.span ({t} : Set R)) ^ (n + 1) := by
      rw [htJ, ← pow_mul]
      exact Ideal.pow_mem_pow hl _
    simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  · have hcomplete : IsAdicComplete J R :=
      (finite_module_adic_complete_and_hom.{u, u, u} l E).1 R |>.1
    let : WithIdeal R := ⟨J⟩
    have htop : IsAdic J := rfl
    have hc := htop.isAdicComplete_iff.mp hcomplete
    rw [htJ]
    exact (is_ideal_adic_pow htop hr).isAdicComplete_iff.mpr hc

end Padic
