/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtension

/-! # Unit times uniformizer power expressions in `𝒪_E`

The chosen uniformizer `ϖ_E` of the integers `𝒪_E` of a finite extension `E/ℚ_ℓ` is irreducible,
so every nonzero element of `𝒪_E` is a unit times a power of `ϖ_E`. Since `ℓ` lies in the maximal
ideal, every nonzero element of `𝒪_E` divides a power of `ℓ`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Padic

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

/-- `𝒪_E` is a discrete valuation ring. -/
theorem coefficientExtensionIntegers_isDiscreteValuationRing :
    IsDiscreteValuationRing (coefficientExtensionIntegers l E) :=
  (coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.2.1

/-- The chosen uniformizer of `𝒪_E` is irreducible. -/
theorem irreducible_coefficientExtensionUniformizer :
    Irreducible (coefficientExtensionUniformizer l E) := by
  have hE := (coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsLocalRing (coefficientExtensionIntegers l E) := hE.2.2.2.1
  let := coefficientExtensionIntegers_isDiscreteValuationRing l E
  have hgen : Ideal.span {coefficientExtensionUniformizer l E} =
      coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr ?_
  exact (hE.2.2.2.2.2.1 (IsLocalRing.maximalIdeal (coefficientExtensionIntegers l E))
    (IsLocalRing.maximalIdeal.isMaximal (coefficientExtensionIntegers l E))).trans hgen.symm

/-- Every nonzero element of `𝒪_E` is a unit times a power of the chosen uniformizer. -/
theorem exists_eq_unit_mul_coefficientExtensionUniformizer_pow
    {x : coefficientExtensionIntegers l E} (hx : x ≠ 0) :
    ∃ (n : ℕ) (c : (coefficientExtensionIntegers l E)ˣ),
      x = c * coefficientExtensionUniformizer l E ^ n := by
  let := coefficientExtensionIntegers_isDiscreteValuationRing l E
  exact IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx
    (irreducible_coefficientExtensionUniformizer l E)

/-- The chosen uniformizer of `𝒪_E` divides `ℓ`. -/
theorem coefficientExtensionUniformizer_dvd_natCast :
    coefficientExtensionUniformizer l E ∣ (l : coefficientExtensionIntegers l E) := by
  have hE := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {coefficientExtensionUniformizer l E} =
      coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  refine Ideal.mem_span_singleton.mp ?_
  rw [hgen]
  refine (hE.2.1 _).mpr ?_
  rw [coefficientExtensionAbsoluteValue_apply, SubringClass.coe_natCast,
    ← map_natCast (algebraMap ℚ_[l] E), spectralNorm_extends]
  exact Padic.norm_p_lt_one

/-- Every nonzero element of `𝒪_E` divides a power of `ℓ`. -/
theorem exists_mul_eq_natCast_pow {x : coefficientExtensionIntegers l E} (hx : x ≠ 0) :
    ∃ (k : ℕ) (y : coefficientExtensionIntegers l E), x * y = ((l ^ k : ℕ) : _) := by
  obtain ⟨n, c, rfl⟩ := exists_eq_unit_mul_coefficientExtensionUniformizer_pow l E hx
  obtain ⟨t, ht⟩ := coefficientExtensionUniformizer_dvd_natCast l E
  refine ⟨n, ↑c⁻¹ * t ^ n, ?_⟩
  rw [Nat.cast_pow, ht, mul_pow]
  calc (c : coefficientExtensionIntegers l E) * coefficientExtensionUniformizer l E ^ n *
        (↑c⁻¹ * t ^ n) = (↑c * ↑c⁻¹) * (coefficientExtensionUniformizer l E ^ n * t ^ n) := by
        ring
    _ = _ := by rw [Units.mul_inv, one_mul]

end Padic
