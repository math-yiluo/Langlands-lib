/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitMap
public import WeilConjectures.RingTheory.Valuation.IntegralClosureHenselianDVR

/-!

# The valuation of the geometric generic point of a slice trait

Let `D` be a slice trait (`AlgebraicGeometry.SliceTrait`): a strictly henselian trait `Spec R`
with a geometric generic point `R ⟶ Ω'`, `Ω'` algebraically closed and algebraic over `R`. The
elements of `Ω'` integral over `R` form a valuation subring (`SliceTrait.valuationSubring`,
from `IsDiscreteValuationRing.integralClosureValuationSubring`): the unique extension of the
valuation of `R` to `Ω'`. It is stable under the automorphisms of `Ω'` over `R`, and a morphism of
slice traits `H` is compatible with these valuations: `H.ΩMap⁻¹(𝒪₂) = 𝒪₁`
(`SliceTrait.Hom.comap_valuationSubring`).

-/

@[expose] public section

universe u

open IsLocalRing

namespace AlgebraicGeometry.SliceTrait

variable {R₁ : Type u} [CommRing R₁] [IsLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)

/-- The valuation subring of `Ω'`: the elements integral over `R`. -/
noncomputable def valuationSubring : ValuationSubring D.Ω :=
  letI := D.a.toAlgebra
  haveI : FaithfulSMul D.R D.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  haveI := D.isAlgebraic_a
  IsDiscreteValuationRing.integralClosureValuationSubring D.R D.Ω

lemma mem_valuationSubring {z : D.Ω} :
    z ∈ D.valuationSubring ↔ letI := D.a.toAlgebra; _root_.IsIntegral D.R z :=
  Iff.rfl

lemma a_mem_valuationSubring (r : D.R) : D.a r ∈ D.valuationSubring :=
  letI := D.a.toAlgebra
  haveI : FaithfulSMul D.R D.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  haveI := D.isAlgebraic_a
  IsDiscreteValuationRing.algebraMap_mem_integralClosureValuationSubring r

lemma valuation_a_lt_one_iff {r : D.R} :
    D.valuationSubring.valuation (D.a r) < 1 ↔ r ∈ maximalIdeal D.R :=
  letI := D.a.toAlgebra
  haveI : FaithfulSMul D.R D.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  haveI := D.isAlgebraic_a
  IsDiscreteValuationRing.valuation_algebraMap_lt_one_iff

lemma valuation_a_eq_one_iff {r : D.R} :
    D.valuationSubring.valuation (D.a r) = 1 ↔ IsUnit r :=
  letI := D.a.toAlgebra
  haveI : FaithfulSMul D.R D.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  haveI := D.isAlgebraic_a
  IsDiscreteValuationRing.valuation_algebraMap_eq_one_iff

/-- The automorphisms of `Ω'` over `R` preserve the valuation subring. -/
lemma map_mem_valuationSubring_iff (σ : D.Ω ≃+* D.Ω) (hσ : ∀ r : D.R, σ (D.a r) = D.a r)
    {z : D.Ω} : σ z ∈ D.valuationSubring ↔ z ∈ D.valuationSubring :=
  letI := D.a.toAlgebra
  haveI : FaithfulSMul D.R D.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  haveI := D.isAlgebraic_a
  IsDiscreteValuationRing.map_mem_integralClosureValuationSubring_iff σ hσ

/-- The value group of `Ω'` is in the divisible hull of that of `R`. -/
lemma exists_valuation_pow_eq_zpow {ϖ : D.R} (hϖ : Irreducible ϖ) {z : D.Ω} (hz : z ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, D.valuationSubring.valuation z ^ n =
      D.valuationSubring.valuation (D.a ϖ) ^ m :=
  letI := D.a.toAlgebra
  haveI : FaithfulSMul D.R D.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  haveI := D.isAlgebraic_a
  IsDiscreteValuationRing.exists_valuation_pow_eq_zpow hϖ hz

end AlgebraicGeometry.SliceTrait

namespace AlgebraicGeometry.SliceTrait.Hom

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] {c : Ω₁ →+* Ω₂}
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁}
  {b₂ : R₂ →+* κ₂} {D₁ : SliceTrait a₁ b₁} {D₂ : SliceTrait a₂ b₂} (H : SliceTrait.Hom ι c D₁ D₂)

/-- A morphism of slice traits is compatible with the valuations of the geometric generic
points: `ΩMap⁻¹(𝒪₂) = 𝒪₁`. -/
theorem comap_valuationSubring :
    D₂.valuationSubring.comap H.ΩMap = D₁.valuationSubring := by
  let := D₁.a.toAlgebra
  let := D₂.a.toAlgebra
  have : FaithfulSMul D₁.R D₁.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D₁.injective_a
  have : FaithfulSMul D₂.R D₂.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D₂.injective_a
  have := D₁.isAlgebraic_a
  have := D₂.isAlgebraic_a
  let : Algebra D₁.R D₂.R := H.ψ.toAlgebra
  let : Algebra D₁.Ω D₂.Ω := H.ΩMap.toAlgebra
  let : Algebra D₁.R D₂.Ω := (D₂.a.comp H.ψ).toAlgebra
  have : IsLocalHom (algebraMap D₁.R D₂.R) := H.isLocalHom_ψ
  have : IsScalarTower D₁.R D₂.R D₂.Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower D₁.R D₁.Ω D₂.Ω := IsScalarTower.of_algebraMap_eq fun r ↦
    (RingHom.congr_fun H.ΩMap_comp_a r).symm
  exact IsDiscreteValuationRing.comap_integralClosureValuationSubring

lemma ΩMap_mem_valuationSubring_iff {z : D₁.Ω} :
    H.ΩMap z ∈ D₂.valuationSubring ↔ z ∈ D₁.valuationSubring := by
  rw [← H.comap_valuationSubring]
  rfl

/-- A morphism of slice traits preserves the order of the valuations. -/
lemma valuation_ΩMap_le_iff (y z : D₁.Ω) :
    D₂.valuationSubring.valuation (H.ΩMap y) ≤ D₂.valuationSubring.valuation (H.ΩMap z) ↔
      D₁.valuationSubring.valuation y ≤ D₁.valuationSubring.valuation z := by
  by_cases hz : z = 0
  · subst hz
    simp only [map_zero, le_zero_iff, Valuation.zero_iff, map_eq_zero_iff _ H.ΩMap.injective]
  · have hz' : H.ΩMap z ≠ 0 := (map_ne_zero_iff _ H.ΩMap.injective).2 hz
    have e₁ : D₁.valuationSubring.valuation y ≤ D₁.valuationSubring.valuation z ↔
        D₁.valuationSubring.valuation (y / z) ≤ 1 := by
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hz)]
    have e₂ : D₂.valuationSubring.valuation (H.ΩMap y) ≤
        D₂.valuationSubring.valuation (H.ΩMap z) ↔
        D₂.valuationSubring.valuation (H.ΩMap (y / z)) ≤ 1 := by
      rw [map_div₀ H.ΩMap, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hz')]
    rw [e₁, e₂, ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
      H.ΩMap_mem_valuationSubring_iff]

lemma valuation_ΩMap_le_one_iff (y : D₁.Ω) :
    D₂.valuationSubring.valuation (H.ΩMap y) ≤ 1 ↔ D₁.valuationSubring.valuation y ≤ 1 := by
  simpa using H.valuation_ΩMap_le_iff y 1

lemma valuation_ΩMap_lt_iff (y z : D₁.Ω) :
    D₂.valuationSubring.valuation (H.ΩMap y) < D₂.valuationSubring.valuation (H.ΩMap z) ↔
      D₁.valuationSubring.valuation y < D₁.valuationSubring.valuation z := by
  rw [← not_le, ← not_le, H.valuation_ΩMap_le_iff]

lemma valuation_ΩMap_lt_one_iff (y : D₁.Ω) :
    D₂.valuationSubring.valuation (H.ΩMap y) < 1 ↔ D₁.valuationSubring.valuation y < 1 := by
  simpa using H.valuation_ΩMap_lt_iff y 1

lemma valuation_ΩMap_eq_one_iff (y : D₁.Ω) :
    D₂.valuationSubring.valuation (H.ΩMap y) = 1 ↔ D₁.valuationSubring.valuation y = 1 := by
  have h := H.valuation_ΩMap_le_iff 1 y
  rw [map_one, map_one, map_one] at h
  rw [le_antisymm_iff, le_antisymm_iff, H.valuation_ΩMap_le_one_iff, h]

end AlgebraicGeometry.SliceTrait.Hom
