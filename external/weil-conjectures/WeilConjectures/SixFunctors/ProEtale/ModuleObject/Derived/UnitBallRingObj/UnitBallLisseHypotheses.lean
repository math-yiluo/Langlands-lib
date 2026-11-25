/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseHypotheses

/-!
# The closed unit ball coefficients satisfy the hypotheses of the closure of `Dᵇc` under `RHom`

Let `E` be a finite normed extension of `ℚ_ℓ` and `O ⊆ E` its closed unit ball. The coefficient
ring `O̲ = Profinite.continuousMapRingObj O` satisfies `ProEtale.CondensedRing.LisseHypotheses`
(`ProEtale.CondensedRing.UnitBallRingObj.lisseHypotheses`).

Choose an embedding `E → ℚ̄_ℓ` of `ℚ_ℓ`-algebras. By the uniqueness of the norm on a finite
extension of the complete field `ℚ_ℓ`, the norm of `E` is the norm restricted from `ℚ̄_ℓ`
(`PadicAlgCl.normedFieldOfAlgebra`), so `O̲` is the coefficient ring `𝒪̲_E` of
`ProEtale.CondensedRing.PadicIntegersRingObj.lisseHypotheses`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]
/-- Two normed field structures with the same underlying field and the same norm are equal. -/
lemma normedField_ext {E : Type*} {N₁ N₂ : NormedField E} (hf : N₁.toField = N₂.toField)
    (hn : ∀ x, N₁.norm x = N₂.norm x) : N₁ = N₂ := by
  cases N₁
  cases N₂
  rename_i n₁ f₁ m₁ d₁ _ n₂ f₂ m₂ d₂ _
  obtain rfl : n₁ = n₂ := by cases n₁; cases n₂; exact congrArg _ (funext hn)
  obtain rfl : f₁ = f₂ := hf
  obtain rfl : m₁ = m₂ := MetricSpace.ext (by ext x y; exact (d₁ x y).trans (d₂ x y).symm)
  rfl

/-- `LisseHypotheses` for `integralCoeff ℓ E` only depends on the normed field structure of `E`
up to equality. -/
private lemma lisseHypotheses_integralCoeff_of_eq {E : Type} (N₁ N₂ : NormedField E)
    (A₁ : @NormedAlgebra ℚ_[ℓ] E _
      (@NormedRing.toSeminormedRing E (@NormedCommRing.toNormedRing E N₁.toNormedCommRing)))
    (h : N₁ = N₂)
    (H : ∀ A₂ : @NormedAlgebra ℚ_[ℓ] E _
      (@NormedRing.toSeminormedRing E (@NormedCommRing.toNormedRing E N₂.toNormedCommRing)),
      LisseHypotheses (@integralCoeff.{u} ℓ _ E N₂ A₂)) :
    LisseHypotheses (@integralCoeff.{u} ℓ _ E N₁ A₁) := by
  subst h
  exact H A₁

/-- The integral coefficient ring `integralCoeff ℓ E` of a finite normed extension `E` of `ℚ_ℓ`
satisfies `ProEtale.CondensedRing.LisseHypotheses`: for an embedding `E → ℚ̄_ℓ`, it is the ring
`𝒪̲_E` of `PadicIntegersRingObj.lisseHypotheses`, the norm of `E` being the norm restricted from
`ℚ̄_ℓ`. -/
theorem lisseHypotheses_integralCoeff (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] : LisseHypotheses (integralCoeff.{u} ℓ E) := by
  let σ : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let : Algebra E (PadicAlgCl ℓ) := σ.toRingHom.toAlgebra
  have : IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (σ.commutes x).symm
  have hn (x : E) : ‖x‖ = ‖algebraMap E (PadicAlgCl ℓ) x‖ := by
    rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ] x]
    refine (spectralNorm_unique_field_norm_ext
      (f := (NormedField.toAbsoluteValue (PadicAlgCl ℓ)).comp
        (algebraMap E (PadicAlgCl ℓ)).injective) (fun c ↦ ?_) x).symm
    change ‖algebraMap E (PadicAlgCl ℓ) (algebraMap ℚ_[ℓ] E c)‖ = ‖c‖
    rw [← IsScalarTower.algebraMap_apply, PadicAlgCl.norm_extends]
  exact lisseHypotheses_integralCoeff_of_eq ℓ _ (PadicAlgCl.normedFieldOfAlgebra ℓ E) _
    (normedField_ext rfl hn) fun _ ↦ PadicIntegersRingObj.lisseHypotheses.{u} ℓ E

namespace UnitBallRingObj

/-- The coefficient ring `O̲ = Profinite.continuousMapRingObj O`, for the closed unit ball `O` of a
finite normed extension `E` of `ℚ_ℓ`, satisfies `ProEtale.CondensedRing.LisseHypotheses`. -/
theorem lisseHypotheses {E : Type} [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)] :
    LisseHypotheses (Profinite.continuousMapRingObj.{u} O) := by
  have hO := hO.out
  have he : O = continuousIntegers ℓ E := by
    ext x
    rw [hO]
    change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
    simpa only [NNReal.coe_one, coe_nnnorm] using
      (NNReal.coe_le_coe : (‖x‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1)
  subst O
  exact lisseHypotheses_integralCoeff ℓ E

end UnitBallRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
