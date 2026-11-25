/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.IntegralCoefficientCohomology

/-!
# Geometric Frobenius on the coefficient twists, stage `E`

At the stage `Λ = E` of a subfield `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the Tate twisted constant `E`-Weil sheaf
`E_X(m)` (`AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant`) is the constant `E`-Weil sheaf
`E_X` with its Weil structure multiplied by a scalar `c ∈ Eˣ` whose image in `ℚ̄_ℓ` is `q^{-m}`:
geometric Frobenius acts on `E(1)` by `q⁻¹`, on `E(m)` by `q^{-m}` and on `E(-m)` by `q^m`
(blueprint `prose-10-21`). The scalar is the image of the twisting unit
`χ_ℓ(σ)ᵐ ∈ 𝒪_Eˣ` of the integral stage, so the action commutes with finite reduction and with
scalar extension to `ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FieldWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (E : IntermediateField ℚ_[l] (PadicAlgCl l))

/-- Blueprint `prose-10-21`: Frobenius on coefficient twists, stage
`E`.

Geometric Frobenius acts on the Tate twist `E(m)` by `q^{-m}`, for every `m ∈ ℤ`: as an `E`-Weil
sheaf, `E_X(m)` is the constant Weil twist of the constant sheaf `E_X` by a scalar `c ∈ Eˣ`
whose image in `ℚ̄_ℓ` is `q^{-m}` (so by `q⁻¹` on `E(1)` and by `q^m` on `E(-m)`). The scalar is
the image under `𝒪_E ⊆ E` of the twisting unit `χ_ℓ(σ)ᵐ` of the integral stage
(`AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant_eq_constantTwist`), and its image in `ℚ̄_ℓ`
is the twisting scalar of the stage `ℚ̄_ℓ`
(`AlgebraicGeometry.WeilSheaf.exists_tateTwistSheaf_iso_constantTwist`). -/
theorem exists_tateTwistConstant_eq_constantTwist (m : ℤ) :
    ∃ c : (↥E)ˣ, algebraMap E (PadicAlgCl l) (c : E) = (Nat.card k₀ : PadicAlgCl l) ^ (-m) ∧
      tateTwistConstant k₀ X E m = (constant k₀ E X).constantTwist c := by
  refine ⟨_, ?_, tateTwistConstant_eq_constantTwist E m⟩
  rw [map_zpow, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.coe_map]
  change algebraMap E (PadicAlgCl l)
      ((ProEtaleIntegralWeilSheaf.cyclotomicUnit k₀ E : PadicAlgCl.integers l E) : E) ^ m = _
  rw [ProEtaleIntegralWeilSheaf.cyclotomicUnit_eq, inv_zpow', zpow_neg]

/-- Blueprint `prose-10-21`: in particular geometric Frobenius acts on
`E(-d)` by multiplication by `q^d`, for `d ∈ ℤ_{≥ 0}`. -/
theorem exists_tateTwistConstant_neg_eq_constantTwist (d : ℕ) :
    ∃ c : (↥E)ˣ, algebraMap E (PadicAlgCl l) (c : E) = (Nat.card k₀ : PadicAlgCl l) ^ d ∧
      tateTwistConstant k₀ X E (-d) = (constant k₀ E X).constantTwist c := by
  simpa using exists_tateTwistConstant_eq_constantTwist k₀ X E (-d)

end AlgebraicGeometry.FieldWeilSheaf
