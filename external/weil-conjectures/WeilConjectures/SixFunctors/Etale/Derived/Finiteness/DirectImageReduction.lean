/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-!
# Direct images of the torsion coefficients as reductions of one integral direct image

Let `Λ` be a ring (for instance `𝒪_E`) and `ϖ` a nonzerodivisor of `Λ`, with
`Λₙ = Λ ⧸ ϖⁿ`. For any morphism `g : T ⟶ Y`, the derived direct images of the constant
coefficients `Λₙ` are the reductions of the single object `Rg_* Λ_T` of `D(Y_ét, Λ)`:

`Rg_* (Λₙ)_T ≅ Rg_* Λ_T ⊗ᴸ (Λₙ)_Y`

(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_constantSingle_quotient`). Indeed
`(Λₙ)_T = Λ_T ⊗ᴸ (Λₙ)_T` is the cone of `ϖⁿ` on `Λ_T` and the triangulated `Λ`-linear functor
`Rg_*` commutes with such cones
(`AlgebraicGeometry.Etale.nonempty_iso_map_reductionModIdeal`). In particular the cohomology
of the stalks of the `Rg_*(Λₙ)` is computed by the Bockstein sequences of one complex, which is
the input of `ModuleCat.finite_limit_of_exact_tateSubmodule`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The reduction of the constant complex: `Λ_X ⊗ᴸ (Λ ⧸ J)_X ≅ (Λ ⧸ J)_X`. -/
noncomputable def reductionModIdealConstantComplexIso (X : Scheme.{u}) (J : Ideal Λ) :
    (reductionModIdeal Λ X J).obj (constantComplex Λ X) ≅
      constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J)) :=
  derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _

/-- **Coefficient base change for torsion direct images.** For a nonzerodivisor `ϖ` of `Λ` and
any morphism `g : T ⟶ Y`, `Rg_*((Λ ⧸ ϖⁿ)_T) ≅ Rg_*(Λ_T) ⊗ᴸ (Λ ⧸ ϖⁿ)_Y` in `D(Y_ét, Λ)`. -/
theorem nonempty_iso_rightDerivedLowerStar_constantSingle_quotient {T Y : Scheme.{u}}
    (g : T ⟶ Y) {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) :
    Nonempty ((R((g)_*[ModuleCat.{u + 1} Λ])).obj
        (constantSingle (ModuleCat.{u + 1} Λ) T (ModuleCat.of Λ (Λ ⧸ Ideal.span {ϖ} ^ n))) ≅
      (reductionModIdeal Λ Y (Ideal.span {ϖ} ^ n)).obj
        ((R((g)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ T))) := by
  obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal (R((g)_*[ModuleCat.{u + 1} Λ])) hϖ n
    (constantComplex Λ T)
  exact ⟨(R((g)_*[ModuleCat.{u + 1} Λ])).mapIso
    (reductionModIdealConstantComplexIso T _).symm ≪≫ e⟩

end AlgebraicGeometry.Etale
