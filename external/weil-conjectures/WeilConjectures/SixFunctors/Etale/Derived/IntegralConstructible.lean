/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CohomologicalSupport
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-!
# Bounded constructible derived-complete integral coefficients

The blueprint defines the integral stage `Dᵇc(Y, 𝒪_E)` as the derived complete objects `K` all of
whose reductions `K ⊗ᴸ_{𝒪_E} A_{E,n}` are bounded constructible, with cohomological supports
(`DerivedCategory.cohomologicalSupport`, blueprint `def-weil-cohomological-support`) contained in
one interval `[r, s]` independent of `n`.

As everywhere in the repository (see
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`), the integral stage is
realised on the small étale site with coefficients in the discrete ring `Λ = 𝒪_E` and the ideal
`I = 𝔪_E`: the reductions are `AlgebraicGeometry.Etale.reductionModIdeal Λ X (I ^ (n + 1))`, the
objects `K ⊗ᴸ (Λ/Iⁿ⁺¹)_X` regarded as `Λ`-module complexes, which is the blueprint's
`Res_n (K ⊗ᴸ A_{E,n})` inside the single category `D(Y, 𝒪_E)`.

The repository's working definition
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`
asks for a uniform *Tor amplitude* of the reductions instead of a uniform cohomological support.
Tor amplitude in `[a, b]` bounds the support by `[a, b]`, so it is contained in the blueprint's
category (`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral_le`); the
converse is the residue-field argument of the blueprint's remark in
`definition-constructible-sheaves`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegralOfSupport`: the
  blueprint's `Dᵇc(Y, 𝒪_E)`, as an object property of `D(Y_ét, Λ)`.
- `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructibleIntegralOfSupport`: the
  corresponding full subcategory.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral_le`: the working
  definition is contained in the blueprint's.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_integralConstructible
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) (X : Scheme.{u})

/-- Bounded constructible derived-complete integral coefficients.

An object `K` of `D(Y, Λ)`, `Λ = 𝒪_E` and `I = 𝔪_E`, lies in `Dᵇc(Y, 𝒪_E)` if it is derived
complete for `I`, every reduction `K ⊗ᴸ (Λ/Iⁿ⁺¹)_Y` is bounded constructible, and the
cohomological supports of all the reductions lie in one interval `[r, s]` independent of `n`.
The uniform support is the only boundedness condition imposed. -/
def DerivedCategory.boundedConstructibleIntegralOfSupport :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I K ∧
    (∀ n : ℕ, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) ∧
    ∃ r s : ℤ, ∀ n : ℕ, _root_.DerivedCategory.cohomologicalSupport
      ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) ⊆ Set.Icc r s

/-- The blueprint's `Dᵇc(Y, 𝒪_E)` as a full subcategory of `D(Y_ét, 𝒪_E)`. -/
abbrev DerivedCategoryBoundedConstructibleIntegralOfSupport :=
  (DerivedCategory.boundedConstructibleIntegralOfSupport I X).FullSubcategory

variable {I X}

/-- The uniform support condition is equivalently a uniform homology concentration. -/
lemma DerivedCategory.boundedConstructibleIntegralOfSupport_iff
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.boundedConstructibleIntegralOfSupport I X K ↔
      _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I K ∧
      (∀ n : ℕ, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) ∧
      ∃ r s : ℤ, ∀ n : ℕ, _root_.DerivedCategory.homologyConcentratedIn r s
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) := by
  simp only [DerivedCategory.boundedConstructibleIntegralOfSupport,
    _root_.DerivedCategory.cohomologicalSupport_subset_Icc_iff]

/-- The working definition `DerivedCategory.boundedConstructibleIntegral` of the repository,
with a uniform Tor amplitude of the reductions, is contained in the blueprint's `Dᵇc(Y, 𝒪_E)`:
Tor amplitude in `[a, b]` bounds the cohomological support by `[a, b]`. -/
lemma DerivedCategory.boundedConstructibleIntegral_le :
    DerivedCategory.boundedConstructibleIntegral I X ≤
      DerivedCategory.boundedConstructibleIntegralOfSupport I X := by
  rintro K ⟨hc, a, b, h⟩
  refine (DerivedCategory.boundedConstructibleIntegralOfSupport_iff K).2
    ⟨hc, fun n ↦ (h n).1, a, b, fun n ↦ ?_⟩
  exact _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn (h n).2

end Etale

end AlgebraicGeometry
