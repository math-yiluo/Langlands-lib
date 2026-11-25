/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.RetractionLift

/-!
# Split restricted base change maps from unique torsion retractions

For a commutative square `sq : g' ≫ p' = p ≫ g` of quasi-compact quasi-separated schemes,
`i : Z ⟶ Y'` and a derived complete `𝒪_E`-complex `K₀`, the restricted base change map
`Li^* BC_sq(K₀)` with `𝒪_E`-coefficients is a split monomorphism if it has unique torsion
retractions (`ProEtale.CondensedRing.HasUniqueTorsionRetractions`): its reductions modulo `ℓⁿ⁺¹`
have unique retractions with a property preserved by reduction. This follows from
`ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`: the source
`Li^* Lg^* Rp_* K₀` is derived complete.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- A morphism `i : A ⟶ B` of `𝒪_E`-complexes **has unique torsion retractions** if there is a
property `Pₙ` of morphisms `B ⊗ᴸ 𝒪_E/ℓⁿ⁺¹ ⟶ A ⊗ᴸ 𝒪_E/ℓⁿ⁺¹` such that each reduction
`i ⊗ᴸ 𝒪_E/ℓⁿ⁺¹` has a unique retraction with property `Pₙ`, and the reduction modulo `ℓⁿ⁺¹` of a
retraction with property `Pₙ₊₁` has property `Pₙ`. For nearby cycles, `Pₙ` is the invariance under
the inertia group (SGA 4½, [Th. finitude], Lemme 3.4). -/
def HasUniqueTorsionRetractions
    {A B : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))} (i : A ⟶ B) : Prop :=
  ∃ P : ∀ n, (L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).obj B ⟶
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).obj A) → Prop,
    (∀ n, ∃ r, P n r ∧
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).map i ≫ r = 𝟙 _) ∧
    (∀ n r r', P n r → P n r' →
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).map i ≫ r = 𝟙 _ →
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1))).map i ≫ r' = 𝟙 _ →
      r = r') ∧
    (∀ n r, P (n + 1) r →
      L(Mod.extendScalars (integersModPowReduction Z ℓ E.1 (n + 1 + 1))).map i ≫ r = 𝟙 _ →
      P n (Mod.derivedExtendScalarsReduction (integersModPowReduction Z ℓ E.1 (n + 1 + 1))
        (modPowTransition Z ℓ E.1 (n + 1)) (integersModPowReduction Z ℓ E.1 (n + 1))
        (integersModPowReduction_comp_modPowTransition Z ℓ E.1 (n + 1)) r))

variable {ℓ E} in
/-- A morphism from a derived complete complex with unique torsion retractions is a split
monomorphism (`ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`). -/
theorem HasUniqueTorsionRetractions.isSplitMono
    {A B : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))} {i : A ⟶ B}
    (h : HasUniqueTorsionRetractions ℓ E i) (hA : derivedCompleteIntegers ℓ E Z A) :
    IsSplitMono i := by
  obtain ⟨P, hex, huniq, hred⟩ := h
  exact isSplitMono_of_derivedCompleteIntegers_of_unique_retractions i hA P hex huniq hred

/-- **Lifting unique torsion retractions of the restricted base change map to `𝒪_E`**: for
quasi-compact quasi-separated schemes and a derived complete `K₀`, the restricted base change map
`Li^* BC_sq(K₀)` with `𝒪_E`-coefficients is a split monomorphism if it has unique torsion
retractions. -/
theorem isSplitMono_map_baseChangeMap_app_padicIntegers_of_hasUniqueTorsionRetractions
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Z] [QuasiSeparatedSpace Z] (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK₀ : derivedCompleteIntegers ℓ E X K₀)
    (h : HasUniqueTorsionRetractions ℓ E ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map
      ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
        (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀))) :
    IsSplitMono ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀)) :=
  h.isSplitMono (derivedCompleteIntegers_leftDerivedUpperStar_obj i
    (derivedCompleteIntegers_leftDerivedUpperStar_obj g
      (derivedCompleteIntegers_rightDerivedLowerStar_obj p hK₀)))

end AlgebraicGeometry.ProEtale.CondensedRing
