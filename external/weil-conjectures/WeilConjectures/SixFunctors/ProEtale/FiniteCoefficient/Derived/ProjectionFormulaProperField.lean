/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormulaBounded
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers

/-!
# The proper projection formula for bounded constructible complexes over a finite field

Let `Λ` be a finite field and `g : Z ⟶ Y` a proper morphism of schemes. For bounded
constructible complexes `N` on `Z_proét` and `L` on `Y_proét` with coefficients in `Λ` (that is,
of the form `ν^* N₀` and `ν^* L₀` for bounded constructible complexes of étale sheaves), the
projection map `Rg_* N ⊗ᴸ L ⟶ Rg_*(N ⊗ᴸ Lg^* L)` is an isomorphism
(`ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_boundedConstructible_of_field`).

It is the étale projection formula for proper morphisms with finite coefficients
(`Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`) transported along `ν^*`
(`ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived`); the boundedness of
`N₀ ⊗ᴸ Lg^* L₀` comes from the finite Tor amplitude of bounded complexes over a field.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **The proper projection formula over a finite field**
(`proposition-proper-direct-image-constructible-complexes--9`, at the finite stage `𝔽_E`): for a
finite field `Λ`, a proper `g : Z ⟶ Y` and bounded constructible complexes `N` on `Z_proét` and `L`
on `Y_proét` with coefficients in `Λ`, the projection map `Rg_* N ⊗ᴸ L ⟶ Rg_*(N ⊗ᴸ Lg^* L)` is an
isomorphism. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_of_boundedConstructible_of_field
    (hΛ : IsField Λ) {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]
    {N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hN : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z N)
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y L) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app N).app L) := by
  obtain ⟨N₀, hN₀, ⟨eN⟩⟩ := (DerivedCategory.boundedConstructible_iff _ _ N).1 hN
  obtain ⟨L₀, hL₀, ⟨eL⟩⟩ := (DerivedCategory.boundedConstructible_iff _ _ L).1 hL
  -- `L₀` has finite Tor amplitude since `Λ` is a field
  obtain ⟨a, b, hL₀t⟩ : Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) Y L₀ := by
    let := hΛ.toField
    exact Etale.DerivedCategory.finiteTorAmplitude_of_boundedConstructible_of_field Λ Y hL₀
  have hML := Etale.plus_derivedTensor_leftDerivedUpperStar g hN₀.1 hL₀t
  -- the étale projection formula for the proper `g`
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite Λ g
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived (ModuleCat.{u + 1} Λ) g
    N₀ L₀ hN₀.1.1 hML
  exact NatTrans.isIso_app_app_of_iso
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g)
    ((ν^*(Z)[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory.app N₀ ≪≫ eN)
    ((ν^*(Y)[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory.app L₀ ≪≫ eL)

end AlgebraicGeometry.ProEtale
