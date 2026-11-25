/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeTest
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaConstant
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatIdeal

/-!
# Direct image and finite Tor amplitude

Let `f : X ⟶ Y` be a morphism of schemes and `Λ` a noetherian commutative ring such that the
higher direct images of `f` vanish above `N` on every sheaf of `Λ`-modules (`UDV(f, Λ; N)`,
`definition-cohomological-dimension--2`). Then `Rf_*` sends an object of Tor amplitude in
`[a, b]` to an object of Tor amplitude in `[a, b + N]`
(`Etale.torAmplitudeIn_rightDerivedLowerStar_of_hasUniformDirectImageVanishingLE`).

## Proof

The object `K` is concentrated in `[a, b]`, so `Rf_* K` is concentrated in `[a, b + N]`. Flatness
of an étale sheaf is tested on the inclusions `I_Y ⟶ Λ_Y` of ideals
(`AlgebraicGeometry.Etale.flat_of_forall_mono_whiskerLeft`), so by the Tor amplitude test
`DerivedCategory.torAmplitudeIn_of_forall_isGE` it suffices that every `Rf_* K ⊗ᴸ (Λ/I)_Y` lies
in degrees `≥ a`. By the projection formula with the finitely generated constant coefficient
`Λ/I` (`proposition-open-direct-image-preserves-finite--1`) this is `Rf_*(K ⊗ᴸ (Λ/I)_X)`, the direct
image of an object concentrated in `[a, b]`. This is the residue-field test of the blueprint
(`theorem-f-shriek-finite-coefficients--1`), with the quotients `Λ/I` in place of the residue field:
it needs neither the stalks of complexes nor minimal resolutions, and no constructibility.

## Main results

- `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_hasUniformDirectImageVanishingLE`
- `AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar`
  (`proposition-six-operations-dctf--2`)
- `AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_two_mul`
  (`proposition-six-operations-dctf--2`)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The short exact sequence `0 ⟶ I ⟶ Λ ⟶ Λ/I ⟶ 0` of `Λ`-modules attached to an ideal. -/
noncomputable def idealShortComplex (I : Ideal Λ) : ShortComplex (ModuleCat.{u + 1} Λ) :=
  ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero

lemma idealShortComplex_shortExact (I : Ideal Λ) : (idealShortComplex I).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ I) I.injective_subtype
    (Submodule.mkQ_surjective I)

/-- **Direct image and Tor amplitude under uniform vanishing.** Let `Λ` be a noetherian
commutative ring and `f : X ⟶ Y` a morphism of schemes with `UDV(f, Λ; N)`: `Rᵠf_* F = 0` for
every sheaf of `Λ`-modules `F` on `X_ét` and every `q > N`. If `K ∈ D(X_ét, Λ)` has Tor amplitude
in `[a, b]`, then `Rf_* K` has Tor amplitude in `[a, b + N]`. -/
theorem torAmplitudeIn_rightDerivedLowerStar_of_hasUniformDirectImageVanishingLE
    [IsNoetherianRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (hf : HasUniformDirectImageVanishingLE Λ f N)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a b : ℤ}
    (hK : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + N)
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨_, _⟩ := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hK
  have := isGE_rightDerivedLowerStar_obj _ f K a
  have := isLE_rightDerivedLowerStar_obj_of_isZero_higherDirectImage
    (fun F q hq ↦ hf F q (by exact_mod_cast hq)) K b
  let S (I : Ideal Λ) : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (idealShortComplex I).map (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  refine _root_.DerivedCategory.torAmplitudeIn_of_forall_isGE S
    (fun I ↦ (idealShortComplex_shortExact I).map_of_exact _)
    (fun F hF ↦ flat_of_forall_mono_whiskerLeft F hF) fun I ↦ ?_
  -- `Rf_* K ⊗ᴸ (Λ/I)_Y ≅ Rf_*(K ⊗ᴸ (Λ/I)_X)` lies in degrees `≥ a`
  let Q := ModuleCat.of Λ (Λ ⧸ I)
  have := isIso_rightDerivedLowerStarProjectionMap_constantSheaf f N hf hK Q
  obtain ⟨_, _⟩ := hK ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj Q)
  have := isGE_rightDerivedLowerStar_obj _ f (K ⊗ constantSingle (ModuleCat.{u + 1} Λ) X Q) a
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso
    ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
      (whiskerLeftIso K (leftDerivedUpperStarSingleConstantSheafIso _ f Q)).symm ≪≫
    (asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y Q))).symm) a

end Etale

end AlgebraicGeometry
