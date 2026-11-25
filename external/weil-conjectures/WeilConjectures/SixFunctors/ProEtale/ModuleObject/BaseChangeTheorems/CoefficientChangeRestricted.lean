/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.PadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.PadicSubfield
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.ResidueField

/-!

# Coefficient change for restricted base change maps

For a commutative square `sq : g' ≫ p' = p ≫ g` and a morphism `i : Z ⟶ Y'`, consider the
*restricted base change map* `Li^* (Lg^* Rp_* K ⟶ Rp'_* Lg'^* K)`, the base change map followed by
the pullback along `i` (for nearby cycles: the base change of `Rj_*` restricted to the special
fibre). This file shows that it is compatible with the change of coefficients
`𝔽_E ⟵ 𝒪_E ⟶ E ⟶ ℚ̄_ℓ`:

* `ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app`:
  extension of scalars along any `a : Λ ⟶ Λ'` carries the restricted base change map at `K` to
  the one at `T K`, if the pushforwards commute with `T` at `K` and `Lg'^* K`;
* `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicIntegers_of_residueField`
  (derived Nakayama): with `𝒪_E`-coefficients, the restricted base change map at a derived
  complete bounded below `K` is invertible if it is invertible with `𝔽_E`-coefficients at
  `𝔽_E ⊗ᴸ K`;
* `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicSubfield_of_padicIntegers` and
  `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_padicSubfield`: the
  invertibility passes from `𝒪_E` to `E` to `ℚ̄_ℓ` by flat extension of scalars.

These are proved in the files of the directory `CoefficientChangeRestricted`, one per coefficient
change; this file combines them along an integral model
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_integral`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The `ℚ̄_ℓ`-restricted base change map from integral models**: for quasi-compact
quasi-separated vertical maps and a topologically noetherian `X`, the restricted base change map
with `ℚ̄_ℓ`-coefficients is invertible at a bounded constructible `K` as soon as, for every finite
subextension `E ⊆ ℚ̄_ℓ`, the one with `𝒪_E`-coefficients is invertible at every bounded
constructible `𝒪_E`-complex: `K ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for an integral model `K₀`
(`ProEtale.exists_padicAlgCl_iso_integralModel`). -/
theorem isIso_map_baseChangeMap_app_padicAlgCl_of_integral [TopologicalSpace.NoetherianSpace X]
    [QuasiCompact p] [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p']
    (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hK : boundedConstructible _ K)
    (h : ∀ (E : FiniteIntermediateField ℓ) (K₀ : DerivedCategory (Mod
      (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))),
      boundedConstructible _ K₀ →
        IsIso ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
          (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀))) :
    IsIso ((L((i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p')
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq)).app K)) := by
  obtain ⟨E, K₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel X ℓ ⟨K, hK⟩
  -- the integral model as an object of the ambient derived category, `ℚ̄_ℓ ⊗ (E ⊗ K₀) ≅ K`
  have hobj : (ObjectProperty.ι _).obj (⟨K, hK⟩ : PadicAlgClConstructible X ℓ) = K := rfl
  have i₁ := (ObjectProperty.liftCompιIso (boundedConstructible (padicAlgClRingObj X ℓ))
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K)).app
      ((boundedConstructibleExtendScalars X ℓ E).obj K₀)
  have i₂ := (derivedExtendScalarsToPadicAlgCl X ℓ E).mapIso
    ((boundedConstructibleExtendScalarsCompatibility X ℓ E).app K₀)
  have e' := Nonempty.intro ((i₁ ≪≫ i₂).symm ≪≫ (ObjectProperty.ι _).mapIso e ≪≫ eqToIso hobj)
  have hK₀ : boundedConstructible _ K₀.obj := by exact_mod_proofs K₀.property
  obtain ⟨n, hn⟩ := hK₀.1.1
  have hE := isIso_map_baseChangeMap_app_padicSubfield_of_padicIntegers ℓ E sq i K₀.obj n hn
    (h E K₀.obj hK₀)
  have hnE := isGE_leftDerivedFunctor_extendScalars_obj
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) K₀.obj n
  have hA := isIso_map_baseChangeMap_app_padicAlgCl_of_padicSubfield ℓ E sq i
    ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      X)).leftDerivedFunctor.obj K₀.obj) n hnE (by exact_mod_proofs hE)
  have hgen := isIso_map_baseChangeMap_app_of_iso_extendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) sq i K₀.obj (K := K)
  -- the hypotheses carry different proofs of `Precoherent Profinite`, which are identified
  clear i₁ i₂ hobj e hK₀ hE hnE
  revert E K₀ n hn hA e' hgen
  normalize_precoherent
  intro E K₀ e' n hn hA hgen
  exact hgen e' hA

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
