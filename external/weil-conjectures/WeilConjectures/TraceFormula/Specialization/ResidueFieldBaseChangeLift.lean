/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerStabilization
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChange
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeIntegral

/-!

# Lifting restricted base change isomorphisms from `𝔽_E` to `ℚ̄_ℓ` at a given integral model

For a commutative square with quasi-compact quasi-separated vertical maps, the restricted base
change map `Li^* (Lg^* Rp_* ⟶ Rp'_* Lg'^*)` with `ℚ̄_ℓ`-coefficients is invertible at
`ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` as soon as the one with `𝔽_E`-coefficients is invertible at
`𝔽_E ⊗ᴸ K₀`, for a derived complete bounded below `𝒪_E`-complex `K₀`
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_residueField`): derived
Nakayama, then flat extension of scalars. Unlike
`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_integral`, this uses a single
integral model, so the square may depend on it.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Generic

variable {Λ₁ Λ₂ Λ₃ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₁]
  [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] [MonObj Λ₃] [IsCommMonObj Λ₃]
  (a : Λ₁ ⟶ Λ₂) [IsMonHom a] (b : Λ₂ ⟶ Λ₃) [IsMonHom b]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b X))]
  {T X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

set_option maxHeartbeats 400000 in
-- the statement involves several large derived functor objects
/-- The restricted base change map with coefficients `Λ₃` is invertible at `Lε^* K` as soon as
it is invertible at `T_b (T_a (Lε^* K₀))` for some `K₀` with `T_b (T_a K₀) ≅ K`. -/
lemma isIso_map_baseChangeMap_app_leftDerivedUpperStar_of_iso_extendScalars
    (sq : CommSq g' p' p g) (i : Z ⟶ Y') (ε : X ⟶ T)
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ₁ T)))
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ₃ T))}
    (e : Nonempty ((Mod.extendScalars (coefficientMap b T)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a T)).leftDerivedFunctor.obj K₀) ≅ K))
    (h : IsIso ((L((i)^*⟦Λ₃⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ₃ p) (derivedUpperStarLowerStarAdjunction Λ₃ p')
      (pullbackSquareComparison Λ₃ sq)).app
        ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
          ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj
            ((L((ε)^*⟦Λ₁⟧)).obj K₀)))))) :
    IsIso ((L((i)^*⟦Λ₃⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ₃ p) (derivedUpperStarLowerStarAdjunction Λ₃ p')
      (pullbackSquareComparison Λ₃ sq)).app ((L((ε)^*⟦Λ₃⟧)).obj K))) :=
  isIso_map_app_of_iso _ _ ((leftDerivedUpperStarExtendScalarsExtendScalarsIso a b ε K₀).symm ≪≫
    (L((ε)^*⟦Λ₃⟧)).mapIso e.some) h

end Generic

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The `ℚ̄_ℓ`-restricted base change map from `𝔽_E`**: for a commutative square with
quasi-compact quasi-separated vertical maps between quasi-compact quasi-separated schemes and a
derived complete bounded below `𝒪_E`-complex `K₀`, the restricted base change map with
`ℚ̄_ℓ`-coefficients is invertible at `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` if the one with
`𝔽_E`-coefficients is invertible at `𝔽_E ⊗ᴸ K₀`: derived Nakayama, then flat extension of
scalars. -/
theorem isIso_map_baseChangeMap_app_padicAlgCl_of_residueField [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Z]
    [QuasiSeparatedSpace Z] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact p']
    [QuasiSeparated p'] (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [K₀.IsGE n]
    (hK₀ : derivedCompleteIntegers ℓ E X K₀)
    (h : IsIso ((L((i)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧)).map
      ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) p)
        (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) p')
        (pullbackSquareComparison
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) sq)).app
        ((Mod.extendScalars (coefficientMap
          (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj K₀)))) :
    IsIso ((L((i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p')
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq)).app
      ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        X)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).leftDerivedFunctor.obj K₀)))) := by
  have h₁ := isIso_map_baseChangeMap_app_padicIntegers_of_residueField ℓ E sq i K₀ n hK₀
    (by exact_mod_proofs h)
  have h₂ := isIso_map_baseChangeMap_app_padicSubfield_of_padicIntegers ℓ E sq i K₀ n
    inferInstance (by exact_mod_proofs h₁)
  have h₃ := isIso_map_baseChangeMap_app_padicAlgCl_of_padicSubfield ℓ E sq i _ n
    (isGE_leftDerivedFunctor_extendScalars_obj
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) K₀ n) (by exact_mod_proofs h₂)
  exact_mod_proofs h₃

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
