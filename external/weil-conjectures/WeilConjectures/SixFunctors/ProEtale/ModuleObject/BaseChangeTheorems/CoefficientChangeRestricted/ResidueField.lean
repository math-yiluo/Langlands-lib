/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.Basic

/-!
# Coefficient change for restricted base change maps: from `𝔽_E` to `𝒪_E`

This file proves derived Nakayama for the restricted base change map
`Li^* BC_sq(K) : Li^* Lg^* Rp_* K ⟶ Li^* Rp'_* Lg'^* K`
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicIntegers_of_residueField`): with
`𝒪_E`-coefficients, it is invertible at a derived complete bounded below `K` if it is invertible
with `𝔽_E`-coefficients at `𝔽_E ⊗ᴸ K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Derived Nakayama for morphisms, via extension of scalars**: a morphism of derived complete
`𝒪_E`-complexes whose extension of scalars to `𝔽_E` is an isomorphism is an isomorphism. -/
theorem isIso_of_derivedCompleteIntegers_of_isIso_extendScalars_map {X : Scheme.{u}}
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} (φ : K ⟶ L)
    (hK : derivedCompleteIntegers ℓ E X K) (hL : derivedCompleteIntegers ℓ E X L)
    (h : IsIso ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map φ)) :
    IsIso φ := by
  obtain ⟨C, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ
  have hF := (Mod.extendScalars
    (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map_distinguished _ hT
  have hC : derivedCompleteIntegers ℓ E X C :=
    derivedCompleteIntegers_ext₂ _ (Pretriangulated.rot_of_distTriang _ hT) hL
      (derivedCompleteIntegers_shift hK 1)
  refine (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction hC ?_)
  rw [isZero_derivedReduction_iff]
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hF).2 h

/-- **Derived Nakayama for the restricted base change map**: with `𝒪_E`-coefficients, the
restricted base change map `Li^* BC_sq(K₀)` at a derived complete bounded below `K₀` is invertible
if the restricted base change map with `𝔽_E`-coefficients is invertible at `𝔽_E ⊗ᴸ K₀`. -/
theorem isIso_map_baseChangeMap_app_padicIntegers_of_residueField [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Z]
    [QuasiSeparatedSpace Z] (sq : CommSq g' p' p g) (i : Z ⟶ Y')
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
    IsIso ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀)) := by
  have : ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀).IsGE n :=
    isGE_leftDerivedUpperStar_obj _ g' K₀ n
  -- elaborating the comparisons against the expected types unfolds the coefficient rings, as
  -- the instances on them differ by proofs of `Precoherent Profinite`: compare them up to proofs
  have k := nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app
    (Profinite.padicIntegersRingObjToResidueField ℓ E.1) sq i K₀ ?h₁ ?h₂
  case h₁ =>
    exact_mod_proofs isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E p K₀ n
  case h₂ =>
    exact_mod_proofs (isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E p'
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀) n)
  have hext := isIso_of_nonempty_arrowIso_of_isIso k (by exact_mod_proofs h)
  have hsrc := derivedCompleteIntegers_leftDerivedUpperStar_obj i
    (derivedCompleteIntegers_leftDerivedUpperStar_obj g
      (derivedCompleteIntegers_rightDerivedLowerStar_obj p hK₀))
  have htgt := derivedCompleteIntegers_leftDerivedUpperStar_obj i
    (derivedCompleteIntegers_rightDerivedLowerStar_obj p'
      (derivedCompleteIntegers_leftDerivedUpperStar_obj g' hK₀))
  exact isIso_of_derivedCompleteIntegers_of_isIso_extendScalars_map ℓ E _ hsrc htgt
    (by exact_mod_proofs hext)

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
