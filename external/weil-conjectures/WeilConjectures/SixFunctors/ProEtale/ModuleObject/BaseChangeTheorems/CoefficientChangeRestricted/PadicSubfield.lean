/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.Basic
public import WeilConjectures.Tactic.FirstOrderApply

/-!
# Coefficient change for restricted base change maps: from `𝒪_E` to `E`

The invertibility of the restricted base change map
`Li^* BC_sq(K) : Li^* Lg^* Rp_* K ⟶ Li^* Rp'_* Lg'^* K` passes from `𝒪_E` to `E` by flat
extension of scalars
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicSubfield_of_padicIntegers`).
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

/-- **From `𝒪_E` to `E` for the restricted base change map**: for quasi-compact quasi-separated
vertical maps, if the restricted base change map with `𝒪_E`-coefficients is invertible at a
bounded below `K₀`, then the one with `E`-coefficients is invertible at `E ⊗ᴸ_{𝒪_E} K₀`. -/
theorem isIso_map_baseChangeMap_app_padicSubfield_of_padicIntegers [QuasiCompact p]
    [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p'] (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) (hn : K₀.IsGE n)
    (h : IsIso ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀))) :
    IsIso ((L((i)^*⟦Profinite.continuousMapRingObj E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p')
      (pullbackSquareComparison (Profinite.continuousMapRingObj E.1) sq)).app
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          X)).leftDerivedFunctor.obj K₀))) := by
  have := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1) g' K₀ n
  have hE := isIso_map_baseChangeMap_app_derivedExtendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) (derivedPullIsoCompCoherence _) sq i K₀
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p K₀ n)
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p'
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀) n)
    (by transport_mod_proofs h)
  fo_apply hE using

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
