/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMono.Basic
public import WeilConjectures.Tactic.FirstOrderApply

/-!
# Split restricted base change maps: from `𝒪_E` to `E`

Flat extension of scalars along `𝒪_E ⟶ E` carries split restricted base change maps to split
restricted base change maps
(`ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_padicSubfield_of_padicIntegers`).
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

/-- **From `𝒪_E` to `E` for split restricted base change maps**, for quasi-compact
quasi-separated vertical maps and a bounded below `K₀`. -/
theorem isSplitMono_map_baseChangeMap_app_padicSubfield_of_padicIntegers [QuasiCompact p]
    [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p'] (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) (hn : K₀.IsGE n)
    (h : IsSplitMono ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map
      ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
        (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀))) :
    IsSplitMono ((L((i)^*⟦Profinite.continuousMapRingObj E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p')
      (pullbackSquareComparison (Profinite.continuousMapRingObj E.1) sq)).app
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          X)).leftDerivedFunctor.obj K₀))) := by
  have := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1) g' K₀ n
  have hE := isSplitMono_map_baseChangeMap_app_derivedExtendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) (derivedPullIsoCompCoherence _) sq i K₀
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p K₀ n)
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p'
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀) n)
    (by transport_mod_proofs h)
  fo_apply hE using

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
