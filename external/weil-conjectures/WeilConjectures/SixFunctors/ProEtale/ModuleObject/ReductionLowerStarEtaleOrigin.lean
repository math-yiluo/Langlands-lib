/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Reduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportDerived

/-!

# The reduction of a direct image is of étale origin

For a quasi-compact quasi-separated morphism `f : X ⟶ Y` and a bounded below complex `K` of
`𝒪_{E,X}`-modules whose first derived reduction `K ⊗ᴸ 𝔽_E` is of étale origin, the first derived
reduction of `Rf_* K` is of étale origin
(`ProEtale.CondensedRing.plusEtaleOrigin_derivedReduction_rightDerivedLowerStar_obj`): the
reduction commutes with `Rf_*` on bounded below complexes
(`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`,
`ProEtale.isIso_residueFieldDerivedPushHom`), and `Rf_*` preserves complexes of étale origin
(`ProEtale.DerivedCategory.plusEtaleOrigin_rightDerivedLowerStar_obj`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
  [QuasiCompact f] [QuasiSeparated f]

/-- For `f` quasi-compact and quasi-separated and a bounded below `𝒪_E`-complex `K` whose first
derived reduction is of étale origin, the first derived reduction of `Rf_* K` is of étale
origin. -/
theorem plusEtaleOrigin_derivedReduction_rightDerivedLowerStar_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [K.IsGE n]
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X
      ((derivedReduction X ℓ E).obj K)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Y
      ((derivedReduction Y ℓ E).obj
        ((R((f)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K)) := by
  have h₁ := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E f K n
  have h₂ := DerivedCategory.plusEtaleOrigin_rightDerivedLowerStar_obj
    (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f hK
  refine ObjectProperty.prop_of_iso _ ?_ h₂
  exact ((residueFieldModuleSheaf Y ℓ E).mapDerivedCategory.mapIso
      (asIso ((derivedUpperStarExtendScalarsPushHom
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) f).app K)) ≪≫
    asIso ((residueFieldDerivedPushHom ℓ E f).app
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))).symm

end AlgebraicGeometry.ProEtale.CondensedRing
