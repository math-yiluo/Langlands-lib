/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedForget
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar

/-!
# The derived pushforward of `ℓ`-adic sheaves on underlying abelian sheaves

The derived pushforward `Rg_*` of `ℓ`-adic sheaves (sheaves of `ℚ̄_ℓ,X`-modules,
`AlgebraicGeometry.ProEtale.AdicSheaf`) commutes with taking underlying complexes:

- `AlgebraicGeometry.ProEtale.mapDerivedCategoryForgetCompRightDerivedLowerStarIso`: with the
  underlying complexes of sheaves of `ℚ̄_ℓ`-modules.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompWeilCoefficientsForgetAbIso`: with the
  underlying complexes of abelian sheaves. The forgetful functor
  `AlgebraicGeometry.ProEtale.weilCoefficientsForgetAb` has the exact left adjoint
  `ℚ̄_ℓ ⊗ -` (`AlgebraicGeometry.ProEtale.weilCoefficientsFreeAdjunction`), `ℚ̄_ℓ` being flat
  over `ℤ`, so it preserves K-injective complexes.
- `AlgebraicGeometry.ProEtale.rightDerivedAdicLowerStarCompForgetAbIso`: the composite.

This is the coefficient bridge between the `ℓ`-adic sheaves of the finiteness theorem
(`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`) and the abelian sheaves `𝒪_{E,X}`,
`E_X`, `ℚ̄_ℓ,X` of `WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafLowerStar`.
-/

@[expose] public section
universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

instance (X : Scheme.{u}) : (weilCoefficientsForgetAb l X).PreservesKInjectiveComplexes := by
  have : (weilCoefficientsFree X l).Additive :=
    (weilCoefficientsFreeAdjunction X l).left_adjoint_additive
  have := (weilCoefficientsFreeAdjunction X l).leftAdjoint_preservesColimits
  have : (weilCoefficientsFree X l).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact (weilCoefficientsFreeAdjunction X l).preservesKInjectiveComplexes

instance (X : Scheme.{u}) : PreservesFiniteLimits (weilCoefficientsForgetAb l X) :=
  have : PreservesLimitsOfSize.{0, 0} (weilCoefficientsForgetAb l X) :=
    (weilCoefficientsFreeAdjunction X l).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

instance {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    ((g)_*[WeilCoefficients.{u} l]).PreservesKInjectiveComplexes :=
  (ProEtale.upperStarLowerStarAdjunction _ g).preservesKInjectiveComplexes

/-- Taking underlying abelian sheaves commutes with the derived pushforward of sheaves of
`ℚ̄_ℓ`-modules. -/
noncomputable def rightDerivedLowerStarCompWeilCoefficientsForgetAbIso {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) :
    ((g)_*[WeilCoefficients.{u} l]).rightDerivedFunctor ⋙
        (weilCoefficientsForgetAb l Y).mapDerivedCategory ≅
      (weilCoefficientsForgetAb l Z).mapDerivedCategory ⋙
        ((g)_*[Ab.{u + 1}]).rightDerivedFunctor :=
  Functor.isoWhiskerLeft _
      (weilCoefficientsForgetAb l Y).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    Functor.rightDerivedFunctorCompIso' _ _
      (show (g)_*[WeilCoefficients.{u} l] ⋙ weilCoefficientsForgetAb l Y ≅
        weilCoefficientsForgetAb l Z ⋙ (g)_*[Ab.{u + 1}] from Iso.refl _) ≪≫
    (Functor.rightDerivedFunctorCompIso' _ _ (Iso.refl _)).symm ≪≫
    Functor.isoWhiskerRight
      (weilCoefficientsForgetAb l Z).rightDerivedFunctorIsoMapDerivedCategory _

/-- **The coefficient bridge**: the derived pushforward of `ℓ`-adic sheaves, followed by taking
underlying complexes of abelian sheaves, is the derived pushforward of abelian sheaves of the
underlying complex. -/
noncomputable def rightDerivedAdicLowerStarCompForgetAbIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (g)_*ᵃ[l].rightDerivedFunctor ⋙ (AdicSheaf.forget Y).mapDerivedCategory ⋙
        (weilCoefficientsForgetAb l Y).mapDerivedCategory ≅
      (AdicSheaf.forget Z).mapDerivedCategory ⋙
        (weilCoefficientsForgetAb l Z).mapDerivedCategory ⋙
          ((g)_*[Ab.{u + 1}]).rightDerivedFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryForgetCompRightDerivedLowerStarIso l g).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompWeilCoefficientsForgetAbIso g)

end AlgebraicGeometry.ProEtale
