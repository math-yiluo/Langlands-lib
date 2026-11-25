/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModLimits
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!
# Pullback of module objects along a weakly étale morphism preserves limits

For a weakly étale `g : U ⟶ X`, the pullback `g^*` of pro-étale sheaves is restriction along the
localization functor (`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), which is
computed sectionwise and hence preserves all limits
(`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_upperStar_of_weaklyEtale`). Consequently, for a
monoid object `R` in abelian pro-étale sheaves on `X`, the transport of `R`-module objects along
`g^*` preserves limits as well
(`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_upperStar_mapMod_of_weaklyEtale`).
-/

@[expose] public section

universe w w' u' u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U X : Scheme.{u}} (g : U ⟶ X) [hg : WeaklyEtale g]

/-- Pullback along a weakly étale morphism preserves all limits that exist in the coefficient
category: it is restriction along the localization functor, computed sectionwise. -/
instance preservesLimitsOfShape_upperStar_of_weaklyEtale (J : Type*) [Category* J]
    [HasLimitsOfShape J A] : PreservesLimitsOfShape J ((g)^*[A]) :=
  have := Scheme.ProEt.isContinuous_overMap hg
  have : PreservesLimitsOfShape J
      (ProEtale.localizationRestriction A g hg ⋙ sheafToPresheaf _ _) :=
    preservesLimitsOfShape_of_natIso (Functor.sheafPushforwardContinuousCompSheafToPresheafIso
      _ _ _ _).symm
  have : PreservesLimitsOfShape J (ProEtale.localizationRestriction A g hg) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  preservesLimitsOfShape_of_natIso (ProEtale.upperStarIsoLocalizationRestriction _ g hg).symm

/-- Pullback along a weakly étale morphism preserves all limits of a size that exist in the
coefficient category. -/
instance preservesLimitsOfSize_upperStar_of_weaklyEtale [HasLimitsOfSize.{w, w'} A] :
    PreservesLimitsOfSize.{w, w'} ((g)^*[A]) where
  preservesLimitsOfShape := inferInstance

/-- For a weakly étale `g : U ⟶ X` and a monoid object `R` of abelian pro-étale sheaves on `X`,
the pullback `g^*` of `R`-module objects preserves all small limits. -/
instance preservesLimitsOfShape_upperStar_mapMod_of_weaklyEtale (J : Type*) [Category* J]
    [HasLimitsOfShape J Ab.{u + 1}] (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] : PreservesLimitsOfShape J (((g)^*[Ab.{u + 1}]).mapMod R) :=
  inferInstance

end AlgebraicGeometry.ProEtale
