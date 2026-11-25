/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomotopyLimitExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Pullback along weakly étale morphisms commutes with derived limits of towers

For a weakly étale `f : X ⟶ Y`, the pullback `f^*` of pro-étale sheaves is restriction along the
localization functor (`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), so it is
exact and preserves countable products, computed sectionwise
(`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_discrete_upperStar_ab`,
`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_discrete_upperStar_moduleCat`). Hence its
derived functor sends homotopy limit cones (`R lim`) to homotopy limit cones
(`AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_mapDerivedCategory_mapCone`), and then
also the Milnor sequences.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : WeaklyEtale f]

/-- Pullback along a weakly étale morphism preserves countable products: it is restriction along
the localization functor, computed sectionwise. -/
instance preservesLimitsOfShape_discrete_upperStar_ab :
    PreservesLimitsOfShape (Discrete ℕ) (ProEtale.upperStar Ab.{u + 1} f) :=
  have := Scheme.ProEt.isContinuous_overMap hf
  have : PreservesLimitsOfShape (Discrete ℕ) (ProEtale.localizationRestriction Ab.{u + 1} f hf ⋙
      sheafToPresheaf _ _) :=
    preservesLimitsOfShape_of_natIso (Functor.sheafPushforwardContinuousCompSheafToPresheafIso
      _ _ _ _).symm
  have : PreservesLimitsOfShape (Discrete ℕ) (ProEtale.localizationRestriction Ab.{u + 1} f hf) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  preservesLimitsOfShape_of_natIso (ProEtale.upperStarIsoLocalizationRestriction _ f hf).symm

/-- **Pullback along a weakly étale morphism commutes with derived limits of towers** of
complexes of abelian pro-étale sheaves. -/
lemma isHomotopyLimit_upperStar_mapDerivedCategory_mapCone
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})} {c : Cone F}
    (hc : IsHomotopyLimit c) :
    IsHomotopyLimit ((ProEtale.upperStar Ab.{u + 1} f).mapDerivedCategory.mapCone c) :=
  (ProEtale.upperStar Ab.{u + 1} f).isHomotopyLimit_mapDerivedCategory_mapCone hc

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Pullback along a weakly étale morphism preserves countable products of sheaves of modules. -/
instance preservesLimitsOfShape_discrete_upperStar_moduleCat :
    PreservesLimitsOfShape (Discrete ℕ) (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f) :=
  have := Scheme.ProEt.isContinuous_overMap hf
  have : PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) f hf ⋙ sheafToPresheaf _ _) :=
    preservesLimitsOfShape_of_natIso (Functor.sheafPushforwardContinuousCompSheafToPresheafIso
      _ _ _ _).symm
  have : PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) f hf) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  preservesLimitsOfShape_of_natIso (ProEtale.upperStarIsoLocalizationRestriction _ f hf).symm

/-- **Pullback along a weakly étale morphism commutes with derived limits of towers** of
complexes of sheaves of modules. -/
lemma isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_moduleCat
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    {c : Cone F} (hc : IsHomotopyLimit c) :
    IsHomotopyLimit ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.mapCone c) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).isHomotopyLimit_mapDerivedCategory_mapCone hc

end AlgebraicGeometry.ProEtale
