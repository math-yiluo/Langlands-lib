/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeColimit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Higher direct images on the unbounded derived category commute with filtered colimits

For a quasi-compact and quasi-separated morphism `h : Y ⟶ X`, the functor
`𝓖 ↦ Hᵠ(Rh_* 𝓖[0])` on sheaves of `Λ`-modules on `Y_ét`, computed with the unbounded derived
category, commutes with filtered colimits indexed by small categories in `Type (u + 1)`
(`AlgebraicGeometry.Etale.preservesColimitsOfShape_singleFunctor_rightDerivedLowerStar`). This is
`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage_large` (blueprint
`lem-sbc-higher-direct-image-large-filtered-colimit`), transported from the bounded below derived
category.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- Higher direct images along a quasi-compact quasi-separated morphism, computed on the
unbounded derived category, commute with filtered colimits (used in the proof of blueprint
`lemma-kunneth-field-coefficients--1`, see `prose-04-17`). -/
theorem preservesColimitsOfShape_singleFunctor_rightDerivedLowerStar
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.homologyFunctor _ q) :=
  have : PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        (R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.ι) ⋙
          DerivedCategory.homologyFunctor _ q) :=
    preservesColimitsOfShape_higherDirectImage_large Λ h q J
  preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.isoWhiskerRight
        ((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility
        (DerivedCategory.homologyFunctor _ q)))

end Etale

end AlgebraicGeometry
