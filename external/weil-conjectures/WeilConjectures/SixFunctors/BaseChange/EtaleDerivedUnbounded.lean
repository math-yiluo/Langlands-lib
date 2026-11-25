/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Étale base change for the unbounded derived pushforward of bounded below complexes

For a cartesian square `g' ≫ f = f' ≫ g` with `g` étale and a bounded below `K`, the derived
pushforward commutes with the pullback along `g`: `Lg^* Rf_* K ≅ Rf'_* Lg'^* K`. This is étale base
change on the bounded below derived categories
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`), transported to the unbounded
derived categories, where the total derived functors restrict to the bounded below ones.

## Main definitions

- `AlgebraicGeometry.Etale.leftDerivedUpperStarRightDerivedLowerStarIsoOfEtale`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **Étale base change** `Lg^* Rf_* K ≅ Rf'_* Lg'^* K` for a cartesian square `g' ≫ f = f' ≫ g`
with `g` étale and a bounded below `K`
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`). -/
noncomputable def leftDerivedUpperStarRightDerivedLowerStarIsoOfEtale (sq : IsPullback g' f' f g)
    [_root_.AlgebraicGeometry.Etale g]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ)
    [K.IsGE a] :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R((f')_*[ModuleCat.{u + 1} Λ])).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) :=
  let Kp : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨K, ⟨a, inferInstance⟩⟩
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
  (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ g).app _ ≪≫
    ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.mapIso
      ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app Kp).symm) ≪≫
    (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.app _).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app Kp)) ≪≫
    ((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _ ≪≫
    (R((f')_*[ModuleCat.{u + 1} Λ])).mapIso
      (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.app Kp ≪≫
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ g').app K).symm)

end AlgebraicGeometry.Etale
