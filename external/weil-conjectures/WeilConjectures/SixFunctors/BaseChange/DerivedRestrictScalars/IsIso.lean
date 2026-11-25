/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedRestrictScalars

/-!
# Restriction of scalars and isomorphy of the derived base change map

Let `φ : Λ →+* Λ'` be a morphism of commutative rings and consider a commutative square of
schemes `g' ≫ f = f' ≫ g`. For an object `K ∈ D⁺(X_ét, Λ')`, the derived base change map over `Λ`
is an isomorphism at `res K` if and only if the derived base change map over `Λ'` is one at `K`
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_restrictScalars_iff`).

This is deduced from the change of coefficients criterion
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_mapDerivedCategoryPlus_iff`, using the
compatibilities of restriction of scalars with the units of the derived pushforwards and with the
underived base change maps proved in
`WeilConjectures.SixFunctors.BaseChange.DerivedRestrictScalars`. The underived parts of the two
derived base change maps are compared in two steps
(`AlgebraicGeometry.Etale.isIso_restrictScalars_map_comp_rightDerivedFunctorPlusUnit_iff` and
`AlgebraicGeometry.Etale.isIso_map_restrictScalars_comp_rightDerivedFunctorPlusUnit_iff`), each
an instance of a half of the diagram chase
`CategoryTheory.isIso_map_comp_iff_of_reflectsIsomorphisms`: checking a single instance of the
whole chase on these concrete derived functors needs too much memory.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The underived part `g^* f_* (res K) ⟶ f'_* g'^* (res K) ⟶ R⁺f'_*(g'^* (res K))` of the
derived base change map over `Λ` is an isomorphism if and only if the restriction of scalars of
the base change map over `Λ'` at `K`, followed by the unit of `R⁺f'_*` over `Λ`, is one. -/
lemma isIso_restrictScalars_map_comp_rightDerivedFunctorPlusUnit_iff (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    IsIso (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (baseChangeMap (ModuleCat.{u + 1} Λ) sq)).app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj K)) ≫
        (f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app
          (((g')^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
            ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj K))) ↔
      IsIso (DerivedCategory.Plus.Qh.map
          ((Sheaf.restrictScalars Y'.smallEtaleTopology φ).mapHomotopyCategoryPlus.map
            ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap (ModuleCat.{u + 1} Λ') sq)).app K)) ≫
        (f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app
          ((Sheaf.restrictScalars X'.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj
            (((g')^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategoryPlus.obj K))) :=
  isIso_map_comp_iff_isIso_map_comp _ _ _ _ _ _ _
    (mapHomotopyCategoryPlus_baseChangeMap_restrictScalars φ sq K) _
    (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.naturality
      ((NatTrans.mapHomotopyCategoryPlus (upperStarRestrictScalars φ g')).app K))

/-- The restriction of scalars of the base change map over `Λ'` at `K`, followed by the unit of
`R⁺f'_*` over `Λ`, is an isomorphism if and only if the underived part
`g^* f_* K ⟶ f'_* g'^* K ⟶ R⁺f'_*(g'^* K)` of the derived base change map over `Λ'` is one:
restriction of scalars reflects isomorphisms and commutes with the units. -/
lemma isIso_map_restrictScalars_comp_rightDerivedFunctorPlusUnit_iff (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    IsIso (DerivedCategory.Plus.Qh.map
          ((Sheaf.restrictScalars Y'.smallEtaleTopology φ).mapHomotopyCategoryPlus.map
            ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap (ModuleCat.{u + 1} Λ') sq)).app K)) ≫
        (f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app
          ((Sheaf.restrictScalars X'.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj
            (((g')^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategoryPlus.obj K))) ↔
      IsIso (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (baseChangeMap (ModuleCat.{u + 1} Λ') sq)).app K) ≫
        (f')_*[ModuleCat.{u + 1} Λ'].rightDerivedFunctorPlusUnith.app
          (((g')^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategoryPlus.obj K)) := by
  -- Elaborating `hu` and `hp` first fixes the objects of the diagram chase; inferring them from
  -- the goal instead makes the elaborator unfold the concrete functors.
  have hu := restrictScalars_map_rightDerivedFunctorPlusUnit_app φ f'
    (((g')^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategoryPlus.obj K)
  have hp :=
    (Sheaf.restrictScalars Y'.smallEtaleTopology φ).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap (ModuleCat.{u + 1} Λ') sq)).app K)
  exact isIso_map_comp_iff_isIso_comp_of_reflectsIsomorphisms _
    (isIso_restrictScalars_mapDerivedCategoryPlus_map_iff φ) _ _ _ _ _ _ _ hu _ _ hp

/-- The underived part `g^* f_* K ⟶ f'_* g'^* K ⟶ R⁺f'_*(g'^* K)` of the derived base change
map over `Λ` at `res K` is an isomorphism if and only if the one over `Λ'` at `K` is one. -/
lemma isIso_comp_rightDerivedFunctorPlusUnit_restrictScalars_iff (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    IsIso (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (baseChangeMap (ModuleCat.{u + 1} Λ) sq)).app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj K)) ≫
        (f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app
          (((g')^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj
            ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj K))) ↔
      IsIso (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (baseChangeMap (ModuleCat.{u + 1} Λ') sq)).app K) ≫
        (f')_*[ModuleCat.{u + 1} Λ'].rightDerivedFunctorPlusUnith.app
          (((g')^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategoryPlus.obj K)) :=
  (isIso_restrictScalars_map_comp_rightDerivedFunctorPlusUnit_iff φ sq K).trans
    (isIso_map_restrictScalars_comp_rightDerivedFunctorPlusUnit_iff φ sq K)

/-- **The derived base change map and restriction of scalars.** For a commutative square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
and `K ∈ D⁺(X_ét, Λ')`, the derived base change map over `Λ` is an
isomorphism at the restriction of scalars of `K` along `φ : Λ →+* Λ'` if and only if the derived
base change map over `Λ'` is an isomorphism at `K`. -/
theorem isIso_derivedBaseChangeMapPlus_app_restrictScalars_iff (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K)) ↔
      IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ') sq).app K) :=
  isIso_derivedBaseChangeMapPlus_app_mapDerivedCategoryPlus_iff _ sq
    (fun J _ ↦ rightAcyclic_lowerStar_restrictScalars_obj φ f J)
    (isIso_comp_rightDerivedFunctorPlusUnit_restrictScalars_iff φ sq) K

end Etale

end AlgebraicGeometry
