/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal

/-!
# Proper base change for higher direct images

For a cartesian square `g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` with `f`
proper and a finite coefficient ring `Λ`, the pullback along `g` of the higher direct image
`Rᵠf_* F` of a sheaf `F` of `Λ`-modules is `Rᵠf'_*(g'^* F)`
(`AlgebraicGeometry.Etale.upperStarHomologyRightDerivedLowerStarIsoOfIsProper`), by the proper
base change theorem `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`.
For a constant sheaf `M_X` this reads `g^* Rᵠf_* M_X ≅ Rᵠf'_* M_{X'}`
(`AlgebraicGeometry.Etale.upperStarHomologyRightDerivedLowerStarConstantSheafIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **Proper base change for higher direct images.** For a cartesian square
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` with `f` proper and `Λ` finite, the
pullback along `g` of `Rᵠf_* F` is `Rᵠf'_*(g'^* F)`. -/
noncomputable def upperStarHomologyRightDerivedLowerStarIsoOfIsProper {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [IsProper f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (g)^*[ModuleCat.{u + 1} Λ].obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≅
    (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f')_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((g')^*[ModuleCat.{u + 1} Λ].obj F))) :=
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  have := Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq K
    (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X isAddTorsion_of_finite K)
  (g)^*[ModuleCat.{u + 1} Λ].mapIso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app K).symm) ≪≫
    ((g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
        (((g')^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusSingleFunctor 0).app F)) ≪≫
    (_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _)

/-- **Proper base change for higher direct images of a constant sheaf.** For a cartesian square
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` with `f` proper and `Λ` finite, and
a `Λ`-module `M`, the pullback along `g` of `Rᵠf_* M_X` is `Rᵠf'_* M_{X'}`. -/
noncomputable def upperStarHomologyRightDerivedLowerStarConstantSheafIso {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [IsProper f] (M : ModuleCat.{u + 1} Λ) (q : ℤ) :
    (g)^*[ModuleCat.{u + 1} Λ].obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) ≅
    (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f')_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) :=
  upperStarHomologyRightDerivedLowerStarIsoOfIsProper sq _ q ≪≫
    (_root_.DerivedCategory.homologyFunctor _ q).mapIso ((R((f')_*[ModuleCat.{u + 1} Λ])).mapIso
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g').app M)))

end Etale

end AlgebraicGeometry
