/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Higher direct images along a finite morphism

For a finite morphism `f : X ⟶ Y` the direct image `f_*` on étale sheaves of `Λ`-modules is
exact (`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`), so its bounded
below right derived functor is `f_*` applied levelwise, and the higher direct images
`R^q f_* F` vanish for `q ≠ 0`, while `R^0 f_* F = f_* F`.

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedFunctorPlusLowerStarSingleIso`:
  `R f_* (F[0]) ≅ (f_* F)[0]` for a finite `f`.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isFinite`: `R^q f_* F = 0` for `q ≠ 0`.
- `AlgebraicGeometry.Etale.higherDirectImageZeroIsoOfIsFinite`: `R^0 f_* F ≅ f_* F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- For a finite morphism `f`, the derived direct image of a sheaf placed in degree `0` is the
direct image placed in degree `0`, `f_*` being exact. -/
noncomputable def Etale.rightDerivedFunctorPlusLowerStarSingleIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    R+((f)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) :=
  ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app _ ≪≫
    (((f)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F

/-- **Higher direct images along a finite morphism vanish** (blueprint
`lemma-finite-direct-images--2`): for a finite morphism `f : X ⟶ Y` and an étale
sheaf `F` of `Λ`-modules on `X`, `R^q f_* F = 0` for every `q ≠ 0`, since `f_*` is exact. -/
theorem Etale.isZero_higherDirectImage_of_isFinite
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℤ} (hq : q ≠ 0) :
    IsZero (Etale.higherDirectImage Λ f q F) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (Etale.rightDerivedFunctorPlusLowerStarSingleIso Λ f F))
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q hq
  · exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q hq

/-- For a finite morphism `f`, the zeroth higher direct image `R^0 f_* F` is `f_* F`
(blueprint `lemma-finite-direct-images--2`). -/
noncomputable def Etale.higherDirectImageZeroIsoOfIsFinite
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.higherDirectImage Λ f 0 F ≅ (f)_*[ModuleCat.{u + 1} Λ].obj F :=
  (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      (Etale.rightDerivedFunctorPlusLowerStarSingleIso Λ f F) ≪≫
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app _

end AlgebraicGeometry
