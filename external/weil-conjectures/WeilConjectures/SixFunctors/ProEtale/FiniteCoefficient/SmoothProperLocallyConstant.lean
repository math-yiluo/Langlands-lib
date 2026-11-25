/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SmoothProperLocallyConstant
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Smooth proper direct images of finite locally constant sheaves on the pro-étale site

Let `ν : X_proét ⟶ X_ét` be the comparison morphism of sites. For `f : X ⟶ Y` quasi-compact and
quasi-separated and an étale sheaf `G`, the higher direct images on the pro-étale site of
`ν^* G` are `ν^*` of the étale higher direct images of `G` (a consequence of
`theorem-comparison-direct-images--1`, formalised as
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`, and of the exactness
of `ν^*`). Combined with the étale theorem
`Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper`
([SGA 4, Exp. XVI, Cor. 2.2]) and with the fact that `ν^*` sends finite locally constant étale
sheaves to pro-étale sheaves locally constant with finite stalks
(`AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_comparisonUpperStar_obj`), this shows that
for `f` smooth and proper, a finite coefficient ring `Λ` of order invertible on the base and
`G` finite locally constant, the pro-étale sheaves `Rᵠf_* ν^* G` are locally constant with
finite stalks.

## Main results

- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarSingleComparisonUpperStarIso`:
  `Rf_*^{proét} ν^* G ≅ ν^* Rf_*^{ét} G` for a sheaf `G` placed in degree `0`.
- `AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarSingleComparisonUpperStarIso`:
  `Rᵠf_*^{proét} ν^* G ≅ ν^* Rᵠf_*^{ét} G`.
- `ProEtale.isFiniteLocallyConstant_homology_rightDerivedLowerStar_of_smooth_of_isProper`:
  the pro-étale higher direct images of `ν^* G` along a smooth proper morphism are locally
  constant with finite stalks.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- For `f` quasi-compact and quasi-separated and an étale sheaf `G` placed in degree `0`, the
pro-étale derived direct image of `ν^* G` is `ν^*` of the étale derived direct image of `G`
(blueprint `theorem-comparison-direct-images--1`, applied to `L = G[0]`). -/
noncomputable def rightDerivedLowerStarSingleComparisonUpperStarIso
    (G : Sheaf X.smallEtaleTopology A) :
    (R(ProEtale.lowerStar A f)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((ν^*(X)[A]).obj G)) ≅
      D(ν^*(Y)[A]).obj
        ((R(Etale.lowerStar A f)).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) :=
  (R(ProEtale.lowerStar A f)).mapIso ((ν^*(X)[A].mapDerivedCategorySingleFunctor 0).app G).symm ≪≫
    rightDerivedLowerStarMapDerivedCategoryObjIso A f _
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G).2

/-- For `f` quasi-compact and quasi-separated and an étale sheaf `G`, the pro-étale higher
direct images of `ν^* G` are `ν^*` of the étale higher direct images of `G`:
`Rᵠf_*^{proét} ν^* G ≅ ν^* Rᵠf_*^{ét} G`. This combines
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarSingleComparisonUpperStarIso` with the
commutation of the exact functor `ν^*` with homology. -/
noncomputable def homologyRightDerivedLowerStarSingleComparisonUpperStarIso
    (G : Sheaf X.smallEtaleTopology A) (q : ℤ) :
    (_root_.DerivedCategory.homologyFunctor _ q).obj ((R(ProEtale.lowerStar A f)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((ν^*(X)[A]).obj G))) ≅
      (ν^*(Y)[A]).obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R(Etale.lowerStar A f)).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
  (_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (rightDerivedLowerStarSingleComparisonUpperStarIso A f G) ≪≫
    ((ν^*(Y)[A].mapDerivedCategoryHomologyFunctorIso q).app _).symm

end Comparison

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Pro-étale higher direct images of a smooth proper morphism are locally constant**, finite
coefficient case. Let `k` be a field, `Λ` a finite ring killed by an integer invertible in `k`,
`Y` of finite type over `k`, `f : X ⟶ Y` smooth and proper and `G` a finite locally constant
sheaf of `Λ`-modules on `X_ét`. Then every pro-étale higher direct image `Rᵠf_* ν^* G` is
locally constant with finite stalks.

It is `ν^* Rᵠf_* G`
(`AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarSingleComparisonUpperStarIso`), and
`Rᵠf_* G` is finite locally constant by the étale theorem
(`Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper`). -/
theorem isFiniteLocallyConstant_homology_rightDerivedLowerStar_of_smooth_of_isProper
    [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [Smooth f] [IsProper f] (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf G] (q : ℤ) :
    IsFiniteLocallyConstant Λ ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G)))) := by
  have := Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper
    Λ aY f G q
  exact isFiniteLocallyConstant_of_iso
    (homologyRightDerivedLowerStarSingleComparisonUpperStarIso _ f G q).symm
    (isFiniteLocallyConstant_comparisonUpperStar_obj _)

end ProEtale

end AlgebraicGeometry
