/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ProjectionMapIhom
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarInternalHom
public import WeilConjectures.TraceFormula.CurveLocal.ExtensionByZero

/-!
# Local terms are not computed stalk by stalk

Blueprint `remark-locality-warning`: the stalk functor does not commute with the internal hom.
For the open complement `j : 𝔾_m ⟶ 𝔸¹_k` of the zero section `s` over a separably closed field
`k` and `K = j_! Λ`, the stalk `Ls^* K` of `K` at the origin vanishes, but
`RHom(j_! Λ, j_! Λ) ≅ Rj_* Λ` has nonzero stalk there.

## The argument

For an open immersion `j : U ⟶ X` both `N ↦ RHom(j_! M, N)` and `N ↦ Rj_* RHom(M, Lj^* N)` are
right adjoint to `T ↦ j_! M ⊗ᴸ T`, using the projection formula
`j_!(Lj^* T ⊗ᴸ M) ≅ T ⊗ᴸ j_! M`
(`AlgebraicGeometry.Etale.isIso_projectionMap_derivedEtaleLowerShriek`) for the left adjoint of
`Lj^*`. The abstract statement is
`CategoryTheory.Functor.Monoidal.ihomObjIsoOfIsIsoProjectionMap`. For `M = Λ_U` and `N = j_! Λ_U`,
`Lj^* j_! Λ_U ≅ Λ_U` and `RHom(Λ_U, Λ_U) ≅ Λ_U`. The stalk at the origin is the derived pullback
`Ls^*` along the zero section. That `Ls^* Rj_* Λ ≠ 0` is
`AlgebraicGeometry.Etale.not_isZero_leftDerivedUpperStar_zeroSection_rightDerivedLowerStar`.

## Main definitions

- `AlgebraicGeometry.Etale.ihomOpenImmersionLowerShriekIso`:
  `RHom(j_! M, N) ≅ Rj_* RHom(M, Lj^* N)` for an open immersion `j`.
- `AlgebraicGeometry.Etale.ihomOpenImmersionLowerShriekConstantIso`:
  `RHom(j_! Λ, j_! Λ) ≅ Rj_* Λ`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_zeroSection_and_not_isZero_ihom`
  (`remark-locality-warning`): `Ls^*(j_! Λ) = 0` but `Ls^* RHom(j_! Λ, j_! Λ) ≠ 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance] _root_.DerivedCategory.braidedCategory'

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The extension by zero `D(j_!)` along an open immersion is the left adjoint of the étale
lower shriek of `j`: both are left adjoint to `Lj^* ≅ D(j^*)`. -/
noncomputable def mapDerivedCategoryEtaleLowerShriekIsoOpenImmersionLowerShriek :
    (etaleLowerShriek (ModuleCat.{u + 1} Λ) j inferInstance).mapDerivedCategory ≅
      D((j)_!open[ModuleCat.{u + 1} Λ]) :=
  (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction j).leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm)

/-- For an open immersion `j : U ⟶ X`, `RHom(j_! M, N) ≅ Rj_* RHom(M, Lj^* N)`: both sides are
right adjoint to `T ↦ j_! M ⊗ᴸ T`, by the projection formula for `j_!`
(`AlgebraicGeometry.Etale.isIso_projectionMap_derivedEtaleLowerShriek`). -/
noncomputable def ihomOpenImmersionLowerShriekIso
    (M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (ihom (D((j)_!open[ModuleCat.{u + 1} Λ]).obj M)).obj N ≅
      (R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((ihom M).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj N)) :=
  letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) j
  haveI (A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((Functor.Monoidal.projectionMap
        (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction j) A).app M) :=
    have := isIso_projectionMap_derivedEtaleLowerShriek (A := ModuleCat.{u + 1} Λ) j A
    inferInstance
  (MonoidalClosed.internalHom.mapIso
      ((mapDerivedCategoryEtaleLowerShriekIsoOpenImmersionLowerShriek Λ j).app M).op).app N ≪≫
    (Functor.Monoidal.ihomObjIsoOfIsIsoProjectionMap
      (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction j)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j) M).app N

/-- Blueprint `remark-locality-warning`: for an open immersion `j : U ⟶ X`,
`RHom(j_! Λ_U, j_! Λ_U) ≅ Rj_* Λ_U`, by `AlgebraicGeometry.Etale.ihomOpenImmersionLowerShriekIso`,
`Lj^* j_! ≅ 𝟭` and `RHom(Λ_U, -) ≅ 𝟭`. -/
noncomputable def ihomOpenImmersionLowerShriekConstantIso :
    (ihom (D((j)_!open[ModuleCat.{u + 1} Λ]).obj (constantComplex Λ U))).obj
        (D((j)_!open[ModuleCat.{u + 1} Λ]).obj (constantComplex Λ U)) ≅
      (R((j)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ U) :=
  ihomOpenImmersionLowerShriekIso Λ j _ _ ≪≫
    (R((j)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((ihom (constantComplex Λ U)).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app _ ≪≫
            (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} Λ) j).unit).symm.app _) ≪≫
        (MonoidalClosed.unitNatIso.app (constantComplex Λ U)).symm)

end OpenImmersion

variable [Finite Λ] [Nontrivial Λ] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
  (k : Type u) [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j]

/-- Blueprint `remark-locality-warning`: Local terms are not computed stalk by stalk.

Let `j : G ⟶ 𝔸¹_k` be the open complement of the zero section `s` over a separably closed field
`k`, and `K = j_! Λ_G`. The stalk `Ls^* K` of `K` at the origin vanishes, but the stalk of
`RHom(K, K) ≅ Rj_* Λ_G` (`AlgebraicGeometry.Etale.ihomOpenImmersionLowerShriekConstantIso`) at
the origin does not. Hence the stalk functor does not commute with this internal hom. -/
theorem isZero_leftDerivedUpperStar_zeroSection_and_not_isZero_ihom
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ) :
    IsZero ((L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)))^*[
        ModuleCat.{u + 1} Λ])).obj
      (D((j)_!open[ModuleCat.{u + 1} Λ]).obj (constantComplex Λ G))) ∧
    ¬ IsZero ((L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)))^*[
        ModuleCat.{u + 1} Λ])).obj
      ((ihom (D((j)_!open[ModuleCat.{u + 1} Λ]).obj (constantComplex Λ G))).obj
        (D((j)_!open[ModuleCat.{u + 1} Λ]).obj (constantComplex Λ G)))) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · exact
      isZero_leftDerivedUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek_of_disjoint_range
        _ j _ (hj ▸ disjoint_compl_right) _
  exact not_isZero_leftDerivedUpperStar_zeroSection_rightDerivedLowerStar Λ k j hj
    (h.of_iso ((L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)))^*[
      ModuleCat.{u + 1} Λ])).mapIso (ihomOpenImmersionLowerShriekConstantIso Λ j).symm))

end Etale

end AlgebraicGeometry
