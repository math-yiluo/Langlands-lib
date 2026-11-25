/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateTransport
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsProjectionPullback
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorSheafUpperStar

/-!
# Derived extension of scalars of étale sheaves commutes with `Rg_*` for proper `g`

Let `R` be a finite commutative ring, `S` an `R`-algebra and `g : Z ⟶ Y` proper. The base change
map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` of derived extension of scalars `Ψ = - ⊗ᴸ_R S` of étale sheaves
along the derived direct image, the mate of the commutation of `Ψ` with `Lg^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso`), is an isomorphism.
Restricted back to `R`, it is the projection map `Rg_* M ⊗ᴸ S_Y ⟶ Rg_* (M ⊗ᴸ Lg^* S_Y)` for the
constant sheaf `S_Y`, an isomorphism by the projection formula
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`).

This is the étale counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerStar`; unlike
the pro-étale statement, it holds for all `M`, since the étale projection formula is unbounded.

## Main results

- `AlgebraicGeometry.Etale.reflectsIsomorphisms_derivedRestrictScalars`: derived restriction of
  scalars of étale sheaves reflects isomorphisms.
- `AlgebraicGeometry.Etale.isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app`:
  the base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` is an isomorphism for finite `R` and proper `g`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

-- Use the monoidal structure of the derived tensor product of étale sheaves, see
-- `WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsDerived`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme

section ReflectsIsomorphisms

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u})

/-- Restriction of scalars of étale sheaves reflects isomorphisms: it is computed sectionwise,
and restriction of scalars of modules reflects isomorphisms. -/
instance reflectsIsomorphisms_sheafRestrictScalars :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).ReflectsIsomorphisms where
  reflects {A B} a h := by
    have (U : X.Etaleᵒᵖ) : IsIso (a.hom.app U) := by
      have : IsIso ((ModuleCat.restrictScalars.{u + 1} φ).map (a.hom.app U)) :=
        inferInstanceAs (IsIso (((sheafToPresheaf _ _).map
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).map a)).app U))
      exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars.{u + 1} φ)
    have : ∀ U, IsIso (((sheafToPresheaf _ _).map a).app U) := this
    have : IsIso ((sheafToPresheaf _ _).map a) := NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- Derived restriction of scalars of étale sheaves reflects isomorphisms: it commutes with the
cohomology sheaves, and restriction of scalars of sheaves reflects isomorphisms. -/
instance reflectsIsomorphisms_derivedRestrictScalars :
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).ReflectsIsomorphisms where
  reflects f _ := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((Sheaf.restrictScalars X.smallEtaleTopology φ).map
        ((DerivedCategory.homologyFunctor _ n).map f)) :=
      (NatIso.isIso_map_iff (Functor.mapDerivedCategoryHomologyFunctorIso
        (Sheaf.restrictScalars X.smallEtaleTopology φ) n) f).2 (by
          dsimp only [Functor.comp_map]
          infer_instance)
    exact isIso_of_reflects_iso _ (Sheaf.restrictScalars X.smallEtaleTopology φ)

end ReflectsIsomorphisms

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]
  {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- **Reduction to the projection formula.** The base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` is
an isomorphism at `M` as soon as the mate `L(- ⊗ S_Y) (Rg_* M) ⟶ Rg_* (L(- ⊗ S_Z) M)` of the
comparison `Lg^* (K ⊗ᴸ S_Y) ⟶ Lg^* K ⊗ᴸ S_Z` is. Indeed, restricted back to `R`, `Ψ` is
`L(- ⊗ S)` (`AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection`), compatibly
with the derived pullback
(`AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection_transpose_upperStar`), and
restriction of scalars reflects isomorphisms. -/
theorem isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app_of_isIso_mateEquiv
    [IsNoetherianRing R] (M : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)))
    [IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)).app M)] :
    IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom).app M) :=
  Adjunction.isIso_mateEquiv_app_of_isIso_mateEquiv_app
    (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Y)
    (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Z)
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g)
    (leftDerivedSheafExtendScalarsProjection R S Y) (leftDerivedSheafExtendScalarsProjection R S Z)
    (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)
    (fun X ↦ Adjunction.map_comp_mateEquiv_app_comp_map_of_transpose _ _ _ _ _ _ X
      (leftDerivedSheafExtendScalarsProjection_transpose_upperStar R S g X)) M

/-- **Derived extension of scalars commutes with `Rg_*` for proper `g`.** For a finite ring `R`,
an `R`-algebra `S` and a proper `g : Z ⟶ Y`, the base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)`, the
mate of `AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso`, is an
isomorphism. Restricted to `R`, it is the projection map `Rg_* M ⊗ᴸ S_Y ⟶ Rg_* (M ⊗ᴸ S_Z)` for
the sheaf `S_Y`. -/
theorem isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app [Finite R]
    [IsProper g] (M : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom).app M) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite R g
  have : IsIso ((((derivedUpperStarLowerStarAdjunction _ g).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)).app M).app
        (derivedSingle (sheafRestrictScalarsUnit R S Y))) :=
    inferInstanceAs (IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) g).app
      M).app (derivedSingle (sheafRestrictScalarsUnit R S Y))))
  have : IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)).app M) :=
    Adjunction.isIso_mateEquiv_app_of_isIso_rightAdjointProjectionMap
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)
      (leftDerivedUpperStarDerivedSingleMap g (upperStarSheafRestrictScalarsUnitMap R S g))
      (leftDerivedTensorRightIso _) (leftDerivedTensorRightIso _) _
      (leftDerivedTensorRightUpperStarMap_app_comp g _) _
  exact isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app_of_isIso_mateEquiv
    R S g M

end AlgebraicGeometry.Etale
