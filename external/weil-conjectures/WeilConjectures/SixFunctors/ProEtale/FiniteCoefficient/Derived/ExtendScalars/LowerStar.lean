/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.MateTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.ProjectionPullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormulaBounded
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjectionComparison

/-!
# Derived scalar extension commutes with `Rg_*` for proper `g`

Let `R` be a finite commutative ring and `S` an `R`-algebra. The base change map
`Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` of derived scalar extension `Ψ = - ⊗ᴸ_R S` along the derived direct
image is the mate of the commutation of `Ψ` with `Lg^*`. For proper `g` it is an isomorphism at
`M = j_! K` with `K` bounded constructible of finite Tor amplitude on an open `j : U ⟶ Z`:
restricted back to `R`, it is the projection map `Rg_* M ⊗ᴸ S_Y ⟶ Rg_* (M ⊗ᴸ Lg^* S_Y)` for the
constant sheaf `S_Y`, an isomorphism by the projection formula
(blueprint `theorem-grothendieck-lefschetz-trace-formula--7`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section LowerStar

variable [IsNoetherianRing R] {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` of derived scalar extension along the derived
direct image: the mate of the commutation `Lg^* ∘ Ψ ≅ Ψ ∘ Lg^*`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`). -/
noncomputable def rightDerivedLowerStarExtendScalarsMap :
    R((g)_*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Y) ⟶
      L(sheafExtendScalars (algebraMap R S) Z) ⋙ R((g)_*[ModuleCat.{u + 1} S]) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (leftDerivedUpperStarExtendScalarsIso R S g).hom

/-- **Reduction to the projection formula.** The base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` is
an isomorphism at `M` as soon as the mate `L(- ⊗ S_Y) (Rg_* M) ⟶ Rg_* (L(- ⊗ S_Z) M)` of the
comparison `Lg^* (K ⊗ᴸ S_Y) ⟶ Lg^* K ⊗ᴸ S_Z` is. Indeed, restricted back to `R`, `Ψ` is
`L(- ⊗ S)` (`AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsProjection`), compatibly
with the derived pullback
(`AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsProjection_transpose_upperStar`), and
restriction of scalars reflects isomorphisms. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isIso_mateEquiv
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R)))
    [IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)).app M)] :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app M) :=
  Adjunction.isIso_mateEquiv_app_of_isIso_mateEquiv_app
    (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (leftDerivedSheafExtendScalarsAdjunction R S Y)
    (leftDerivedSheafExtendScalarsAdjunction R S Z) (leftDerivedUpperStarExtendScalarsIso R S g)
    (leftDerivedSheafExtendScalarsProjection R S Y) (leftDerivedSheafExtendScalarsProjection R S Z)
    (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)
    (fun X ↦ Adjunction.map_comp_mateEquiv_app_comp_map_of_transpose _ _ _ _ _ _ X
      (leftDerivedSheafExtendScalarsProjection_transpose_upperStar R S g X)) M

/-- **The projection formula at `S_Y`.** For a finite ring `R` and a proper `g`, the projection
map `Rg_*(j_! K) ⊗ᴸ S_Y ⟶ Rg_*(j_! K ⊗ᴸ Lg^* S_Y)` is an isomorphism for `K` bounded
constructible of finite Tor amplitude: `S_Y` is the pro-étale realization of a bounded étale
complex (`AlgebraicGeometry.ProEtale.exists_comparisonUpperStar_obj_iso_sheafRestrictScalarsUnit`),
so this is `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_bounded`.
-/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_derivedSingle [Finite R] [IsProper g]
    {U : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) U K) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) g).app
      (D((j)_!open[ModuleCat.{u + 1} R]).obj K)).app
        (derivedSingle (sheafRestrictScalarsUnit R S Y))) := by
  obtain ⟨c₀, ⟨e⟩⟩ := exists_comparisonUpperStar_obj_iso_sheafRestrictScalarsUnit R S Y
  have hL₀ : _root_.DerivedCategory.TStructure.t.bounded
      ((_root_.DerivedCategory.singleFunctor _ 0).obj c₀) :=
    ⟨⟨0, inferInstanceAs (_root_.DerivedCategory.IsGE
        ((_root_.DerivedCategory.singleFunctor _ 0).obj c₀) 0)⟩,
      ⟨0, inferInstanceAs (_root_.DerivedCategory.IsLE
        ((_root_.DerivedCategory.singleFunctor _ 0).obj c₀) 0)⟩⟩
  have : IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) g).app
      (D((j)_!open[ModuleCat.{u + 1} R]).obj K)).app
        ((_root_.DerivedCategory.singleFunctor _ 0 ⋙ D(ν^*(Y)[ModuleCat.{u + 1} R])).obj c₀)) :=
    isIso_rightDerivedLowerStarProjectionMap_app_app_of_bounded R g j hK hL₀
  exact NatTrans.isIso_app_app_of_iso _ (Iso.refl _)
    (((ν^*(Y)[ModuleCat.{u + 1} R]).mapDerivedCategorySingleFunctor 0).app c₀ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
      (_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).symm.app
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (sheafRestrictScalarsUnit R S Y)))

/-- **Derived scalar extension commutes with `Rg_*` for proper `g`.** Let `R` be a finite ring
and `g : Z ⟶ Y` proper. For a complex `K` on an open subscheme `j : U ⟶ Z` that is bounded
constructible of finite Tor amplitude, the base change map `Ψ (Rg_* j_! K) ⟶ Rg_* Ψ (j_! K)` is an
isomorphism. Restricted to `R`, it is the projection map `Rg_* (j_! K) ⊗ᴸ S_Y ⟶ Rg_* (j_! K ⊗ᴸ S_Z)`
for the constant sheaf `S_Y`. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app [Finite R] [IsProper g] {U : Scheme.{u}}
    (j : U ⟶ Z) [IsOpenImmersion j]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) U K) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app
      (D((j)_!open[ModuleCat.{u + 1} R]).obj K)) := by
  have : IsIso ((((derivedUpperStarLowerStarAdjunction _ g).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)).app
        (D((j)_!open[ModuleCat.{u + 1} R]).obj K)).app
          (derivedSingle (sheafRestrictScalarsUnit R S Y))) :=
    isIso_rightDerivedLowerStarProjectionMap_app_app_derivedSingle R S g j hK
  have : IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)).app
        (D((j)_!open[ModuleCat.{u + 1} R]).obj K)) :=
    Adjunction.isIso_mateEquiv_app_of_isIso_rightAdjointProjectionMap
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)
      (leftDerivedUpperStarDerivedSingleMap g (upperStarSheafRestrictScalarsUnitMap R S g))
      (leftDerivedTensorRightIso _) (leftDerivedTensorRightIso _) _
      (leftDerivedTensorRightUpperStarMap_app_comp g _) _
  exact isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isIso_mateEquiv R S g _

end LowerStar

end AlgebraicGeometry.ProEtale
