/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow
import WeilConjectures.CategoryTheory.DerivedCategory.IsLE

/-!
# Cohomological amplitude of the pro-étale direct images

We transport the finite cohomological amplitude of the étale functors `Rf_*` and `Rf_!` on
torsion sheaves to the pro-étale site through the comparison functor `ν^*`, whose essential image
on bounded below complexes consists of the classical complexes.

## Implementation details

For `Rf_*`, the étale bound is Stacks Project, Tag 0F10
(`AlgebraicGeometry.torsionEtaleCohomologicalDimension_finite_of_finiteType`); it is transported
to the pro-étale site by the comparison of direct images `ν_Y^* ∘ Rf_* ≅ Rf_* ∘ ν_X^*` on
bounded below complexes
(`AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar`).

For `Rf_!`, write `f = g ∘ j` for the chosen compactification; `Rf_! = Rg_* ∘ j_!` with `j_!`
exact, and Tag 0F10 applies to the proper map `g`
(`AlgebraicGeometry.Etale.exists_isLE_rightDerivedLowerShriekOfCompactification_obj`). The
comparison `Rf_! ∘ ν_X^* ≅ ν_Y^* ∘ Rf_!` on bounded below complexes
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`) transports the bound, since
the exact functor `ν_Y^*` preserves it.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- **Finite cohomological amplitude of `Rf_*` on classical torsion sheaves**: for a morphism
`f : X ⟶ Y` of schemes of finite type over a field `K`, there is `N` such that for every torsion
étale sheaf `F` on `X`, the pro-étale higher direct images `R^q f_* ν_X^* F` of the classical
sheaf `ν_X^* F` vanish for `q > N`. -/
theorem exists_isZero_homology_rightDerivedLowerStar_comparisonUpperStar_of_finiteType
    (K : Type u) [Field K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] :
    ∃ N : ℕ, ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
      ∀ q : ℤ, (N : ℤ) < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
          (R+(ProEtale.lowerStar AddCommGrpCat.{u + 1} f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F)))) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of K))).mp inferInstance
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiSeparated f := QuasiSeparated.of_quasiSeparatedSpace f
  obtain ⟨_, ⟨n, rfl, hn⟩, _⟩ :=
    sInf_lt_iff.mp (torsionEtaleCohomologicalDimension_finite_of_finiteType K X Y f).1
  obtain ⟨e⟩ := nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar
    AddCommGrpCat.{u + 1} f
  refine ⟨n, fun F hF q hq ↦ ?_⟩
  let ν := comparisonUpperStar AddCommGrpCat.{u + 1}
  let M := (DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F
  refine ((ν Y).map_isZero (hn F hF q hq)).of_iso ?_
  exact (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (R+(ProEtale.lowerStar AddCommGrpCat.{u + 1} f).mapIso
        (((ν X).mapDerivedCategoryPlusSingleFunctor 0).app F).symm ≪≫ (e.app M).symm) ≪≫
    (((ν Y).mapDerivedCategoryPlusHomologyFunctorIso q).app _).symm

/-- **Finite cohomological amplitude of `Rf_!` on classical torsion complexes**: for a finite
coefficient ring `Λ` (so that every sheaf of `Λ`-modules is torsion) and `f : X ⟶ Y` admitting a
compactification with `Y` quasi-compact, there is `N` such that the pro-étale `Rf_!` sends every
bounded below classical complex `ν_X^* L`, `L ∈ D⁺(X_ét, Λ)`, concentrated in degrees `≤ n` to a
complex concentrated in degrees `≤ n + N`. -/
theorem exists_isLE_rightDerivedLowerShriek_comparisonUpperStar
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] :
    ∃ N : ℕ, ∀ (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (n : ℤ), L.obj.IsLE n →
        ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj L.obj)).IsLE (n + N) := by
  obtain ⟨N, hN⟩ := Etale.exists_isLE_rightDerivedLowerShriekOfCompactification_obj Λ
    (HasCompactification.compactification f)
  refine ⟨N, fun L n hL ↦ ?_⟩
  have : ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
      (DerivedCategory.Plus.ι.obj L)).IsLE (n + N) := hN L.obj n hL
  exact DerivedCategory.isLE_of_iso_of_isLE
    ((rightDerivedLowerShriekComparisonIso (ModuleCat.{u + 1} Λ) f).app L).symm
    ((ν^*(Y)[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj _ _)

end AlgebraicGeometry.ProEtale
