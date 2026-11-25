/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.UnitIsIsoTransfer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonUnit

/-!
# The affine line is acyclic on the pro-étale site, finite coefficients

Let `k` be an algebraically closed field, `Y` a separated `k`-scheme of finite type and `Λ` a
finite coefficient ring whose exponent is invertible on `k`. For the affine line
`p : 𝔸¹_Y ⟶ Y`, the unit `Λ_Y ⟶ Rp_* Lp^* Λ_Y` of the derived adjunction `Lp^* ⊣ Rp_*` of
pro-étale sheaves of `Λ`-modules is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_unit_affineLine_singleFunctor_tensorUnit`).

This is the étale statement `AlgebraicGeometry.Etale.isIso_unit_constantComplex_affineLine`,
first restricted to the bounded below derived categories
(`AlgebraicGeometry.Etale.isIso_unit_plus_affineLine_singleFunctor_tensorUnit`), then
transported along the site comparison `ν^*`, which is compatible with the units
(`AlgebraicGeometry.ProEtale.comparison_unit`) and sends `Λ_Y` to `Λ_Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
  [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

namespace Etale

include aY in
/-- **The affine line is acyclic, on bounded below complexes**: for the affine line
`p : 𝔸¹_Y ⟶ Y` over a separated `k`-scheme of finite type `Y`, `k` algebraically closed, the
unit `Λ_Y ⟶ Rp_* p^* Λ_Y` of the bounded below derived adjunction `p^* ⊣ Rp_*` is an
isomorphism. The unbounded statement is
`AlgebraicGeometry.Etale.isIso_unit_constantComplex_affineLine`, and the invertibility of a
unit only depends on the left adjoint, which on bounded below complexes is the restriction of
the unbounded one. -/
theorem isIso_unit_plus_affineLine_singleFunctor_tensorUnit :
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (𝟙_ _))) := by
  have h := isIso_unit_constantComplex_affineLine Λ aY
  have : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app
        (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj (𝟙_ _)))) :=
    (NatTrans.isIso_app_iff_of_iso _ (constantComplexIsoSingleFunctor Λ Y)).1 h
  exact Adjunction.isIso_unit_app_of_isIso_unit_app_obj _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))
    DerivedCategory.Plus.ι
    DerivedCategory.Plus.ι
    ((Etale.upperStar (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).mapDerivedCategoryPlusCompatibility ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) _).symm) _

end Etale

namespace ProEtale

include aY in
/-- **The affine line is acyclic on the pro-étale site, finite coefficients**: for the affine
line `p : 𝔸¹_Y ⟶ Y` over a separated `k`-scheme of finite type `Y`, `k` algebraically closed, the
unit `Λ_Y ⟶ Rp_* Lp^* Λ_Y` of the derived adjunction `Lp^* ⊣ Rp_*` of pro-étale sheaves of
`Λ`-modules is an isomorphism: it is `ν^*` of the étale unit, up to the comparison
isomorphisms (`AlgebraicGeometry.ProEtale.comparison_unit`). -/
theorem isIso_unit_affineLine_singleFunctor_tensorUnit :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) := by
  let G := (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).obj (𝟙_ _)
  have := Etale.isIso_unit_plus_affineLine_singleFunctor_tensorUnit Λ aY
  have h := comparison_unit Λ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) G
  have : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj G)) := by
    rw [← h]
    infer_instance
  let e : (DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj G ≅
      (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _) :=
    ((ν^*(Y)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (comparisonUpperStarUnitIso Λ Y)
  exact (NatTrans.isIso_app_iff_of_iso _ e).1 this

end ProEtale

end AlgebraicGeometry
