/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf
public import WeilConjectures.SixFunctors.Etale.LowerStarGeometricPoint

/-!
# Direct images out of the spectrum of a separably closed field

Let `L` be a separably closed field. Étale sheaves of `Λ`-modules on `Spec L` are `Λ`-modules
(`AlgebraicGeometry.Etale.constantSheafEquivalenceOfIsSepClosed`), and the free sheaf `Λ[W]` on
an étale `L`-scheme `W` corresponds to the free module on the `L`-points of `W`; hence it is a
projective object (`AlgebraicGeometry.Etale.projective_freeSheaf_of_isSepClosed`). The direct
image `f_*` along any morphism `f : Spec L ⟶ Y` is exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isSepClosed`), and hence the
higher direct images vanish (`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isSepClosed`,
the second half of blueprint `lemma-sheaves-finite-support-finite-morphisms--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {L : Type u} [Field L] [IsSepClosed L]

/-- Over a separably closed field `L`, the free sheaf `Λ[W]` on an étale `L`-scheme `W` is a
projective object of the category of étale sheaves of `Λ`-modules on `Spec L`: under the
equivalence with `Λ`-modules given by the global sections it is the free module on the
`L`-points of `W`, since sheafification does not change global sections
(`AlgebraicGeometry.Etale.bijective_toSheafify_app_etalePoint`). -/
theorem projective_freeSheaf_of_isSepClosed (W : (Spec (.of L)).Etale) :
    Projective ((Etale.freeSheaf Λ (Spec (.of L))).obj W) := by
  let P : (Spec (.of L)).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
    uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ
  have : IsIso ((toSheafify (Spec (.of L)).smallEtaleTopology P).app (op (etalePoint L))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toSheafify_app_etalePoint Λ P)
  have hP : Projective (P.obj (op (etalePoint L))) :=
    ModuleCat.projective_of_free (Finsupp.basisSingleOne)
  have hP' : Projective
      ((constantSheafEquivalenceOfIsSepClosed Λ (k := L)).symm.functor.obj
        ((Etale.freeSheaf Λ (Spec (.of L))).obj W)) :=
    Projective.of_iso (asIso ((toSheafify (Spec (.of L)).smallEtaleTopology P).app
      (op (etalePoint L)))) hP
  exact ((constantSheafEquivalenceOfIsSepClosed Λ (k := L)).symm.map_projective_iff _).1 hP'

instance preservesHomology_lowerStar_of_isSepClosed {Y : Scheme.{u}} (f : Spec (.of L) ⟶ Y) :
    ((f)_*[ModuleCat.{u + 1} Λ]).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1`, second half: for a separably
closed field `L` and any morphism `f : Spec L ⟶ Y`, the higher direct images `R^q f_* F` vanish for
`q ≠ 0`, the direct image `f_*` being exact. -/
theorem isZero_higherDirectImage_of_isSepClosed {Y : Scheme.{u}} (f : Spec (.of L) ⟶ Y)
    (F : Sheaf (Spec (.of L)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℤ} (hq : q ≠ 0) :
    IsZero (Etale.higherDirectImage Λ f q F) := by
  obtain hq' | hq' := hq.lt_or_gt
  · exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hq'
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by omega⟩
  let e : (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) :=
    ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
      (((f)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F
  refine IsZero.of_iso ?_ ((homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ f F n).symm ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso e)
  exact (DerivedCategory.isLE_iff _ 0).1 inferInstance n (by omega)

end Etale

end AlgebraicGeometry
