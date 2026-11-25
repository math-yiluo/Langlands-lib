/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

/-!

# The projection formula for the extension by zero on module objects

Let `Λ` be a commutative condensed ring and `j : U ⟶ X` an open immersion. On the derived
categories of module objects over `Λ`, the adjunction `Dj_! ⊣ Lj^*` has the projection map
```
q_{j,M,N} : Dj_! (M ⊗ᴸ Lj^* N) ⟶ Dj_! M ⊗ᴸ N,
```
the transpose of `M ⊗ᴸ Lj^* N ⟶ Lj^* Dj_! M ⊗ᴸ Lj^* N ⟶ Lj^* (Dj_! M ⊗ᴸ N)`
(`CategoryTheory.Adjunction.projectionMap` for the lax monoidal structure of `Lj^*`). This file
shows that it is an isomorphism: the derived projection formula for the extension by zero.

## Main definitions

- `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction'`: the
  adjunction `Dj_! ⊣ Lj^*`.
- `ProEtale.CondensedRing.openImmersionProjectionComparison'`: the projection map `q_j`, as a
  natural transformation of bifunctors.

## Main results

- `ProEtale.CondensedRing.isIso_openImmersionProjectionComparison'`: `q_j` is an isomorphism.

## The argument

The unit of `Dj_! ⊣ Lj^*` is an isomorphism, since `j_!` on module objects is fully faithful
(`ProEtale.CondensedRing.fullyFaithfulOpenImmersionLowerShriek`) and the derived adjunction is
obtained levelwise (`Adjunction.isIso_mapDerivedCategoryAdjunction_unit`), and the lax monoidal
structure of `Lj^*` is an isomorphism. By
`CategoryTheory.Adjunction.isIso_projectionMap_app_app_of_iso`
it therefore suffices that `Dj_! M ⊗ᴸ N` lies in the essential image of `Dj_!`, which is
`ProEtale.CondensedRing.tensorObj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek`
(see `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage`): on
K-flat representatives the derived tensor product is computed termwise, and the termwise
relative tensor products `j_! M^p ⊗_{Λ_X} N^q` lie in the essential image of `j_!` by the
projection formula for abelian sheaves.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The derived adjunction `Dj_! ⊣ Lj^*` along an open immersion `j`, with the derived pullback
`L((j)^*⟦Λ⟧)` (rather than the levelwise `D((j)^*⟦Λ⟧)`) as right adjoint. -/
noncomputable def derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' :
    D((j)_!open⟦Λ⟧) ⊣ L((j)^*⟦Λ⟧) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm

/-- The unit of the adjunction `Dj_! ⊣ Lj^*` along an open immersion `j` is an isomorphism. -/
instance isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_unit :
    IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).unit := by
  set adj := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j
  have (T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) : IsIso (adj.unit.app T) := by
    have h := Adjunction.homEquiv_ofNatIsoRight_apply
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm
      (𝟙 (D((j)_!open⟦Λ⟧).obj T))
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at h
    have h' : IsIso (adj.unit.app T ≫ 𝟙 _) := by
      erw [h]
      have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
        Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
      have := NatIso.isIso_app_of_isIso
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit T
      exact IsIso.comp_isIso' (IsIso.comp_isIso' this (IsIso.id _)) inferInstance
    exact IsIso.of_isIso_comp_right _ (𝟙 _)
  exact NatIso.isIso_of_isIso_app _

/-- The projection map `q_{j,M,N} : Dj_! (M ⊗ᴸ Lj^* N) ⟶ Dj_! M ⊗ᴸ N` of the adjunction
`Dj_! ⊣ Lj^*` along an open immersion `j`, as a natural transformation of bifunctors: the
transpose of
```
M ⊗ᴸ Lj^* N --(η ⊗ᴸ 1)--> Lj^* Dj_! M ⊗ᴸ Lj^* N --μ--> Lj^* (Dj_! M ⊗ᴸ N),
```
where `η` is the unit of `Dj_! ⊣ Lj^*` and `μ` the lax monoidal structure of `Lj^*`
(`CategoryTheory.Adjunction.projectionMap`). -/
noncomputable def openImmersionProjectionComparison' :
    (Functor.postcompose₂.obj D((j)_!open⟦Λ⟧)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((j)^*⟦Λ⟧)).obj (curriedTensor _)) ⟶
      (((Functor.whiskeringLeft₂ _).obj D((j)_!open⟦Λ⟧)).obj (𝟭 _)).obj (curriedTensor _) :=
  (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).projectionMap
    L((j)^*⟦Λ⟧) (curriedTensor _) (curriedTensor _)
    (Functor.LaxMonoidal.μNatTrans L((j)^*⟦Λ⟧))

/-- **The derived projection formula for the extension by zero**: the projection map
`q_{j,M,N} : Dj_! (M ⊗ᴸ Lj^* N) ⟶ Dj_! M ⊗ᴸ N` along an open immersion is an isomorphism. -/
instance isIso_openImmersionProjectionComparison'_app_app
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (((openImmersionProjectionComparison' Λ j).app M).app N) := by
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).fullyFaithfulLOfIsIsoUnit.full
  have :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso (Functor.LaxMonoidal.μNatTrans L((j)^*⟦Λ⟧)) := by
    have (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) : IsIso ((Functor.LaxMonoidal.μNatTrans L((j)^*⟦Λ⟧)).app K) := by
      have (Y : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))) :
          IsIso (((Functor.LaxMonoidal.μNatTrans L((j)^*⟦Λ⟧)).app K).app Y) :=
        inferInstanceAs (IsIso (Functor.LaxMonoidal.μ L((j)^*⟦Λ⟧) K Y))
      exact NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  obtain ⟨Z, ⟨e⟩⟩ := tensorObj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek Λ j M N
  exact Adjunction.isIso_projectionMap_app_app_of_iso _ _ _ _ _ M N Z e.symm

instance isIso_openImmersionProjectionComparison'_app
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    IsIso ((openImmersionProjectionComparison' Λ j).app M) :=
  NatIso.isIso_of_isIso_app _

instance isIso_openImmersionProjectionComparison' :
    IsIso (openImmersionProjectionComparison' Λ j) :=
  NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.ProEtale.CondensedRing
