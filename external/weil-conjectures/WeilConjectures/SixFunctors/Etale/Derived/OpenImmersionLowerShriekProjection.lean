/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# The projection formula for the extension by zero along an open immersion

Let `j : U ⟶ X` be an open immersion. For `K` in `D(U_ét)` and `M` in `D(X_ét)` there is a
canonical morphism
```
j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M
```
in `D(X_ét)`: the projection map `CategoryTheory.Adjunction.projectionMap` of the adjunction
`D(j_!) ⊣ D(j^*)`, i.e. the transpose along `j_! ⊣ j^*` of
```
K ⊗ᴸ Lj^*M --(η ⊗ᴸ 1)--> j^*(j_!K) ⊗ᴸ Lj^*M ≅ j^*(j_!K ⊗ᴸ M),
```
where `η` is the unit of `j_! ⊣ j^*` and the isomorphism comes from the inverse of
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`. It is an isomorphism.

The projection map `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of the blueprint
(`WeilConjectures.SixFunctors.Etale.Derived.Exchange`) goes in the opposite direction: its
open part is the inverse `(derivedOpenImmersionLowerShriekProjectionIso j).inv`.

## Main definitions and results

- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionMap j`: the morphism
  `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` of bifunctors `D(U_ét) ⥤ D(X_ét) ⥤ D(X_ét)`.
- `AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekProjectionMap`: it is an
  isomorphism.
- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso j`: the resulting
  isomorphism of bifunctors.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

open _root_.DerivedCategory

variable [Etale.UpperStarPreservesFlat A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The bifunctor `(K, M) ↦ K ⊗ᴸ Lj^*M`, of type `D(U_ét) ⥤ D(X_ét) ⥤ D(U_ét)`: the derived
tensor product with `Lj^*` applied to the right argument. -/
noncomputable abbrev derivedTensorWhiskeringRightLeftDerivedUpperStar :
    DerivedCategory (Sheaf U.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf U.smallEtaleTopology A) :=
  (((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((j)^*[A])).obj (-⊗ᴸ-(U)[A])

/-- The bifunctor `(K, M) ↦ j_!K ⊗ᴸ M`, of type `D(U_ét) ⥤ D(X_ét) ⥤ D(X_ét)`: the derived
tensor product with `j_!` applied to the left argument. -/
noncomputable abbrev derivedTensorWhiskeringLeftOpenImmersionLowerShriek :
    DerivedCategory (Sheaf U.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (((Functor.whiskeringLeft₂ _).obj D((j)_!open[A])).obj (𝟭 _)).obj (-⊗ᴸ-(X)[A])

/-- The isomorphism `j^*X ⊗ᴸ Lj^*Y ≅ j^*(X ⊗ᴸ Y)` of bifunctors
`D(X_ét) ⥤ D(X_ét) ⥤ D(U_ét)`, the composite
```
j^*X ⊗ᴸ Lj^*Y ≅ Lj^*X ⊗ᴸ Lj^*Y ≅ Lj^*(X ⊗ᴸ Y) ≅ j^*(X ⊗ᴸ Y)
```
of `Lj^* ≅ D(j^*)` and the inverse of `leftDerivedUpperStarTensorComparison`. -/
noncomputable def mapDerivedCategoryUpperStarDerivedTensorIso :
    (((Functor.whiskeringLeft₂ _).obj D((j)^*[A])).obj L((j)^*[A])).obj (-⊗ᴸ-(U)[A]) ≅
      (Functor.postcompose₂.obj D((j)^*[A])).obj (-⊗ᴸ-(X)[A]) :=
  (((Functor.whiskeringLeft₂ _).mapIso (leftDerivedUpperStarIsoMapDerivedCategory A j).symm).app
      L((j)^*[A])).app (-⊗ᴸ-(U)[A]) ≪≫
    (leftDerivedUpperStarTensorNatIso A j).symm ≪≫
    (Functor.postcompose₂.mapIso (leftDerivedUpperStarIsoMapDerivedCategory A j)).app
      (-⊗ᴸ-(X)[A])

/-- The **projection map** `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` of bifunctors
`D(U_ét) ⥤ D(X_ét) ⥤ D(X_ét)`, for an open immersion `j : U ⟶ X`: the projection map
`Adjunction.projectionMap` of `D(j_!) ⊣ D(j^*)` with respect to
`mapDerivedCategoryUpperStarDerivedTensorIso`. It is the composite
```
j_!(K ⊗ᴸ Lj^*M) --j_!(φ)--> j_! j^*(j_!K ⊗ᴸ M) --ε--> j_!K ⊗ᴸ M
```
where `ε` is the counit of `j_! ⊣ j^*` and `φ` is the composite
```
K ⊗ᴸ Lj^*M --(η ⊗ᴸ 1)--> j^*(j_!K) ⊗ᴸ Lj^*M ≅ j^*(j_!K ⊗ᴸ M).
```
The blueprint's projection map `PF` goes in the opposite direction; it is the inverse of
`derivedOpenImmersionLowerShriekProjectionIso`. -/
noncomputable def derivedOpenImmersionLowerShriekProjectionMap :
    (Functor.postcompose₂.obj D((j)_!open[A])).obj
        (derivedTensorWhiskeringRightLeftDerivedUpperStar A j) ⟶
      derivedTensorWhiskeringLeftOpenImmersionLowerShriek A j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).projectionMap L((j)^*[A])
    (-⊗ᴸ-(U)[A]) (-⊗ᴸ-(X)[A]) (mapDerivedCategoryUpperStarDerivedTensorIso A j).hom

/-- The projection map `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` is an isomorphism. -/
instance isIso_derivedOpenImmersionLowerShriekProjectionMap
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    IsIso (derivedOpenImmersionLowerShriekProjectionMap A j) := by
  have key (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
      IsIso ((derivedOpenImmersionLowerShriekProjectionMap A j).app K) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    -- By open–closed conservativity it suffices to check this after `Lj^*` and after the
    -- derived pullback to the closed complement of `j`.
    refine isIso_of_isIso_leftDerivedUpperStar_closedComplement_map A j _ ?_ ?_
    · -- After `Lj^* ≅ D(j^*)`, it is an isomorphism since the unit of `j_! ⊣ j^*` is.
      rw [NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory A j)]
      exact Adjunction.isIso_map_projectionMap_app_app _ _ _ _ _ K M
    · -- On the closed complement both sides vanish, since `j_!` does.
      exact isIso_of_source_target_iso_zero _
        (isZero_leftDerivedUpperStar_closedComplement_obj_openImmersionLowerShriek A j
          (((-⊗ᴸ-(U)[A]).obj K).obj (L((j)^*[A]).obj M))).isoZero
        ((isZero_derivedTensor_obj_obj_of_isZero_left
          (isZero_leftDerivedUpperStar_closedComplement_obj_openImmersionLowerShriek A j K)
          (L((j.closedComplement)^*[A]).obj M)).of_iso
            (leftDerivedUpperStarTensorIso A j.closedComplement _ M)).isoZero
  exact NatIso.isIso_of_isIso_app _

/-- The **projection formula** for an open immersion `j : U ⟶ X`: the isomorphism
`j_!(K ⊗ᴸ Lj^*M) ≅ j_!K ⊗ᴸ M` of bifunctors `D(U_ét) ⥤ D(X_ét) ⥤ D(X_ét)`, whose underlying
morphism is `derivedOpenImmersionLowerShriekProjectionMap`. Its inverse is the open part of
the blueprint's projection map `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)`. -/
noncomputable def derivedOpenImmersionLowerShriekProjectionIso
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    (Functor.postcompose₂.obj D((j)_!open[A])).obj
        (derivedTensorWhiskeringRightLeftDerivedUpperStar A j) ≅
      derivedTensorWhiskeringLeftOpenImmersionLowerShriek A j :=
  asIso (derivedOpenImmersionLowerShriekProjectionMap A j)

@[simp]
lemma derivedOpenImmersionLowerShriekProjectionIso_hom
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    (derivedOpenImmersionLowerShriekProjectionIso A j).hom =
      derivedOpenImmersionLowerShriekProjectionMap A j :=
  rfl

end Etale

end AlgebraicGeometry
