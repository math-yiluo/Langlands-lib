/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection

/-!
# The projection formula for the extension by zero along an open immersion

Let `j : U ⟶ X` be an open immersion. For `K` in `D(U_proét)` and `M` in `D(X_proét)` there is a
canonical morphism
```
j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M
```
in `D(X_proét)`: the projection map `CategoryTheory.Adjunction.projectionMap` of the adjunction
`D(j_!) ⊣ D(j^*)`, i.e. the transpose along `j_! ⊣ j^*` of
```
K ⊗ᴸ Lj^*M --(η ⊗ᴸ 1)--> j^*(j_!K) ⊗ᴸ Lj^*M ≅ j^*(j_!K ⊗ᴸ M),
```
where `η` is the unit of `j_! ⊣ j^*` and the isomorphism comes from the inverse of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`. It is an isomorphism.

The projection map `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of the blueprint
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Exchange`) goes in the opposite
direction: its open part is the inverse `(derivedOpenImmersionLowerShriekProjectionIso j).inv`.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionMap j`: the morphism
  `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` of bifunctors `D(U_proét) ⥤ D(X_proét) ⥤ D(X_proét)`.
- `AlgebraicGeometry.ProEtale.isIso_derivedOpenImmersionLowerShriekProjectionMap`: it is an
  isomorphism.
- `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso j`: the resulting
  isomorphism of bifunctors.
- `AlgebraicGeometry.ProEtale.derivedTensorOpenImmersionLowerShriekIso j K L`: the projection
  formula `j_!K ⊗ᴸ L ≅ j_!(K ⊗ᴸ Lj^*L)` (blueprint `lemma-change-coefficients-compact-support`).

## The argument

The unit of `D(j_!) ⊣ D(j^*)` is an isomorphism, so by
`CategoryTheory.Adjunction.isIso_projectionMap_app_app_of_iso` it suffices that `j_!K ⊗ᴸ M` lies
in the essential image of `D(j_!)`. Writing `K` as a complex `K₀` and `M` as a K-flat complex
`M₁`, the derived tensor product is computed termwise, `j_!K ⊗ᴸ M ≅ Q(j_!K₀ ⊗ M₁)`, and the
termwise projection isomorphisms
`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekProjectionMap_app_app` of sheaves
assemble to an isomorphism of complexes `j_!(K₀ ⊗ j^*M₁) ≅ j_!K₀ ⊗ M₁`
(`HomologicalComplex.mapBifunctorComparison`).
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

namespace ProEtale

open DerivedCategory

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The bifunctor `(K, M) ↦ K ⊗ j^*M` on pro-étale sheaves, of type
`Sheaf U ⥤ Sheaf X ⥤ Sheaf U`. -/
noncomputable abbrev tensorUpperStar :
    Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology X) A ⥤
      Sheaf (Scheme.ProEt.topology U) A :=
  (((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj (j)^*[A]).obj (curriedTensor _)

instance : (tensorUpperStar A j).PreservesZeroMorphisms where
  map_zero _ _ := by ext; simp

instance (K : Sheaf (Scheme.ProEt.topology U) A) :
    ((tensorUpperStar A j).obj K).PreservesZeroMorphisms where
  map_zero _ _ := by simp

/-- The termwise projection formula: for complexes `K₀` on `U_proét` and `M₁` on `X_proét`, the
isomorphism of complexes `j_!(K₀ ⊗ j^*M₁) ≅ j_!K₀ ⊗ M₁` induced by the projection isomorphisms
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekProjectionMap` of sheaves. -/
noncomputable def openImmersionLowerShriekMapBifunctorIso
    (K₀ : CochainComplex (Sheaf (Scheme.ProEt.topology U) A) ℤ)
    (M₁ : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ) :
    (((j)_!open[A]).mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K₀ M₁ (tensorUpperStar A j) (.up ℤ)) ≅
      (((j)_!open[A]).mapHomologicalComplex (.up ℤ)).obj K₀ ⊗ M₁ :=
  have : ∀ K M, IsIso (((openImmersionLowerShriekProjectionMap A j).app K).app M) :=
    fun _ _ ↦ inferInstance
  have : IsIso (HomologicalComplex.mapBifunctorComparison
      (openImmersionLowerShriekProjectionMap A j) (.up ℤ) K₀ M₁) := by
    apply HomologicalComplex.Hom.isIso_of_components
  @asIso _ _ _ _ _ this

/-- For `K` in `D(U_proét)` and `M` in `D(X_proét)`, the derived tensor product `j_!K ⊗ᴸ M` lies
in the essential image of `D(j_!)`: with `K = Q K₀` and `M = Qh M₁` for a K-flat `M₁`, it is
`D(j_!)` of `Q(K₀ ⊗ j^*M₁)` by `openImmersionLowerShriekMapBifunctorIso`. -/
lemma exists_derivedTensor_openImmersionLowerShriek_iso
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ∃ Z, Nonempty (((-⊗ᴸ-(X)[A]).obj (D((j)_!open[A]).obj K)).obj M ≅
      D((j)_!open[A]).obj Z) := by
  let R : (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A)
      (.up ℤ)).localizerMorphismKFlat.LeftResolution (Qh.objPreimage M) :=
    Classical.arbitrary _
  let eM : Qh.obj R.X₁.obj ≅ M :=
    Localization.isoOfHom Qh (HomotopyCategory.quasiIso _ (.up ℤ)) R.w R.hw ≪≫
      Qh.objObjPreimageIso M
  let K₀ := Q.objPreimage K
  let K₁ := (((j)_!open[A]).mapHomologicalComplex (.up ℤ)).obj K₀
  let M₁ := R.X₁.obj.as
  have := isIso_μNatTrans_Qh_app_app_of_kFlat ((HomotopyCategory.quotient _ _).obj K₁)
    R.X₁.obj R.X₁.property
  exact ⟨Q.obj (HomologicalComplex.mapBifunctor K₀ M₁ (tensorUpperStar A j) (.up ℤ)),
    ⟨((-⊗ᴸ-(X)[A]).mapIso (D((j)_!open[A]).mapIso (Q.objObjPreimageIso K).symm ≪≫
        (((j)_!open[A]).mapDerivedCategoryFactors.app K₀) ≪≫
        ((quotientCompQhIso _).app K₁).symm)).app M ≪≫
      ((-⊗ᴸ-(X)[A]).obj _).mapIso eM.symm ≪≫
      asIso (((Functor.LaxMonoidal.μNatTrans Qh).app _).app R.X₁.obj) ≪≫
      Qh.mapIso (Functor.Monoidal.μIso (HomotopyCategory.quotient _ _) K₁ M₁).symm ≪≫
      (quotientCompQhIso _).app (K₁ ⊗ M₁) ≪≫
      Q.mapIso (openImmersionLowerShriekMapBifunctorIso A j K₀ M₁).symm ≪≫
      (((j)_!open[A]).mapDerivedCategoryFactors.app _).symm⟩⟩

variable [ProEtale.UpperStarPreservesFlat A]

/-- The bifunctor `(K, M) ↦ K ⊗ᴸ Lj^*M`, of type `D(U_proét) ⥤ D(X_proét) ⥤ D(U_proét)`: the derived
tensor product with `Lj^*` applied to the right argument. -/
noncomputable abbrev derivedTensorWhiskeringRightLeftDerivedUpperStar :
    DerivedCategory (Sheaf (Scheme.ProEt.topology U) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology U) A) :=
  (((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((j)^*[A])).obj (-⊗ᴸ-(U)[A])

/-- The bifunctor `(K, M) ↦ j_!K ⊗ᴸ M`, of type `D(U_proét) ⥤ D(X_proét) ⥤ D(X_proét)`: the derived
tensor product with `j_!` applied to the left argument. -/
noncomputable abbrev derivedTensorWhiskeringLeftOpenImmersionLowerShriek :
    DerivedCategory (Sheaf (Scheme.ProEt.topology U) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (((Functor.whiskeringLeft₂ _).obj D((j)_!open[A])).obj (𝟭 _)).obj (-⊗ᴸ-(X)[A])

/-- The isomorphism `j^*X ⊗ᴸ Lj^*Y ≅ j^*(X ⊗ᴸ Y)` of bifunctors
`D(X_proét) ⥤ D(X_proét) ⥤ D(U_proét)`, the composite
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
`D(U_proét) ⥤ D(X_proét) ⥤ D(X_proét)`, for an open immersion `j : U ⟶ X`: the projection map
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
instance isIso_derivedOpenImmersionLowerShriekProjectionMap :
    IsIso (derivedOpenImmersionLowerShriekProjectionMap A j) := by
  have : IsIso (ProEtale.openImmersionLowerShriekUpperStarAdjunction A j).unit :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction A j).unit_isIso_of_L_fully_faithful
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A))
      (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
      IsIso (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M) := by
    obtain ⟨Z, ⟨e⟩⟩ := exists_derivedTensor_openImmersionLowerShriek_iso A j K M
    exact Adjunction.isIso_projectionMap_app_app_of_iso _ _ _ _ _ K M Z e
  have (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)) :
      IsIso ((derivedOpenImmersionLowerShriekProjectionMap A j).app K) :=
    NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- The **projection formula** for an open immersion `j : U ⟶ X`: the isomorphism
`j_!(K ⊗ᴸ Lj^*M) ≅ j_!K ⊗ᴸ M` of bifunctors `D(U_proét) ⥤ D(X_proét) ⥤ D(X_proét)`, whose underlying
morphism is `derivedOpenImmersionLowerShriekProjectionMap`. Its inverse is the open part of
the blueprint's projection map `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)`. -/
noncomputable def derivedOpenImmersionLowerShriekProjectionIso :
    (Functor.postcompose₂.obj D((j)_!open[A])).obj
        (derivedTensorWhiskeringRightLeftDerivedUpperStar A j) ≅
      derivedTensorWhiskeringLeftOpenImmersionLowerShriek A j :=
  asIso (derivedOpenImmersionLowerShriekProjectionMap A j)

@[simp]
lemma derivedOpenImmersionLowerShriekProjectionIso_hom :
    (derivedOpenImmersionLowerShriekProjectionIso A j).hom =
      derivedOpenImmersionLowerShriekProjectionMap A j :=
  rfl


/-- Blueprint `lemma-change-coefficients-compact-support`: Projection formula for extension by
zero.

For an open immersion `j : U ⟶ X`, `K` in `D(U_proét)` and `L` in `D(X_proét)`, the canonical map
`(j_!K) ⊗ᴸ L ⟶ j_!(K ⊗ᴸ Lj^*L)` is an isomorphism; it is the inverse of the projection map
`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionMap` (the transpose along
`j_! ⊣ j^*` of `(η ⊗ᴸ 1)`, `η` the unit of `j_! ⊣ j^*`). This holds for every coefficient category
`A` as above, in particular for `A = ModuleCat Λ` with `Λ` a finite ring. -/
noncomputable def derivedTensorOpenImmersionLowerShriekIso
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((-⊗ᴸ-(X)[A]).obj (D((j)_!open[A]).obj K)).obj L ≅
      D((j)_!open[A]).obj (((-⊗ᴸ-(U)[A]).obj K).obj (L((j)^*[A]).obj L)) :=
  (((derivedOpenImmersionLowerShriekProjectionIso A j).app K).app L).symm

lemma derivedTensorOpenImmersionLowerShriekIso_inv
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (derivedTensorOpenImmersionLowerShriekIso A j K L).inv =
      ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app L :=
  rfl

end ProEtale

end AlgebraicGeometry
