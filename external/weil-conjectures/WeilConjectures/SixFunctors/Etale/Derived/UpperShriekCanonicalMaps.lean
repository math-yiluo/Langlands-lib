/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The canonical maps of the exceptional inverse image

For a finite coefficient ring `Λ` and a morphism `f : X ⟶ Y` admitting a compactification, two
canonical morphisms built from the adjunction `Rf_! ⊣ Rf^!`, which enter the definition of a
cohomologically smooth morphism (blueprint `proposition-exceptional-inverse-image-smooth-morphism`):

* the *tensor map* `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`, where `ω_f = Rf^! Λ_Y`: the adjunct of
  `Rf_!(ω_f ⊗ᴸ Lf^* K) ≅ Rf_! ω_f ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`, the inverse of the projection map
  (`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) followed by the counit;
  more generally, the tensor map `Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)`;
* the *base change map* `Rf^! ⋙ Lg'^* ⟶ Lg^* ⋙ Rf'^!` of a cartesian square
  `g' ≫ f = f' ≫ g`: the mate, under `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`, of the inverse of the
  compact-support base change isomorphism `Ex_! : Rf_! ⋙ Lg^* ≅ Lg'^* ⋙ Rf'_!`
  (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`), and its value
  `Lg'^* ω_f ⟶ ω_{f'}` at `Λ_Y`.

## Main definitions

- `AlgebraicGeometry.Etale.lowerShriekRightAdjointTensorMap`,
  `AlgebraicGeometry.Etale.lowerShriekRightAdjointUnitTensorMap`: the tensor maps of a right
  adjoint of `Rf_!`, for any coefficients satisfying the projection formula
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`,
  `AlgebraicGeometry.Etale.dualizingComplexTensorMap`
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`
- `AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Tensor

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]
  [IsIso (projectionMap A f)]
  {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}

/-- The **tensor map** `G M ⊗ᴸ Lf^* N ⟶ G(M ⊗ᴸ N)` of a right adjoint `G` of `Rf_!`, for a
morphism `f` admitting a compactification and satisfying the projection formula: the transpose
under `Rf_! ⊣ G` of `Rf_!(G M ⊗ᴸ Lf^* N) ≅ Rf_! G M ⊗ᴸ N ⟶ M ⊗ᴸ N`, the inverse of the
projection map followed by the counit (`CategoryTheory.Adjunction.projectionTensorMap`). For a
finite coefficient ring and `G = Rf^!` it is
`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`. -/
noncomputable abbrev lowerShriekRightAdjointTensorMap (adj : R(f)_![A] ⊣ G)
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    G.obj M ⊗ (L((f)^*[A])).obj N ⟶ G.obj (M ⊗ N) :=
  adj.projectionTensorMap (fun M N ↦ ((projectionMap A f).app M).app N) M N

/-- The **tensor map** `G Λ_Y ⊗ᴸ Lf^* K ⟶ G K` of a right adjoint `G` of `Rf_!`, for a morphism
`f` admitting a compactification and satisfying the projection formula: the tensor map
`AlgebraicGeometry.Etale.lowerShriekRightAdjointTensorMap` at `(Λ_Y, K)` followed by the left
unitor. For a finite coefficient ring and `G = Rf^!` it is
`AlgebraicGeometry.Etale.dualizingComplexTensorMap`. -/
noncomputable def lowerShriekRightAdjointUnitTensorMap (adj : R(f)_![A] ⊣ G)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensor A X).obj (G.obj (𝟙_ _))).obj ((L((f)^*[A])).obj K) ⟶ G.obj K :=
  lowerShriekRightAdjointTensorMap adj (𝟙_ _) K ≫ G.map (λ_ K).hom

end General

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

instance : IsIso (projectionMap (ModuleCat.{u + 1} Λ) f) :=
  isIso_projectionMap_of_finite Λ f

variable {Λ} in
/-- The **tensor map** `Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)` of a morphism `f` admitting a
compactification, for finite coefficients: the transpose under `Rf_! ⊣ Rf^!` of
`Rf_!(Rf^! M ⊗ᴸ Lf^* N) ≅ Rf_! Rf^! M ⊗ᴸ N ⟶ M ⊗ᴸ N`, the inverse of the projection map
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) followed by the counit
(`AlgebraicGeometry.Etale.lowerShriekRightAdjointTensorMap`). -/
noncomputable abbrev rightDerivedUpperShriekTensorMap
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(f)^![Λ]).obj M ⊗ (L((f)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ (R(f)^![Λ]).obj (M ⊗ N) :=
  lowerShriekRightAdjointTensorMap (rightDerivedUpperShriekAdjunction Λ f) M N

/-- The canonical **tensor map** `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` (blueprint
`proposition-exceptional-inverse-image-smooth-morphism`), for `ω_f = Rf^! Λ_Y` and finite
coefficients: the adjunct under `Rf_! ⊣ Rf^!` of
`Rf_!(ω_f ⊗ᴸ Lf^* K) ≅ Rf_! ω_f ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`, the inverse of the projection map
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) followed by the counit and the left unitor
(`AlgebraicGeometry.Etale.lowerShriekRightAdjointUnitTensorMap`). -/
noncomputable def dualizingComplexTensorMap
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex Λ f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶
      (R(f)^![Λ]).obj K :=
  lowerShriekRightAdjointUnitTensorMap (rightDerivedUpperShriekAdjunction Λ f) K

end Tensor

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- The canonical **base change map** `Rf^! ⋙ Lg'^* ⟶ Lg^* ⋙ Rf'^!` of a cartesian square
`g' ≫ f = f' ≫ g`

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

the mate, under the adjunctions `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`, of the inverse of the
compact-support base change isomorphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). -/
noncomputable def rightDerivedUpperShriekBaseChangeMap (sq : IsPullback g' f' f g) :
    R(f)^![Λ] ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')^![Λ] :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  mateEquiv (rightDerivedUpperShriekAdjunction _ f) (rightDerivedUpperShriekAdjunction _ f')
    (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))

/-- The canonical base change map `Lg'^* ω_f ⟶ ω_{f'}` of the dualizing complexes of a cartesian
square `g' ≫ f = f' ≫ g` (blueprint `proposition-exceptional-inverse-image-smooth-morphism`): the
component of `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap` at `Λ_Y`, followed by
`Rf'^!(Lg^* Λ_Y ≅ Λ_{Y'})`. -/
noncomputable def dualizingComplexBaseChangeMap (sq : IsPullback g' f' f g) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) ⟶
      dualizingComplex Λ f' :=
  (rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _) ≫
    (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom

/-- The base change map of the dualizing complexes is an isomorphism as soon as the base change
map of `R^!` is one at `Λ_Y`. -/
lemma isIso_dualizingComplexBaseChangeMap_iff (sq : IsPullback g' f' f g) :
    IsIso (dualizingComplexBaseChangeMap Λ sq) ↔
      IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _)) := by
  rw [dualizingComplexBaseChangeMap, isIso_comp_right_iff]

end BaseChange

end Etale

end AlgebraicGeometry
