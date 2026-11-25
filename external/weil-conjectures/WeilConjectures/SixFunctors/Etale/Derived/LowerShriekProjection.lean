/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-!
# The projection map for the compactly supported direct image

Let `f : X ⟶ Y` be a morphism of schemes with a compactification
`c = (X ⟶[i] Z ⟶[g] Y)`, so that `Rf_!(c) = Di_! ⋙ Rg_*`. We construct the projection map
```
PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)
```
natural in `K` in `D(X_ét)` and `L` in `D(Y_ét)`, as the composite
```
Rg_*(i_!K) ⊗ᴸ L ⟶ Rg_*(i_!K ⊗ᴸ Lg^*L)          (projection map of `Rg_*`)
                ≅ Rg_*(i_!(K ⊗ᴸ Li^*Lg^*L))     (projection formula for `i_!`)
                ≅ Rg_*(i_!(K ⊗ᴸ Lf^*L))         (`Lg^* ⋙ Li^* ≅ L(i ≫ g)^*` and `f = i ≫ g`)
```
of `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`, of the inverse of
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso` and of
`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`.

## Main definitions and results

- `AlgebraicGeometry.Etale.derivedTensorRightDerivedLowerShriek c` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar c`: the
  bifunctors `(K, L) ↦ Rf_!(c)K ⊗ᴸ L` and `(K, L) ↦ Rf_!(c)(K ⊗ᴸ Lf^*L)`, of type
  `D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`.
- `AlgebraicGeometry.Etale.projectionMapOfCompactification c`: the projection map `PF_c`, as a
  natural transformation between these bifunctors.
- `AlgebraicGeometry.Etale.projectionMap f`: the projection map for the chosen
  compactification `HasCompactification.compactification f`.
- `AlgebraicGeometry.Etale.projectionMapOfCompactification_app_app`: the value of `PF_c` at
  `(K, L)` is the composite above.

The results depend on `sorryAx` through `AlgebraicGeometry.Etale.derivedTensor`.
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

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The bifunctor `(K, L) ↦ Rf_!(c)K ⊗ᴸ L`, of type `D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`. -/
noncomputable def derivedTensorRightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  Rf_!(c)[A] ⋙ -⊗ᴸ-(Y)[A]

@[simp]
lemma derivedTensorRightDerivedLowerShriek_obj_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensorRightDerivedLowerShriek A c).obj K).obj L =
      ((-⊗ᴸ-(Y)[A]).obj ((Rf_!(c)[A]).obj K)).obj L :=
  rfl

/-- The bifunctor `(K, L) ↦ Rf_!(c)(K ⊗ᴸ Lf^*L)`, of type `D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`. -/
noncomputable def rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Functor.postcompose₂.obj Rf_!(c)[A]).obj
    ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((f)^*[A])).obj (-⊗ᴸ-(X)[A]))

@[simp]
lemma rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A c).obj K).obj L =
      (Rf_!(c)[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) :=
  rfl

/-- The isomorphism `Li^* ∘ Lg^* ≅ Lf^*` (that is, `Lg^* ⋙ Li^* ≅ Lf^*`) for a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`: the inverse of
`AlgebraicGeometry.Etale.leftDerivedUpperStarComp` transported along `f = i ≫ g`. -/
noncomputable def leftDerivedUpperStarCompactificationIso :
    L((c.g)^*[A]) ⋙ L((c.i)^*[A]) ≅ L((f)^*[A]) :=
  (leftDerivedUpperStarComp A c.i c.g).symm ≪≫
    eqToIso (congrArg (fun h ↦ L((h)^*[A])) c.comm.symm)

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The **projection map** `PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)` for a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, as a natural transformation of bifunctors
`D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`. It is the composite
```
Rg_*(i_!K) ⊗ᴸ L ⟶ Rg_*(i_!K ⊗ᴸ Lg^*L) ≅ Rg_*(i_!(K ⊗ᴸ Li^*Lg^*L)) ≅ Rg_*(i_!(K ⊗ᴸ Lf^*L))
```
of the projection map `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap` of `g`, of
`Rg_*` applied to the inverse of the projection formula
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso` for `i`, and of the
isomorphism `AlgebraicGeometry.Etale.leftDerivedUpperStarCompactificationIso`. -/
noncomputable def projectionMapOfCompactification :
    derivedTensorRightDerivedLowerShriek A c ⟶
      rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A c :=
  Functor.whiskerLeft D((c.i)_!open[A]) (rightDerivedLowerStarProjectionMap A c.g) ≫
    (Functor.postcompose₂.obj R((c.g)_*[A])).map
      (Functor.whiskerRight (derivedOpenImmersionLowerShriekProjectionIso A c.i).inv
        ((Functor.whiskeringLeft _ _ _).obj L((c.g)^*[A]))) ≫
    (Functor.postcompose₂.obj R((c.g)_*[A])).map
      (Functor.whiskerLeft ((Functor.postcompose₂.obj D((c.i)_!open[A])).obj (-⊗ᴸ-(X)[A]))
        ((Functor.whiskeringLeft _ _ _).map (leftDerivedUpperStarCompactificationIso A c).hom))

/-- The value of the projection map `PF_c` at `(K, L)` is the composite
```
Rg_*(i_!K) ⊗ᴸ L ⟶ Rg_*(i_!K ⊗ᴸ Lg^*L) ≅ Rg_*(i_!(K ⊗ᴸ Li^*Lg^*L)) ≅ Rg_*(i_!(K ⊗ᴸ Lf^*L)).
``` -/
lemma projectionMapOfCompactification_app_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app K).app L =
      ((rightDerivedLowerStarProjectionMap A c.g).app (D((c.i)_!open[A]).obj K)).app L ≫
        R((c.g)_*[A]).map
          (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
            (L((c.g)^*[A]).obj L)) ≫
        R((c.g)_*[A]).map (D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
          ((leftDerivedUpperStarCompactificationIso A c).hom.app L))) :=
  rfl

/-- Blueprint `sk-def-sf-exchanges`: Exchange and projection transformations, typed (the
projection transformation `PF_{f,K,L}`; also the projection transformation of `def-sf-pf`).

The **projection map** `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` for a morphism
`f : X ⟶ Y` admitting a compactification: the projection map
`AlgebraicGeometry.Etale.projectionMapOfCompactification` for the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def projectionMap (f : X ⟶ Y) [HasCompactification f] :
    derivedTensorRightDerivedLowerShriek A (HasCompactification.compactification f) ⟶
      rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A
        (HasCompactification.compactification f) :=
  projectionMapOfCompactification A (HasCompactification.compactification f)

end Etale

end AlgebraicGeometry
