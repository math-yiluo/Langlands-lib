/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal

/-!
# The projection map for the derived pushforward

Let `p : X ⟶ Y` be a morphism of schemes. We construct the projection map
`Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)`, natural in `M` in `D(X_proét)` and `L` in `D(Y_proét)`, as the
specialisation of the general `CategoryTheory.Adjunction.rightAdjointProjectionMap` to the
adjunction `Lp^* ⊣ Rp_*` and the comparison
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`. Its transpose along
`Lp^* ⊣ Rp_*` is given by the diagram
```
Lp^*(Rp_*M ⊗ᴸ L) --comparison--> Lp^*Rp_*M ⊗ᴸ Lp^*L
        \                               |
         \                              | ε_M ⊗ᴸ 𝟙
       transpose                        v
           ---------------------->  M ⊗ᴸ Lp^*L
```
where the comparison is `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`, the long
edge is `(homEquiv _ _).symm` of the projection map and `ε` is the counit of
`AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction`.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.derivedTensorRightDerivedLowerStar p` and
  `AlgebraicGeometry.ProEtale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar p`: the
  bifunctors `(M, L) ↦ Rp_*M ⊗ᴸ L` and `(M, L) ↦ Rp_*(M ⊗ᴸ Lp^*L)`, of type
  `D(X_proét) ⥤ D(Y_proét) ⥤ D(Y_proét)`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap p`: the projection map, as a
  natural transformation between these bifunctors.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap_app_app`: its value at `(M, L)`
  is the transpose of the composite in the diagram above.
- `AlgebraicGeometry.ProEtale.homEquiv_symm_rightDerivedLowerStarProjectionMap`: its transpose
  is the composite in the diagram above.

The results depend on `sorryAx` through `AlgebraicGeometry.ProEtale.derivedTensor`.

## TODO

- The projection formula at finite coefficients, currently stated with `Nonempty` in the
  `TODO(unify)` of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Exchange`, should
  be restated through `AlgebraicGeometry.ProEtale.projectionMap`, which is built from this
  projection map in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`.
- The pro-pro-étale and `O_E`/`E`-coefficient projection maps should be obtained in the same way
  from `CategoryTheory.Adjunction.rightAdjointProjectionMap`.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The bifunctor `(M, L) ↦ Rp_*M ⊗ᴸ L`, of type `D(X_proét) ⥤ D(Y_proét) ⥤ D(Y_proét)`. -/
noncomputable def derivedTensorRightDerivedLowerStar :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  R((p)_*[A]) ⋙ -⊗ᴸ-(Y)[A]

@[simp]
lemma derivedTensorRightDerivedLowerStar_obj_obj
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((derivedTensorRightDerivedLowerStar A p).obj M).obj L =
      ((-⊗ᴸ-(Y)[A]).obj (R((p)_*[A]).obj M)).obj L :=
  rfl

/-- The bifunctor `(M, L) ↦ Rp_*(M ⊗ᴸ Lp^*L)`, of type `D(X_proét) ⥤ D(Y_proét) ⥤ D(Y_proét)`. -/
noncomputable def rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  (Functor.postcompose₂.obj R((p)_*[A])).obj
    ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((p)^*[A])).obj (-⊗ᴸ-(X)[A]))

@[simp]
lemma rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar_obj_obj
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A p).obj M).obj L =
      R((p)_*[A]).obj (((-⊗ᴸ-(X)[A]).obj M).obj (L((p)^*[A]).obj L)) :=
  rfl

variable [ProEtale.UpperStarPreservesFlat A]

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` for the derived pushforward along
`p : X ⟶ Y`, as a natural transformation of bifunctors `D(X_proét) ⥤ D(Y_proét) ⥤ D(Y_proét)`.
It is `CategoryTheory.Adjunction.rightAdjointProjectionMap` for the adjunction
`AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction` and the comparison
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`. -/
noncomputable def rightDerivedLowerStarProjectionMap :
    derivedTensorRightDerivedLowerStar A p ⟶
      rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A p :=
  (derivedUpperStarLowerStarAdjunction A p).rightAdjointProjectionMap
    (leftDerivedUpperStarTensorComparison A p)

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` at `(M, L)` is the transpose along
`Lp^* ⊣ Rp_*` of the comparison `Lp^*(Rp_*M ⊗ᴸ L) ⟶ Lp^*Rp_*M ⊗ᴸ Lp^*L` followed by
`ε_M ⊗ᴸ 𝟙`. -/
lemma rightDerivedLowerStarProjectionMap_app_app
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((rightDerivedLowerStarProjectionMap A p).app M).app L =
      (derivedUpperStarLowerStarAdjunction A p).homEquiv _ _
        (((leftDerivedUpperStarTensorComparison A p).app (R((p)_*[A]).obj M)).app L ≫
          ((-⊗ᴸ-(X)[A]).map ((derivedUpperStarLowerStarAdjunction A p).counit.app M)).app
            (L((p)^*[A]).obj L)) :=
  rfl

/-- The transpose along `Lp^* ⊣ Rp_*` of the projection map
`Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` is the composite
```
Lp^*(Rp_*M ⊗ᴸ L) --comparison--> Lp^*Rp_*M ⊗ᴸ Lp^*L
        \                               |
         \                              | ε_M ⊗ᴸ 𝟙
       transpose                        v
           ---------------------->  M ⊗ᴸ Lp^*L
```
where the comparison is `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`, the long
edge is `(homEquiv _ _).symm` of the projection map and `ε` is the counit of
`AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction`. -/
@[simp, reassoc]
lemma homEquiv_symm_rightDerivedLowerStarProjectionMap
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((derivedUpperStarLowerStarAdjunction A p).homEquiv _ _).symm
        (((rightDerivedLowerStarProjectionMap A p).app M).app L) =
      ((leftDerivedUpperStarTensorComparison A p).app (R((p)_*[A]).obj M)).app L ≫
        ((-⊗ᴸ-(X)[A]).map ((derivedUpperStarLowerStarAdjunction A p).counit.app M)).app
          (L((p)^*[A]).obj L) :=
  Adjunction.homEquiv_symm_rightAdjointProjectionMap_app_app _ _ M L

/-- The counit form of
`AlgebraicGeometry.ProEtale.homEquiv_symm_rightDerivedLowerStarProjectionMap`: applying `Lp^*`
to the projection map and composing with the counit of `Lp^* ⊣ Rp_*` gives the comparison
followed by `ε_M ⊗ᴸ 𝟙`. -/
@[reassoc]
lemma map_rightDerivedLowerStarProjectionMap_comp_counit
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    L((p)^*[A]).map (((rightDerivedLowerStarProjectionMap A p).app M).app L) ≫
        (derivedUpperStarLowerStarAdjunction A p).counit.app _ =
      ((leftDerivedUpperStarTensorComparison A p).app (R((p)_*[A]).obj M)).app L ≫
        ((-⊗ᴸ-(X)[A]).map ((derivedUpperStarLowerStarAdjunction A p).counit.app M)).app
          (L((p)^*[A]).obj L) :=
  Adjunction.map_rightAdjointProjectionMap_app_app_comp_counit _ _ M L

end ProEtale

end AlgebraicGeometry
