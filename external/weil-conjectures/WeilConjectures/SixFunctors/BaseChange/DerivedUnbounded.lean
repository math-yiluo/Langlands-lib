/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# The derived base change map `Lg^* Rf_* ⟶ Rf'_* Lg'^*` on unbounded derived categories

For a commutative square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

(`sq : CommSq g' f' f g`) the two composites `Lf'^* ∘ Lg^*` and `Lg'^* ∘ Lf^*` of derived
pullbacks on the unbounded derived categories `D(-_ét)` are both identified with the derived
pullback along the diagonal `g' ≫ f = f' ≫ g` by
`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`. This gives the *derived square
isomorphism* `AlgebraicGeometry.Etale.derivedSquareUpperStarIso sq : Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*`,
the derived analogue of `AlgebraicGeometry.Etale.squareUpperStarIso`.

The **derived base change map** `AlgebraicGeometry.Etale.derivedBaseChangeMap sq :
Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`, that is `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*`, is the mate
(`CategoryTheory.mateEquiv`) of the derived square isomorphism with respect to the derived
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`, exactly as the underived
`AlgebraicGeometry.Etale.baseChangeMap` is the mate of `AlgebraicGeometry.Etale.squareUpperStarIso`.
It is the exchange `Ex_*` on the unbounded derived categories, which the exchange `Ex_!` needs
since `Rf_!` lives there.

```
  D(X) --Lg'^*--> D(X')
   |               |
  Rf_*   ⇓ Ex_*   Rf'_*
   ↓               ↓
  D(Y) --Lg^*---> D(Y')
```

As for the mate of any 2-square, its adjoint `Lf'^* Lg^* Rf_* K ⟶ Lg'^* K` is the derived
square isomorphism followed by `Lg'^*` of the counit of `Lf^* ⊣ Rf_*`
(`AlgebraicGeometry.Etale.derivedUpperStar_map_derivedBaseChangeMap_app_counit`), and its
composite with the unit of `Lf^* ⊣ Rf_*` is the unit of `Lf'^* ⊣ Rf'_*` followed by `Rf'_*` of
the derived square isomorphism (`AlgebraicGeometry.Etale.map_unit_derivedBaseChangeMap_app`).

(blueprint: `def:weil-pbc-derived-exchange-unbounded`)

## TODO

* Show that `AlgebraicGeometry.Etale.derivedBaseChangeMap` restricts on `D⁺` to
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.
* Show that the conjugate of `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` along the derived
  adjunctions is the composition isomorphism of derived pushforwards, and deduce the pushforward
  form of `Ex_*` and its invertibility for universal homeomorphisms, as in the underived case.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g`: both sides are identified with the derived pullback along the diagonal
`g' ≫ f = f' ≫ g` by `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` (the inverse on the
left, the forward map on the right).

```
  D(Y) --Lf^*--> D(X)
   |              |
  Lg^*    ≅     Lg'^*
   ↓              ↓
  D(Y') --Lf'^*-> D(X')
```
-/
noncomputable def derivedSquareUpperStarIso (sq : CommSq g' f' f g) :
    L((g)^*[A]) ⋙ L((f')^*[A]) ≅ L((f)^*[A]) ⋙ L((g')^*[A]) :=
  (leftDerivedUpperStarComp A f' g (g' ≫ f) sq.w).symm ≪≫ leftDerivedUpperStarComp A g' f

/-- The derived base change map as a `TwoSquare`, for the mate calculus: the mate of
`(AlgebraicGeometry.Etale.derivedSquareUpperStarIso A sq).hom` with respect to the derived
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
noncomputable abbrev derivedBaseChangeSquare (sq : CommSq g' f' f g) :
    TwoSquare R((f)_*[A]) L((g')^*[A]) L((g)^*[A]) R((f')_*[A]) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom)

/-- **The derived base change map** `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` of a commutative square,
on the unbounded derived categories of étale sheaves, as a natural transformation
`Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`: the mate of the derived square isomorphism
`AlgebraicGeometry.Etale.derivedSquareUpperStarIso` with respect to the derived adjunctions
`Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. This is the exchange map `Ex_*` of `sk-def-sf-exchanges`.

```
  D(X) --Lg'^*--> D(X')
   |               |
  Rf_*   ⇓ Ex_*   Rf'_*
   ↓               ↓
  D(Y) --Lg^*---> D(Y')
```

(blueprint: `def:weil-pbc-derived-exchange-unbounded`) -/
noncomputable def derivedBaseChangeMap (sq : CommSq g' f' f g) :
    R((f)_*[A]) ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ R((f')_*[A]) :=
  (derivedBaseChangeSquare A sq)

omit [HasSmallSiteSheafify A] in
/-- **The adjoint of the derived base change map** is the derived square isomorphism followed
by the counit: for `K` in `D(X_ét)` the following square commutes.

```
  Lf'^* Lg^* Rf_* K --Lf'^*(Ex_* K)--> Lf'^* Rf'_* Lg'^* K
          |                                   |
  derivedSquareUpperStarIso                 ε_{f'}
          ↓                                   ↓
  Lg'^* Lf^* Rf_* K ---Lg'^*(ε_f K)-------> Lg'^* K
```

(blueprint: `def:weil-pbc-derived-exchange-unbounded`) -/
@[reassoc]
lemma derivedUpperStar_map_derivedBaseChangeMap_app_counit (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (L((f')^*[A])).map ((derivedBaseChangeMap A sq).app K) ≫
        (derivedUpperStarLowerStarAdjunction A f').counit.app ((L((g')^*[A])).obj K) =
      (derivedSquareUpperStarIso A sq).hom.app ((R((f)_*[A])).obj K) ≫
        (L((g')^*[A])).map ((derivedUpperStarLowerStarAdjunction A f).counit.app K) :=
  mateEquiv_counit _ _ _ K

omit [HasSmallSiteSheafify A] in
/-- **The unit form of the derived base change map**: for `M` in `D(Y_ét)` the following
square commutes.

```
  Lg^* M -----------η_{f'}-----------> Rf'_* Lf'^* Lg^* M
    |                                         |
  Lg^*(η_f M)             Rf'_*(derivedSquareUpperStarIso M)
    ↓                                         ↓
  Lg^* Rf_* Lf^* M -------Ex_*-------> Rf'_* Lg'^* Lf^* M
```
-/
@[reassoc]
lemma map_unit_derivedBaseChangeMap_app (sq : CommSq g' f' f g)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (L((g)^*[A])).map ((derivedUpperStarLowerStarAdjunction A f).unit.app M) ≫
        (derivedBaseChangeMap A sq).app ((L((f)^*[A])).obj M) =
      (derivedUpperStarLowerStarAdjunction A f').unit.app ((L((g)^*[A])).obj M) ≫
        (R((f')_*[A])).map ((derivedSquareUpperStarIso A sq).hom.app M) :=
  unit_mateEquiv _ _ _ M

end Etale

end AlgebraicGeometry
