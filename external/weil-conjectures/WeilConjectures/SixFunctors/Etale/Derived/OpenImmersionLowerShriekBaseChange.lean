/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# Derived base change for the extension by zero

For a cartesian square of schemes

```
  U' --j'--> Z'
  |          |
  g'         g''
  ↓          ↓
  U  --j---> Z
```

with `j` and `j'` open immersions, the base change map
`AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap : g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*` is
an isomorphism. All four functors are exact, so it induces an isomorphism on unbounded derived
categories, first between the induced functors `D(-)` and then, since the pullbacks are exact,
between `Lg'^* ⋙ Dj'_!` and `Dj_! ⋙ Lg''^*`.

## Main definitions

- `AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`: the
  isomorphism `Dg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Dg''^*`.
- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso`: the isomorphism
  `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*`.

## TODO

`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedIso` is the same construction
for the square of a refinement of compactifications, built from
`Compactification.Refinement.openImmersionLowerShriekBaseChange` rather than from
`openImmersionLowerShriekBaseChangeMap`. It should be restated as a special case of
`mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **Derived base change for the extension by zero**: for a cartesian square
`g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the isomorphism
`Dg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Dg''^*` of the functors induced on unbounded derived categories by
the base change isomorphism `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`.

```
  D(U) --Dg'^*--> D(U')
   |               |
  Dj_!     ≅     Dj'_!
   ↓               ↓
  D(Z) --Dg''^*-> D(Z')
```
-/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
    (hsq : IsPullback g' j' j g'') :
    D((g')^*[A]) ⋙ D((j')_!open[A]) ≅ D((j)_!open[A]) ⋙ D((g'')^*[A]) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A hsq)) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **Derived base change for the extension by zero**, with derived pullbacks: for a cartesian
square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the isomorphism
`Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` on unbounded derived categories. It is
`AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso` conjugated
by the identifications `Lg'^* ≅ Dg'^*` and `Lg''^* ≅ Dg''^*` of the derived functors of the
exact pullbacks.

```
  D(U) --Lg'^*--> D(U')
   |               |
  Dj_!     ≅     Dj'_!
   ↓               ↓
  D(Z) --Lg''^*-> D(Z')
```
-/
noncomputable def derivedOpenImmersionLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'') :
    L((g')^*[A]) ⋙ D((j')_!open[A]) ≅ D((j)_!open[A]) ⋙ L((g'')^*[A]) :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g') _ ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A g'').symm

end Etale

end AlgebraicGeometry
