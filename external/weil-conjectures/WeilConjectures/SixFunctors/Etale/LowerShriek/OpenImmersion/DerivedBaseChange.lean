/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-!
# Extension by zero commutes with arbitrary base change, for complexes

Consider a cartesian square of schemes

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

with `j` (hence `j'`) an open immersion. The extension by zero `j_!` is exact
(`AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek`), and the base change
map `j'_! g'^* ⟶ g''^* j_!` is an isomorphism of functors on étale sheaves
(`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`). Since all four functors
are exact, they act termwise on complexes, and the base change isomorphism induces an
isomorphism of the induced functors on the derived categories.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekDerivedBaseChangeIso`: the isomorphism
  `j'_! g'^* ≅ g''^* j_!` of functors `D(U_ét) ⥤ D(Z'_ét)`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap_mapHomologicalComplex`:
  the base change map is an isomorphism of functors on complexes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--11`, for complexes: for a
cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, the base change map
`j'_! g'^* ⟶ g''^* j_!` is an isomorphism of functors on cochain complexes of étale sheaves,
the four functors acting termwise. -/
lemma Etale.isIso_openImmersionLowerShriekBaseChangeMap_mapHomologicalComplex
    (hsq : IsPullback g' j' j g'') {ι : Type*} (c : ComplexShape ι) :
    IsIso (NatTrans.mapHomologicalComplex
      (Etale.openImmersionLowerShriekBaseChangeMap A hsq.toCommSq) c) :=
  have := Etale.isIso_openImmersionLowerShriekBaseChangeMap A hsq
  (NatIso.mapHomologicalComplex
    (asIso (Etale.openImmersionLowerShriekBaseChangeMap A hsq.toCommSq)) c).isIso_hom

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--11`: for an open immersion
`j : U ⟶ Z` and a cartesian square

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

the extension by zero is exact
(`AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek` and
`PreservesFiniteColimits`),`j'_! g'^* F ≅ g''^* j_! F` for every sheaf `F` on `U_ét`
(`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`), and the same holds for
complexes: this is the induced isomorphism `j'_! g'^* ≅ g''^* j_!` of functors on the derived
categories `D(U_ét) ⥤ D(Z'_ét)`, all four functors being exact. -/
noncomputable def Etale.openImmersionLowerShriekDerivedBaseChangeIso
    (hsq : IsPullback g' j' j g'') :
    ((g')^*[A]).mapDerivedCategory ⋙ ((j')_!open[A]).mapDerivedCategory ≅
      ((j)_!open[A]).mapDerivedCategory ⋙ ((g'')^*[A]).mapDerivedCategory :=
  have := Etale.isIso_openImmersionLowerShriekBaseChangeMap A hsq
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (Etale.openImmersionLowerShriekBaseChangeMap A hsq.toCommSq)) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry
