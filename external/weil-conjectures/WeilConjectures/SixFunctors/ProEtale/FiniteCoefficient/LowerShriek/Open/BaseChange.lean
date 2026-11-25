/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

/-!
# Base change for the pro-étale extension by zero

Consider a commutative square of schemes

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

with `j` and `j'` open immersions, i.e. `g' ≫ j = j' ≫ g''`. This file constructs the canonical
base change map `j'_! ∘ g'^* ⟶ g''^* ∘ j_!` on sheaves for the small pro-étale sites, and proves
that it is an isomorphism when the square is cartesian (blueprint
`proposition-extension-zero-restriction-closed-subscheme--11`). This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`.

The map is the conjugate, under `j_! ⋙ g''^* ⊣ g''_* ⋙ j^*` and `g'^* ⋙ j'_! ⊣ j'^* ⋙ g'_*`, of
the base change map `ProEtale.baseChangeMap A sq : g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of weakly étale
base change. For a cartesian square that map is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback`): both right adjoints send a
sheaf `M` on `Z'` to `V ↦ M(V ×_Z Z') = M(V ×_U U')`.

All functors involved are exact, so the base change isomorphism passes to the derived categories
degreewise (`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`).

## Main definitions

- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekBaseChangeMap`: the base change map
  `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*`.
- `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`: its derived
  version for a cartesian square.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekBaseChangeMap`: **base change for
  the pro-étale extension by zero**.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme MorphismProperty

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The base change map for the pro-étale extension by zero: for a commutative square
`g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

the canonical natural transformation `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*`, i.e. `j'_! g'^* ⟶ g''^* j_!`,
on sheaves for the small pro-étale sites. It is the conjugate of the base change map
`ProEtale.baseChangeMap A sq : g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` under the adjunctions
`j_! ⋙ g''^* ⊣ g''_* ⋙ j^*` and `g'^* ⋙ j'_! ⊣ j'^* ⋙ g'_*`. It runs against the direction of
the map `g^{-1} j_! K ⟶ j'_! g_U^{-1} K` of the blueprint, which is its inverse for a cartesian
square (`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekBaseChangeMap`). -/
noncomputable def openImmersionLowerShriekBaseChangeMap (sq : CommSq g' j' j g'') :
    (g')^*[A] ⋙ (j')_!open[A] ⟶ (j)_!open[A] ⋙ (g'')^*[A] :=
  (conjugateEquiv ((openImmersionLowerShriekUpperStarAdjunction A j).comp
      (upperStarLowerStarAdjunction A g''))
    ((upperStarLowerStarAdjunction A g').comp
      (openImmersionLowerShriekUpperStarAdjunction A j'))).symm
    (ProEtale.baseChangeMap A sq)

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--11`: Pro-etale
extension-by-zero base change.

**Base change for the pro-étale extension by zero along a cartesian square**: if the square
`g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions is cartesian, the base change map
`j'_! g'^* ⟶ g''^* j_!` on pro-étale sheaves is an isomorphism, natural in the sheaf, being the
conjugate of the isomorphism `ProEtale.baseChangeMap A hsq.toCommSq` of weakly étale base
change. Its inverse is the canonical map `g''^{-1} j_! K ⟶ j'_! g'^{-1} K` of the blueprint; for
complexes see `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`. -/
lemma isIso_openImmersionLowerShriekBaseChangeMap (hsq : IsPullback g' j' j g'') :
    IsIso (openImmersionLowerShriekBaseChangeMap A hsq.toCommSq) :=
  have := ProEtale.isIso_baseChangeMap_of_isPullback A hsq
  conjugateEquiv_symm_iso _ _ _

/-- The base change isomorphism `j'_! g'^* ≅ g''^* j_!` of the pro-étale extension by zero
along a cartesian square. -/
noncomputable def openImmersionLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'') :
    (g')^*[A] ⋙ (j')_!open[A] ≅ (j)_!open[A] ⋙ (g'')^*[A] :=
  have := isIso_openImmersionLowerShriekBaseChangeMap A hsq
  asIso (openImmersionLowerShriekBaseChangeMap A hsq.toCommSq)

/-- **Base change for the pro-étale extension by zero on complexes**: for a cartesian square
with `j`, `j'` open immersions, the isomorphism `D(j'_!) D(g'^*) ≅ D(g''^*) D(j_!)` of functors
`D(U_proét) ⥤ D(Z'_proét)` induced degreewise by
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekBaseChangeIso`, all four functors being
exact (blueprint `proposition-extension-zero-restriction-closed-subscheme--11`). -/
noncomputable def derivedOpenImmersionLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'') :
    D((g')^*[A]) ⋙ D((j')_!open[A]) ≅ D((j)_!open[A]) ⋙ D((g'')^*[A]) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekBaseChangeIso A hsq) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end ProEtale

end AlgebraicGeometry
