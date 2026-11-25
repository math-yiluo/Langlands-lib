/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange

/-!
# Compact-support exchange maps along compatible compactifications

Let `f : X ⟶ Y` and `f' : X' ⟶ Y'` be morphisms of schemes with compactifications
`c = (X ⟶[c.i] c.Z ⟶[c.g] Y)` and `c' = (X' ⟶[c'.i] c'.Z ⟶[c'.g] Y')`, and let `g : Y' ⟶ Y`,
`g' : X' ⟶ X` and `gZ : c'.Z ⟶ c.Z` be morphisms such that
```
X' --c'.i--> c'.Z --c'.g--> Y'
|g'           |gZ            |g
v             v              v
X  --c.i-->  c.Z  --c.g-->  Y
```
commutes, the left square being cartesian. The *compact-support exchange map*
(blueprint `def-exchange-projection`, `prose-05-31`)

`Ex_! : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*`

on the unbounded derived categories of pro-étale sheaves is the derived base change map
`Lg^* R(c.g)_* ⟶ R(c'.g)_* L(gZ)^*` of the right square
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`) applied after `(c.i)_!`, followed by the
inverse of the base change isomorphism `(c'.i)_! g'^* ≅ gZ^* (c.i)_!` of the extension by zero
along the cartesian left square
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`, blueprint
`proposition-extension-zero-restriction-closed-subscheme--11`). For `c' = c ×_Y Y'` and a cartesian
outer square it is the map
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`.

## Main definitions

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso`: the
  base change isomorphism `L(g'')^* j_! ≅ j'_! Lg'^*` of the extension by zero along a cartesian
  square of open immersions, with derived pullbacks.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChange`: the exchange
  map `Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section OpenImmersion

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **Base change for the pro-étale extension by zero, with derived pullbacks**: for a cartesian
square `g' ≫ j = j' ≫ g''` with `j` and `j'` open immersions, the isomorphism
`L(g'')^* j_! ≅ j'_! Lg'^*` of functors `D(U_proét) ⥤ D(Z'_proét)`: the inverse of
`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`, the derived pullbacks
of the exact pullbacks being computed degreewise
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory`). -/
noncomputable def leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso
    (hsq : IsPullback g' j' j g'') :
    D((j)_!open[A]) ⋙ L((g'')^*[A]) ≅ L((g')^*[A]) ⋙ D((j')_!open[A]) :=
  Functor.isoWhiskerLeft D((j)_!open[A]) (leftDerivedUpperStarIsoMapDerivedCategory A g'') ≪≫
    (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g').symm
      D((j')_!open[A])

end OpenImmersion

section Compactification

variable {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} (c : Compactification f)
  (c' : Compactification f') {g : Y' ⟶ Y} {g' : X' ⟶ X} {gZ : c'.Z ⟶ c.Z}

/-- Blueprint `def-exchange-projection`, `prose-05-31`: compact-support exchange map
along compactifications compatible with `g`.

**The pro-étale compact-support exchange map along compatible compactifications**: for
compactifications `c` of `f : X ⟶ Y` and `c'` of `f' : X' ⟶ Y'` and morphisms `g : Y' ⟶ Y`,
`g' : X' ⟶ X`, `gZ : c'.Z ⟶ c.Z` such that the square `g' ≫ c.i = c'.i ≫ gZ` is cartesian and
the square `gZ ≫ c.g = c'.g ≫ g` commutes, the natural transformation
`Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*` of functors `D(X_proét) ⥤ D(Y'_proét)`, the composite
```
Lg^* R(c.g)_* (c.i)_! ⟶ R(c'.g)_* L(gZ)^* (c.i)_! ≅ R(c'.g)_* (c'.i)_! Lg'^*
```
of the derived base change map of the right square
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`) and of `R(c'.g)_*` applied to the base
change isomorphism of the extension by zero
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso`). -/
noncomputable def rightDerivedLowerShriekOfCompactificationBaseChange
    (hi : IsPullback g' c'.i c.i gZ) (hg : CommSq gZ c'.g c.g g) :
    Rf_!(c)[A] ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ Rf_!(c')[A] :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open[A]) (derivedBaseChangeMap A hg) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso A hi).hom
      R((c'.g)_*[A]) ≫
    (Functor.associator _ _ _).hom

/-- The components of
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChange`:
the derived base change map at `(c.i)_! K`, followed by `R(c'.g)_*` of the base change
isomorphism of the extension by zero. -/
lemma rightDerivedLowerShriekOfCompactificationBaseChange_app
    (hi : IsPullback g' c'.i c.i gZ) (hg : CommSq gZ c'.g c.g g)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (rightDerivedLowerShriekOfCompactificationBaseChange A c c' hi hg).app K =
      (derivedBaseChangeMap A hg).app (D((c.i)_!open[A]).obj K) ≫
        R((c'.g)_*[A]).map
          ((leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso A hi).hom.app K) := by
  simp [rightDerivedLowerShriekOfCompactificationBaseChange]

end Compactification

end AlgebraicGeometry.ProEtale
