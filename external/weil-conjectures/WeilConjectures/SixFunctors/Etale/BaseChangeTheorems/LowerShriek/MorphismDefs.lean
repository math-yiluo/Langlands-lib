/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.CategoryTheory.DerivedCategory.ExchangeLeftPlus

/-!

# The base-change morphism for the lower shriek

Fix a Cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y`
of `f`. This file constructs the compact-support base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` (in diagrammatic `⋙`-order)

on the bounded below derived categories of étale sheaves, where `c' = c.ofIsPullback sq`
is the base-changed compactification of `f'` and `Rf_!^c := Di_! ⋙ R⁺p_*` is the derived
lower shriek `Rf_!(c)[A]+` of `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
associated with `c` — the bounded below derived incarnation of the lower shriek
`Compactification.lowerShriek` (`f_!^c = i_! ⋙ p_*`), in which the exact extension by
zero `i_!` needs no resolutions and only the pushforward is derived.

`Ex_!^c` is assembled from two exchange morphisms:

- the *direct-image exchange* `Ex_* : Rp_* ⋙ Lg^* ⟶ Lḡ^* ⋙ Rp'_*` for the proper
  square of the base-changed compactification, which is the base-change morphism
  `Etale.baseChange` of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`
  (no properness enters its construction);
- the *extension-by-zero exchange* for the open-immersion square of the base-changed
  compactification. Its canonical mate goes in the direction
  `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*` (`Etale.derivedPlusOpenImmersionLowerShriekBaseChange`); base
  change for extension by zero asserts that this mate is an isomorphism
  (`Etale.isIso_derivedPlusOpenImmersionLowerShriekBaseChange`, deduced from the underived base
  change isomorphism `Etale.openImmersionLowerShriekBaseChangeMap`), and the
  construction of `Ex_!^c` uses its inverse.

The independence of `Ex_!^c` from the chosen compactification is *not* treated here; all
statements are relative to an explicit compactification `c`.

## Main definitions

- `AlgebraicGeometry.Etale.derivedPlusOpenImmersionLowerShriekBaseChangeUnitStep`,
  `Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep`,
  `Etale.derivedPlusOpenImmersionLowerShriekBaseChangeCounitStep`: the three steps of the
  extension-by-zero exchange morphism, mirroring the three steps of `Etale.baseChange`.
- `AlgebraicGeometry.Etale.derivedPlusOpenImmersionLowerShriekBaseChange`: the canonical exchange
  morphism `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*` for a commutative square of open immersions.
- `AlgebraicGeometry.Etale.isIso_derivedPlusOpenImmersionLowerShriekBaseChange`: base change for
  extension by zero, for a Cartesian square;
  `Etale.derivedPlusOpenImmersionLowerShriekBaseChangeIso`
  is the inverse isomorphism `i_! ⋙ Lḡ^* ≅ Lg'^* ⋙ i'_!`.
- `AlgebraicGeometry.Etale.lowerShriekBaseChange`: the compact-support base-change
  morphism `Ex_!^c`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Abelian

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open Scheme Etale

/-! ### The square isomorphism through an arbitrary diagonal -/

section SquareUpperStar

/-- The composition isomorphism `Etale.upperStarComp` with a prescribed diagonal
`h₁₂ = h₁ ≫ h₂` is the one with the canonical diagonal `h₁ ≫ h₂`, preceded by the transport
along `h₁₂ = h₁ ≫ h₂`. -/
lemma Etale.upperStarComp_eq_eqToIso_trans {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    Etale.upperStarComp A h₁ h₂ h₁₂ hh =
      eqToIso (by rw [hh]) ≪≫ Etale.upperStarComp A h₁ h₂ := by
  subst hh
  simp

/-- The square isomorphism `Etale.squareUpperStarIso` of a commutative square
`g' ≫ f = f' ≫ g` is the composite of the composition isomorphisms with their canonical
diagonals `f' ≫ g` and `g' ≫ f`, through the transport along `f' ≫ g = g' ≫ f`. -/
lemma Etale.squareUpperStarIso_eq {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    Etale.squareUpperStarIso A sq =
      (Etale.upperStarComp A f' g).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫
        Etale.upperStarComp A g' f := by
  rw [Etale.squareUpperStarIso, Etale.upperStarComp_eq_eqToIso_trans A f' g (g' ≫ f) sq.w,
    Iso.trans_symm, Iso.trans_assoc]
  rfl

end SquareUpperStar

/-! ### The extension-by-zero exchange morphism on bounded below derived categories -/

section OpenImmersion

variable {X Z X' Z' : Scheme.{u}}
  {j : X ⟶ Z} {g : Z' ⟶ Z} {j' : X' ⟶ Z'} {g' : X' ⟶ X}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The *square transport* step of the extension-by-zero exchange morphism on the
bounded below derived categories: the natural isomorphism obtained by transporting along
the pullback comparison `θ_sq : Lj^* ∘ Lg'^* ≅ Lg^* ∘ Lj'^*` of the square
(`Etale.pullbackSquareComparison` applied to `sq.flip`) under `j_!` on the left and
`j'_!` on the right; the reassociations are the only other ingredient. -/
noncomputable def Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep
    (sq : CommSq g' j' j g) :
    (D+((j)_!open[A]) ⋙ D+((j)^*[A])) ⋙ (D+((g')^*[A]) ⋙ D+((j')_!open[A])) ≅
      (D+((j)_!open[A]) ⋙ D+((g)^*[A])) ⋙ (D+((j')^*[A]) ⋙ D+((j')_!open[A])) :=
  Functor.squareTransport D+((j)_!open[A]) D+((j')_!open[A])
    (Etale.pullbackSquareComparison A sq.flip)

lemma Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep_app (sq : CommSq g' j' j g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep A sq).app K =
      D+((j')_!open[A]).mapIso
        ((pullbackSquareComparison A sq.flip).app (D+((j)_!open[A]).obj K)) := by
  simp [derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep]

lemma Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep_hom_app (sq : CommSq g' j' j g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep A sq).hom.app K =
      D+((j')_!open[A]).map
        ((pullbackSquareComparison A sq.flip).hom.app (D+((j)_!open[A]).obj K)) :=
  congrArg Iso.hom (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep_app A sq K)

lemma Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep_inv_app (sq : CommSq g' j' j g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep A sq).inv.app K =
      D+((j')_!open[A]).map
        ((pullbackSquareComparison A sq.flip).inv.app (D+((j)_!open[A]).obj K)) :=
  congr(Iso.inv $(Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep_app A sq K))

/-- For a Cartesian square of open immersions, the exchange morphism of the square isomorphism
for the adjunctions `j_! ⊣ j^*` and `j'_! ⊣ j'^*` is an isomorphism: it is the base change map
`Etale.openImmersionLowerShriekBaseChangeMap`. -/
lemma Etale.isIso_exchangeLeft_squareUpperStarIso (sq : IsPullback g' j' j g) :
    IsIso (Adjunction.exchangeLeft (openImmersionLowerShriekUpperStarAdjunction A j)
      (openImmersionLowerShriekUpperStarAdjunction A j')
      (squareUpperStarIso A sq.toCommSq.flip)) := by
  rw [Adjunction.exchangeLeft_eq_of_unit_app_comp _ _ _ _
    (unit_map_openImmersionLowerShriekBaseChangeMap_app A sq.toCommSq)]
  exact isIso_openImmersionLowerShriekBaseChangeMap A sq

/- The K-flat resolution package on the coefficient category `A`, as in the sections
`DerivedUpperStar` and `DerivedUpperLowerStarAdjunction` of
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`; it enters here through the
bounded below derived adjunction `Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus`
of `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (j g j' g')

/-- The *unit insertion* step of the extension-by-zero exchange morphism on the bounded
below derived categories: the natural transformation
`Lg'^* ⋙ j'_! ⟶ (j_! ⋙ Lj^*) ⋙ (Lg'^* ⋙ j'_!)` obtained by inserting the unit of the
derived adjunction `j_! ⊣ Lj^*`. -/
noncomputable def Etale.derivedPlusOpenImmersionLowerShriekBaseChangeUnitStep :
    D+((g')^*[A]) ⋙ D+((j')_!open[A]) ⟶
      (D+((j)_!open[A]) ⋙ D+((j)^*[A])) ⋙ (D+((g')^*[A]) ⋙ D+((j')_!open[A])) :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight
  (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j).unit
  (D+((g')^*[A]) ⋙ D+((j')_!open[A]))

lemma Etale.derivedPlusOpenImmersionLowerShriekBaseChangeUnitStep_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeUnitStep A j j' g').app K =
      D+((j')_!open[A]).map (D+((g')^*[A]).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j).unit.app K)) := by
  simp [derivedPlusOpenImmersionLowerShriekBaseChangeUnitStep]

/-- The *counit contraction* step of the extension-by-zero exchange morphism on the
bounded below derived categories: the natural transformation
`(j_! ⋙ Lg^*) ⋙ (Lj'^* ⋙ j'_!) ⟶ j_! ⋙ Lg^*` obtained by contracting the counit of the
derived adjunction `j'_! ⊣ Lj'^*`. -/
noncomputable def Etale.derivedPlusOpenImmersionLowerShriekBaseChangeCounitStep :
    (D+((j)_!open[A]) ⋙ D+((g)^*[A])) ⋙ (D+((j')^*[A]) ⋙ D+((j')_!open[A])) ⟶
      D+((j)_!open[A]) ⋙ D+((g)^*[A]) :=
  Functor.whiskerLeft (D+((j)_!open[A]) ⋙ D+((g)^*[A]))
  (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j').counit
    ≫ (Functor.rightUnitor _).hom

lemma Etale.derivedPlusOpenImmersionLowerShriekBaseChangeCounitStep_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeCounitStep A j g j').app K =
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j').counit.app
        ((D+((j)_!open[A]) ⋙ D+((g)^*[A])).obj K) := by
  simp [derivedPlusOpenImmersionLowerShriekBaseChangeCounitStep]

variable {j g j' g'}

/-- The canonical exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` on the bounded below
derived categories for a commutative square
```
X' --g'--> X
|          |
j'         j
v          v
Z' --g---> Z
```
of schemes with `j` and `j'` open immersions, assembled as the composite of the unit
insertion, the square transport, and the counit contraction. -/
@[no_expose]
noncomputable def Etale.derivedPlusOpenImmersionLowerShriekBaseChange (sq : CommSq g' j' j g) :
    D+((g')^*[A]) ⋙ D+((j')_!open[A]) ⟶ D+((j)_!open[A]) ⋙ D+((g)^*[A]) :=
  (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeUnitStep A j j' g') ≫
    (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep A sq).hom ≫
      (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeCounitStep A j g j')

lemma Etale.derivedPlusOpenImmersionLowerShriekBaseChange_app (sq : CommSq g' j' j g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedPlusOpenImmersionLowerShriekBaseChange A sq).app K =
      (derivedPlusOpenImmersionLowerShriekBaseChangeUnitStep A j j' g').app K ≫
        (derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep A sq).hom.app K ≫
          (derivedPlusOpenImmersionLowerShriekBaseChangeCounitStep A j g j').app K := by
  simp [Etale.derivedPlusOpenImmersionLowerShriekBaseChange]

/-- The extension-by-zero exchange morphism `Etale.derivedPlusOpenImmersionLowerShriekBaseChange`
is the exchange morphism `Adjunction.exchangeLeft` of the pullback comparison of the square for
the bounded below derived adjunctions `j_! ⊣ j^*` and `j'_! ⊣ j'^*`. -/
lemma Etale.derivedPlusOpenImmersionLowerShriekBaseChange_eq_exchangeLeft (sq : CommSq g' j' j g) :
    Etale.derivedPlusOpenImmersionLowerShriekBaseChange A sq =
      Adjunction.exchangeLeft (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j)
        (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j')
        (pullbackSquareComparison A sq.flip) := by
  refine NatTrans.ext (funext fun K => ?_)
  rw [derivedPlusOpenImmersionLowerShriekBaseChange_app, Adjunction.exchangeLeft_app,
    derivedPlusOpenImmersionLowerShriekBaseChangeUnitStep_app,
    derivedPlusOpenImmersionLowerShriekBaseChangeSquareStep_hom_app,
    derivedPlusOpenImmersionLowerShriekBaseChangeCounitStep_app]
  rfl

/-- **Base change for extension by zero**: for a *Cartesian* square with `j` and `j'`
open immersions, the exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is an isomorphism.

Mathematically, since the square is Cartesian, `X'` is the preimage of the open
subscheme `X ⊆ Z` under `g`, and on geometric stalks both sides are the pulled-back
stalk at points of `X'` and vanish outside `X'`. -/
theorem Etale.isIso_derivedPlusOpenImmersionLowerShriekBaseChange (sq : IsPullback g' j' j g) :
    IsIso (Etale.derivedPlusOpenImmersionLowerShriekBaseChange A sq.toCommSq) := by
  have := Etale.isIso_exchangeLeft_squareUpperStarIso A sq
  rw [Etale.squareUpperStarIso_eq] at this
  rw [Etale.derivedPlusOpenImmersionLowerShriekBaseChange_eq_exchangeLeft]
  exact Adjunction.isIso_exchangeLeft_mapDerivedCategoryPlusAdjunction_of_eqToIso _ _
    (Etale.upperStarComp A g' j (g' ≫ j) rfl) (Etale.upperStarComp A j' g (j' ≫ g) rfl) _ _

/-- The extension-by-zero exchange isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!` of a Cartesian
square of open immersions: the inverse of the canonical exchange morphism
`Etale.derivedPlusOpenImmersionLowerShriekBaseChange`, which is an isomorphism by base change for
extension by zero. -/
noncomputable def Etale.derivedPlusOpenImmersionLowerShriekBaseChangeIso
    (sq : IsPullback g' j' j g) :
    D+((j)_!open[A]) ⋙ D+((g)^*[A]) ≅ D+((g')^*[A]) ⋙ D+((j')_!open[A]) :=
  have := Etale.isIso_derivedPlusOpenImmersionLowerShriekBaseChange A sq
  (asIso (Etale.derivedPlusOpenImmersionLowerShriekBaseChange A sq.toCommSq)).symm

end OpenImmersion

/-! ### The compact-support base-change morphism -/

section LowerShriek

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *compact-support base-change morphism*
`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` of a Cartesian square `sq` and a
compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`, where `c' = c.ofIsPullback sq`: with
`Rf_!^c = Di_! ⋙ R⁺p_*`, it is the pasting of the direct-image exchange `Etale.baseChange`
of the proper square of the base-changed compactification with the inverse of the
extension-by-zero exchange of its open-immersion square,

`Di_! ⋙ R⁺p_* ⋙ Lg^* ⟶ Di_! ⋙ Lḡ^* ⋙ R⁺p'_* ⟶ Lg'^* ⋙ Di'_! ⋙ R⁺p'_*`.

The base change theorem for the lower shriek asserts that this morphism is an
isomorphism on complexes with torsion cohomology; no such hypothesis is built into the
definition. -/
@[no_expose]
noncomputable def Etale.lowerShriekBaseChange (c : Compactification f)
    (sq : IsPullback g' f' f g) :
    Rf_!(c)[A]+ ⋙ D+((g)^*[A]) ⟶ D+((g')^*[A]) ⋙ Rf_!(c.ofIsPullback sq)[A]+ :=
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft D+((c.i)_!open[A])
    (Etale.baseChange A (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight
    (Etale.derivedPlusOpenImmersionLowerShriekBaseChangeIso A
      (c.isPullback_i_ofIsPullback sq)).hom
    R+(((c.ofIsPullback sq).g)_*[A]) ≫
  (Functor.associator _ _ _).hom

lemma Etale.lowerShriekBaseChange_app (c : Compactification f) (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.lowerShriekBaseChange A c sq).app K =
      (Etale.baseChange A (c.isPullback_g_ofIsPullback sq).flip.toCommSq).app
          (D+((c.i)_!open[A]).obj K) ≫
        R+(((c.ofIsPullback sq).g)_*[A]).map
          ((Etale.derivedPlusOpenImmersionLowerShriekBaseChangeIso A
            (c.isPullback_i_ofIsPullback sq)).hom.app K) := by
  simp [Etale.lowerShriekBaseChange]

end LowerShriek

end AlgebraicGeometry
