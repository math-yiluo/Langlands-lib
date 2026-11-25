/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# Exchanging an extension by zero with a derived pushforward

For a cartesian square of schemes

```
  U' --j'--> Z'
  |          |
  g'         g''
  ↓          ↓
  U  --j---> Z
```

with `j` and `j'` open immersions, there is a natural exchange map
`Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` on unbounded derived categories of étale sheaves. It is the
mate, along the adjunctions `D(g'^*) ⊣ Rg'_*` and `D(g''^*) ⊣ Rg''_*`, of the inverse of the
derived base change isomorphism `D(g'^*) ⋙ Dj'_! ≅ Dj_! ⋙ D(g''^*)` for the extension by zero.
Since the pullbacks are exact, this needs no monoidal structure on the coefficients.

When `g''` is proper and the coefficients are torsion, this map is an isomorphism; this is the
key step in the proof of the composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`).

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarExchange`: the exchange map
  `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring`:
  with torsion coefficients `Λ` and `g''` proper, the exchange map is an isomorphism.

## TODO

- Redefine `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison` as
  this exchange map for the square `(𝟙 X, c.i, d.i, r.hom)`, whiskered by `R(d.g)_*` and
  composed with `R(𝟙 X)_* ≅ 𝟭` and `R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`. This first needs
  `AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedIso` to be restated as a special
  case of `AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.

## Blueprint

This file constructs the map of `thm:open-proper-interchange` on unbounded derived categories.
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

/-- **The exchange map of an extension by zero and a derived pushforward**: for a cartesian
square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the natural
transformation `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`. It is the mate, along the adjunctions
`D(g'^*) ⊣ Rg'_*` and `D(g''^*) ⊣ Rg''_*`, of the inverse of the base change isomorphism
`AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.

```
  D(U') --Dj'_!--> D(Z')
   |                 |
  Rg'_*     ⇗      Rg''_*
   ↓                 ↓
  D(U) ---Dj_!---> D(Z)
```

The 2-cell goes from the path `Rg'_*` then `Dj_!` (left, then bottom) to the path `Dj'_!` then
`Rg''_*` (top, then right). (blueprint: the map of `thm:open-proper-interchange`, on unbounded
derived categories) -/
noncomputable def openImmersionLowerShriekLowerStarExchange (hsq : IsPullback g' j' j g'') :
    R((g')_*[A]) ⋙ D((j)_!open[A]) ⟶ D((j')_!open[A]) ⋙ R((g'')_*[A]) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction A g')
    (mapDerivedUpperStarLowerStarAdjunction A g'')
    (TwoSquare.mk _ _ _ _
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).inv))

/-- The exchange map `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` at `K`, written out: the unit of
`D(g''^*) ⊣ Rg''_*`, then the inverse of the base change isomorphism `bc`, then the counit of
`D(g'^*) ⊣ Rg'_*`.

```
  Dj_! Rg'_* K --η--> Rg''_* Dg''^* Dj_! Rg'_* K --Rg''_*(bc⁻¹)--> Rg''_* Dj'_! Dg'^* Rg'_* K
                                                                          |
                                                                   Rg''_* Dj'_!(ε)
                                                                          ↓
                                                                   Rg''_* Dj'_! K
```
-/
@[reassoc]
lemma openImmersionLowerShriekLowerStarExchange_app (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U'.smallEtaleTopology A)) :
    (openImmersionLowerShriekLowerStarExchange A hsq).app K =
      (mapDerivedUpperStarLowerStarAdjunction A g'').unit.app
          (D((j)_!open[A]).obj (R((g')_*[A]).obj K)) ≫
        R((g'')_*[A]).map
          ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).inv.app
              (R((g')_*[A]).obj K) ≫
            D((j')_!open[A]).map ((mapDerivedUpperStarLowerStarAdjunction A g').counit.app K)) := by
  simp [openImmersionLowerShriekLowerStarExchange]

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Extension by zero commutes with proper pushforward**: if the coefficient ring `Λ` is
torsion as an additive group, then for a cartesian square `g' ≫ j = j' ≫ g''` of schemes with
`j` and `j'` open immersions and `g''` proper, the exchange map
`Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` on the unbounded derived categories `D(-_ét, Λ)` is an
isomorphism.

The statement fails for general coefficients, which is why `Λ` is torsion here.

Proof: with `i` the closed complement of `j`, it suffices to check the claim after `D(j^*)` and
after `D(i^*)` (open–closed conservativity).
- After `D(j^*)` it is formal: the mate of the exchange map under `j_! ⊣ j^*` and `j'_! ⊣ j'^*`
  is the conjugate of the base change isomorphism, and the units of `j_! ⊣ j^*` and
  `j'_! ⊣ j'^*` are isomorphisms (`CategoryTheory.isIso_map_mateEquiv_app_of_isIso`).
- After `D(i^*)` both sides vanish: the source because `i^* j_! = 0`, and the target by proper
  base change for `g''` along `i`, which is
  `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`, since
  the pullback of `j'_!` to the closed complement of `j'` vanishes.

(blueprint: unbounded analogue of `thm:open-proper-interchange`) -/
theorem isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring
    (hΛ : IsAddTorsion Λ) [IsProper g''] (hsq : IsPullback g' j' j g'') :
    IsIso (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq) := by
  have hdisj : Disjoint (Set.range j.closedComplement.base) (Set.range j.base) := by
    rw [j.range_closedComplement]
    exact disjoint_compl_left
  let sq := IsPullback.of_hasPullback g'' j.closedComplement
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ hΛ sq
  have hdisj' : Disjoint (Set.range (pullback.fst g'' j.closedComplement).base)
      (Set.range j'.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨u, hu⟩
    refine Set.disjoint_left.1 hdisj
      ⟨(pullback.snd g'' j.closedComplement).base p, rfl⟩ ⟨g'.base u, ?_⟩
    rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply, hu, ← Scheme.Hom.comp_apply,
      pullback.condition, Scheme.Hom.comp_apply]
  have (K : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq).app K) := by
    apply isIso_of_isIso_mapDerivedCategoryUpperStar_map _ j j.closedComplement
      j.range_closedComplement
    · exact isIso_map_mateEquiv_app_of_isIso (mapDerivedUpperStarLowerStarAdjunction _ g')
        (mapDerivedUpperStarLowerStarAdjunction _ g'')
        (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j')
        (TwoSquare.mk _ _ _ _ (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso _ hsq).inv) K
    · refine isIso_of_source_target_iso_zero _
        (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ j
          j.closedComplement hdisj _).isoZero (IsZero.isoZero ?_)
      have hN : IsZero (L((pullback.fst g'' j.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj
          (D((j')_!open[ModuleCat.{u + 1} Λ]).obj K)) :=
        (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ j'
          _ hdisj' K).of_iso ((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _)
      exact IsZero.of_iso
        ((R((pullback.snd g'' j.closedComplement)_*[ModuleCat.{u + 1} Λ])).map_isZero hN)
        ((leftDerivedUpperStarIsoMapDerivedCategory _ _).symm.app _ ≪≫
          asIso ((derivedBaseChangeMap _ sq.toCommSq).app _))
  exact NatIso.isIso_of_isIso_app _

end Etale

end AlgebraicGeometry
