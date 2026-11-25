/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ExchangeLeftAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!

# Weakly étale base change on the ambient derived categories of module objects

For a cartesian square of schemes

```
X' --g'--> X
|          |
p'         p
v          v
Y' --g---> Y
```

with `g` and `g'` weakly étale, the base change map `Lg^* Rp_* ⟶ Rp'_* Lg'^*` on the ambient
derived categories of module objects over a commutative condensed ring `Λ`
(`ProEtale.CondensedRing.baseChangeMap`) is an isomorphism, for an arbitrary morphism `p` and on
all complexes (`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`). This is the
localization case of base change: for weakly étale `g` the site `Y'_proét` is the localization of
`Y_proét` at `Y'`, and the pullback `g^*` is restriction.

The proof derives the weakly étale base change on module objects
(`ProEtale.CondensedRing.isIso_lowerStarBaseChange_of_isPullback`) along the abstract statement
`Adjunction.isIso_exchangeRight_derivedAdjunction_leftDerivedFunctorSquareIso_of_leftAdjoint`: the
pullbacks `g^*` and `g'^*` have exact left adjoints, the extensions by zero
(`ProEtale.CondensedRing.weaklyEtaleLowerShriekUpperStarAdjunction`), so the exchange morphism of
the derived adjunctions is conjugate to an exchange morphism of exact functors, which is computed
levelwise.

## Main statements

- `ProEtale.CondensedRing.pullbackSquareComparison_eq_leftDerivedFunctorSquareIso`: the pullback
  comparison of a commutative square on the ambient derived categories is induced by the
  comparison `upperStarSquareComparison` of the pullbacks of module objects.
- `ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`: weakly étale base change on the
  ambient derived categories.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 6.2.3 (localization).
- Stacks Project, Tag 0F4X / Section 21.20, *Cohomology on the localized site*.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

-- the instances of the general lemmas are found for each of the categories of module objects
/-- The pullback comparison `Lg^* ⋙ Lp'^* ≅ Lp^* ⋙ Lg'^*` of a commutative square on the ambient
derived categories is the isomorphism of total left derived functors induced by the comparison
`upperStarSquareComparison` of the pullbacks of module objects. -/
lemma pullbackSquareComparison_eq_leftDerivedFunctorSquareIso (sq : CommSq g' p' p g) :
    pullbackSquareComparison Λ sq =
      Adjunction.leftDerivedFunctorSquareIso (upperStarSquareComparison Λ sq) := by
  ext K
  rw [Adjunction.leftDerivedFunctorSquareIso_hom_app_of_eq (upperStarSquareComparison Λ sq)
    (upperStarComp Λ p' g) (upperStarComp Λ g' p) (by rw [sq.w]) rfl K]
  simp only [pullbackSquareComparison, leftDerivedUpperStarComp, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc]

-- the instances of the general lemma are found for each of the categories of module objects
/-- **Weakly étale base change on the ambient derived categories**: for a cartesian square
`g' ≫ p = p' ≫ g` of schemes with `g` and `g'` weakly étale, the base change map
`Lg^* Rp_* ⟶ Rp'_* Lg'^*` of module objects over `Λ` is an isomorphism, for every morphism `p`
and on all complexes. -/
theorem isIso_baseChangeMap_of_weaklyEtale (sq : IsPullback g' p' p g) [WeaklyEtale g]
    [WeaklyEtale g'] : IsIso (baseChangeMap Λ sq.toCommSq) := by
  have : IsIso (Adjunction.exchangeRight (upperStarLowerStarAdjunction Λ p)
      (upperStarLowerStarAdjunction Λ p') (upperStarSquareComparison Λ sq.toCommSq)) :=
    isIso_lowerStarBaseChange_of_isPullback Λ sq
  rw [baseChangeMap, pullbackSquareComparison_eq_leftDerivedFunctorSquareIso]
  exact Adjunction.isIso_exchangeRight_derivedAdjunction_leftDerivedFunctorSquareIso_of_leftAdjoint
    (upperStarLowerStarAdjunction Λ p) (upperStarLowerStarAdjunction Λ p')
    (weaklyEtaleLowerShriekUpperStarAdjunction Λ g)
    (weaklyEtaleLowerShriekUpperStarAdjunction Λ g') (upperStarSquareComparison Λ sq.toCommSq)

end AlgebraicGeometry.ProEtale.CondensedRing
