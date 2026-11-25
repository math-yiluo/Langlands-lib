/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange

/-!
# Base change of the extension by zero along an open immersion

For a commutative square of `k`-schemes whose horizontal maps `j`, `j'` are open immersions, the
base-change morphism `j_! ⋙ Lg^* ⟶ Lg'^* ⋙ j'_!` of the extension by zero on bounded constructible
complexes (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange`), and
the isomorphism it gives for a cartesian square
(`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`). The
compact-support base change built from it is in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### For a compactification -/

section Compactification

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

include ℓ k

section OpenImmersion

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  (j : X ⟶ Z) (g : Z' ⟶ Z) (j' : X' ⟶ Z') (g' : X' ⟶ X)
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]



/-- The *unit insertion* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`Lg'^* ⋙ j'_! ⟶ (j_! ⋙ Lj^*) ⋙ (Lg'^* ⋙ j'_!)` obtained by inserting the unit of the adjunction
`j_! ⊣ Lj^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep :
    boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' ⟶
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit
    (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')

variable {j g j' g'} in
/-- The *square transport* step of the extension-by-zero exchange morphism on bounded
constructible complexes: `Functor.squareTransport` applied to the pullback comparison
`Lj^* ∘ Lg'^* ≅ Lg^* ∘ Lj'^*` of the square, under `j_!` on the left and `j'_!` on the
right. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep
    (sq : CommSq g' j' j g) :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') ≅
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ j' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') :=
  Functor.squareTransport (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq.flip)

/-- The *counit contraction* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`(j_! ⋙ Lg^*) ⋙ (Lj'^* ⋙ j'_!) ⟶ j_! ⋙ Lg^*` obtained by contracting the counit of the
adjunction `j'_! ⊣ Lj'^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ j' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g :=
  Functor.whiskerLeft
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').counit ≫
    (Functor.rightUnitor _).hom

variable {j g j' g'}

/-- The canonical exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` on bounded constructible
complexes for a commutative square
```
X' --g'--> X
|          |
j'         j
v          v
Z' --g---> Z
```
of schemes with `j` and `j'` open immersions, assembled as the composite of the unit insertion,
the square transport, and the counit contraction. -/
@[no_expose]
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChange (sq : CommSq g' j' j g) :
    boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g :=
  boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep Λ ℓ j j' g' ≫
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep Λ ℓ sq).hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep Λ ℓ j g j'

/-- The exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is the exchange morphism
`CategoryTheory.Adjunction.exchangeLeft` of the pullback comparison of the square under the
adjunctions `j_! ⊣ Lj^*` and `j'_! ⊣ Lj'^*`. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft
    (sq : CommSq g' j' j g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq.flip) := by
  unfold boundedConstructibleOpenImmersionLowerShriekBaseChange
    boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep
    boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep
    boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep Adjunction.exchangeLeft
  rfl


/-- **Base change for extension by zero** (blueprint `sk-def-sfb-open-base-change`) on bounded
constructible complexes: for a *cartesian* square with `j` and `j'` open immersions, the exchange
morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is an isomorphism.

Mathematically, since the square is cartesian, `X'` is the preimage of the open subscheme
`X ⊆ Z` under `g`, and on stalks at points of `Z'_proét` both sides are the pulled-back stalk at
points of `X'` and vanish outside `X'`. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange (sq : IsPullback g' j' j g) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq) := by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft] at this
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft]
  exact this

/-- The extension-by-zero exchange isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!` on bounded
constructible complexes for a cartesian square of open immersions: the inverse of the canonical
exchange morphism, which is an isomorphism by base change for extension by zero. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
    (sq : IsPullback g' j' j g) :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g ≅
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq
  (asIso (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq)).symm

end OpenImmersion

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing
