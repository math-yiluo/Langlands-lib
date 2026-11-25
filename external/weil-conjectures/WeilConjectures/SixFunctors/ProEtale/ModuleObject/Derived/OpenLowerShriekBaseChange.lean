/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement
public import Mathlib.Tactic.IrreducibleDef

/-!

# Extension by zero and base change on bounded constructible module objects

Let `Λ` be a commutative condensed ring. All schemes are separated and of finite type over a
field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all morphisms are morphisms of
`Over (Spec (.of k))`. This file compares the extension by zero `j_!` along open immersions on the
bounded constructible derived categories `Dᵇc(-)⟦Λ⟧` with pullbacks and pushforwards along a
commutative square
```
X' --g'--> X
|          |
j'         j
v          v
Z' --g---> Z
```
with `j` and `j'` open immersions.

* **Base change for extension by zero.** The canonical exchange morphism
  `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange'`) is an
  isomorphism for a cartesian square
  (`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange'`).
* **The exchange morphism.** For the inverse of this isomorphism, the mate under the adjunctions
  `Lg'^* ⊣ Rg'_*` and `Lg^* ⊣ Rg_*` is the *exchange morphism* `Rg'_* ⋙ j_! ⟶ j'_! ⋙ Rg_*`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'`, where
  the square is written `IsPullback p i' j p'`). For a cartesian square with `g` proper it is an
  isomorphism, for the coefficient rings `E̲` of a finite extension `E` of `ℚ_ℓ` and `ℚ̲̄_ℓ`: this
  is the coefficient analogue of part (3) of the interchange lemma, proved in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange`.

Both morphisms are the exchange morphisms `CategoryTheory.Adjunction.exchangeLeft` and
`CategoryTheory.Adjunction.exchangeRight` of the abstract mate calculus of
`WeilConjectures.CategoryTheory.Adjunction.ExchangeMate`
(`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft`
and `..._eq_exchangeRight` for the exchange morphism).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange'` and, for a
  cartesian square, its inverse
  `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'`.
- `ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'`: the
  exchange morphism `Rg'_* ⋙ j_! ⟶ j'_! ⋙ Rg_*`.

## Base change for extension by zero

`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange'` (blueprint
`sk-def-sfb-open-base-change`): the restrictions to `X'` and to its closed complement jointly
reflect isomorphisms. Over `X'` the exchange morphism is an isomorphism because both extensions
by zero are fully faithful (`CategoryTheory.Adjunction.isIso_map_exchangeLeft_app`). Over the
closed complement both sides vanish: the square being cartesian, the complement of `X'` maps into
the complement of `X`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Base change for extension by zero -/

section BaseChange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

include ℓ k

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
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep' :
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
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep'
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
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep' :
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

omit ℓ k in
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
noncomputable irreducible_def boundedConstructibleOpenImmersionLowerShriekBaseChange'
    (sq : CommSq g' j' j g) :
    boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g :=
  boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep' Λ ℓ j j' g' ≫
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep' Λ ℓ sq).hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep' Λ ℓ j g j'

/-- The exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is the exchange morphism
`CategoryTheory.Adjunction.exchangeLeft` of the pullback comparison of the square under the
adjunctions `j_! ⊣ Lj^*` and `j'_! ⊣ Lj'^*`. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft
    (sq : CommSq g' j' j g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq.flip) := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange'_def]
  unfold boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep'
    boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep'
    boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep' Adjunction.exchangeLeft
  rfl

/-- **Base change for extension by zero** (blueprint `sk-def-sfb-open-base-change`) on bounded
constructible complexes: for a *cartesian* square with `j` and `j'` open immersions, the exchange
morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is an isomorphism.

Mathematically, since the square is cartesian, `X'` is the preimage of the open subscheme
`X ⊆ Z` under `g`, and on stalks at points of `Z'_proét` both sides are the pulled-back stalk at
points of `X'` and vanish outside `X'`. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' (sq : IsPullback g' j' j g) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq.toCommSq) := by
  have : QuasiCompact (j'.left ≫ Z'.hom) := by
    rw [Over.w j']
    infer_instance
  have : QuasiCompact j'.left := QuasiCompact.of_comp j'.left Z'.hom
  -- The range of `j'` is the preimage of the range of `j` under `g`.
  have hrange : Set.range j'.left.base = g.left.base ⁻¹' Set.range j.left.base := by
    have hsq : IsPullback g'.left j'.left j.left g.left := sq.map (Over.forget _)
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨g'.left y, by rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]⟩
    · intro hx
      have hx' : x ∈ Set.range (pullback.snd j.left g.left) := by
        rw [IsOpenImmersion.range_pullbackSnd]
        exact hx
      obtain ⟨z, rfl⟩ := hx'
      exact ⟨hsq.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd]⟩
  let c := overClosedComplement j'
  have hK (K : Dᵇc(X.left)⟦Λ⟧) :
      IsIso ((boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq.toCommSq).app K) := by
    refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl Λ ℓ c j'
      (isCompl_range_overClosedComplement j') _ ?_ ?_
    · -- Over `X'`: both extensions by zero are fully faithful.
      rw [boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft]
      exact Adjunction.isIso_map_exchangeLeft_app _ _ _ K
    · -- Over the closed complement of `X'`: both sides vanish.
      have hS : IsZero ((boundedConstructibleUpperStar Λ ℓ c).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j').obj
            ((boundedConstructibleUpperStar Λ ℓ g').obj K))) :=
        isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ j' c
          (isCompl_range_overClosedComplement j').disjoint.symm _
      have hdisj : Disjoint (Set.range j.left.base) (Set.range (c ≫ g).left.base) := by
        rw [Set.disjoint_left]
        rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
        have hy' : c.left y ∈ Set.range j'.left.base := by
          rw [hrange]
          exact ⟨x, by simpa using hy.symm⟩
        exact (isCompl_range_overClosedComplement j').disjoint.ne_of_mem ⟨y, rfl⟩ hy' rfl
      have hT : IsZero ((boundedConstructibleUpperStar Λ ℓ c).obj
          ((boundedConstructibleUpperStar Λ ℓ g).obj
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K))) :=
        (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ j (c ≫ g) hdisj
          K).of_iso ((boundedConstructibleUpperStarComp Λ ℓ c g).app _).symm
      exact ⟨⟨hT.to_ _, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩
  exact NatIso.isIso_of_isIso_app _

/-- The extension-by-zero exchange isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!` on bounded
constructible complexes for a cartesian square of open immersions: the inverse of the canonical
exchange morphism, which is an isomorphism by base change for extension by zero. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
    (sq : IsPullback g' j' j g) :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g ≅
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq
  (asIso (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq.toCommSq)).symm

end BaseChange

/-! ### The exchange morphism -/

section Exchange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

include ℓ k

/-- The *unit insertion* step of the exchange morphism: the natural transformation
`Rp_* ⋙ j_! ⟶ (Rp_* ⋙ j_!) ⋙ (Lp'^* ⋙ Rp'_*)` obtained by inserting the unit of the adjunction
`Lp'^* ⊣ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep' :
    boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j ⟶
      (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
          (Profinite.padicAlgClRingObj ℓ) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p' ⋙
            boundedConstructibleLowerStar ℓ p') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction ℓ p').unit

/-- The *square transport* step of the exchange morphism: `Functor.squareTransport` applied to
the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!` of the cartesian
square, under `Rp_*` on the left and `Rp'_*` on the right. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep'
    (sq : IsPullback p i' j p') :
    (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p' ⋙
            boundedConstructibleLowerStar ℓ p') ≅
      (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleUpperStar
          (Profinite.padicAlgClRingObj ℓ) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ p') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ p)
    (boundedConstructibleLowerStar ℓ p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' (Profinite.padicAlgClRingObj ℓ) ℓ
        sq)

/-- The *counit contraction* step of the exchange morphism: the natural transformation
`(Rp_* ⋙ Lp^*) ⋙ (i'_! ⋙ Rp'_*) ⟶ i'_! ⋙ Rp'_*` obtained by contracting the counit of the
adjunction `Lp^* ⊣ Rp_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep' :
    (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj
        ℓ) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ p') ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ p' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The *exchange morphism* `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` on bounded constructible complexes for
a cartesian square
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` and `i'` open immersions: the mate, under the adjunctions `Lp^* ⊣ Rp_*` and
`Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!`
(`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'`), assembled as the composite of the
unit insertion, the square transport, and the counit contraction:
`Rp_* ⋙ j_! ⟶ Rp_* ⋙ j_! ⋙ Lp'^* ⋙ Rp'_* ≅ Rp_* ⋙ Lp^* ⋙ i'_! ⋙ Rp'_* ⟶ i'_! ⋙ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ p' :=
  boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep' ℓ ≫
    (boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep' ℓ sq).hom ≫
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep' ℓ


/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the extension-by-zero base-change isomorphism under
the adjunctions `Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`. -/
lemma boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchangeRight
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq =
      Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ p)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ p')
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' (Profinite.padicAlgClRingObj ℓ)
            ℓ sq) := by
  unfold boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep'
    Adjunction.exchangeRight
  rfl

/-- The inverse of the extension-by-zero base-change isomorphism is the exchange morphism
`CategoryTheory.Adjunction.exchangeLeft` of the pullback comparison. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'_inv
    (sq : IsPullback p i' j p') :
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq).inv =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip) :=
  boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft Λ ℓ sq.toCommSq

end Exchange

end AlgebraicGeometry.ProEtale.CondensedRing
