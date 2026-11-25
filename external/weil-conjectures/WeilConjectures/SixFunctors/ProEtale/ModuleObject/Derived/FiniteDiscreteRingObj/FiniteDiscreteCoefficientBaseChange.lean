/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitBallRingObj.FiniteDiscreteCoefficient

/-!

# The base-change morphism on bounded constructible module objects over `T̲` and `O̲`

This file is the counterpart of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` for the two
coefficient rings of
the module `UnitBallRingObj.FiniteDiscreteCoefficient`:
`T̲ = Profinite.continuousMapRingObj T` for a finite discrete ring `T` in which `ℓ` is nilpotent
(namespace `ProEtale.CondensedRing.FiniteDiscreteRingObj`), and
`O̲ = Profinite.continuousMapRingObj O` for the closed unit ball `O` of a finite normed extension
`E` of `ℚ_ℓ` (namespace `ProEtale.CondensedRing.UnitBallRingObj`). For a commutative square
`sq : CommSq g' f' f g` of separated `k`-schemes of finite type, the base-change morphism

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` (in diagrammatic `⋙`-order)

on `Dᵇc(-)⟦T̲⟧` and `Dᵇc(-)⟦O̲⟧` is the composite of the unit insertion, the square transport
along the pullback comparison `boundedConstructiblePullbackSquareComparison` (stated for a general
`Λ` in `MorphismDefs`) and the counit contraction, with the names of `MorphismDefs`.

## Main definitions

- `boundedConstructibleBaseChangeUnitStep`, `boundedConstructibleBaseChangeSquareStep`,
  `boundedConstructibleBaseChangeCounitStep`: the three steps.
- `boundedConstructibleBaseChange`: the base-change morphism `BC_sq`.

## Main results

- `boundedConstructibleBaseChange_eq_unit_square_counit`: the defining equation of `BC_sq`.
- `boundedConstructibleBaseChange_eq_exchangeRight`: `BC_sq` is the exchange morphism
  `CategoryTheory.Adjunction.exchangeRight` of `θ_sq`.
- `boundedConstructibleBaseChange_adjunct`: the adjunct of `BC_sq` under `Lf'^* ⊣ Rf'_*` is
  `θ_sq` followed by `Lg'^*` of the counit of `Lf^* ⊣ Rf_*`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

/-- The adjunct formula `Adjunction.squareExchange_map_counit`, for a transformation `β` known to
be equal to the square exchange. -/
private lemma squareExchange_map_counit_of_eq {C D C' D' : Type*} [Category C] [Category D]
    [Category C'] [Category D'] {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D') (θ : G ⋙ L' ≅ L ⋙ H)
    {β : R ⋙ G ⟶ H ⋙ R'} (h : β = Adjunction.squareExchange a b G H θ) (N : D) :
    L'.map (β.app N) ≫ b.counit.app (H.obj N) = θ.hom.app (R.obj N) ≫ H.map (a.counit.app N) := by
  subst h
  exact Adjunction.squareExchange_map_counit a b G H θ N

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

include ℓ k

/-! ### The coefficient ring `T̲`, `T` a finite discrete ring in which `ℓ` is nilpotent -/

namespace FiniteDiscreteRingObj

section BaseChange

variable (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
  [hTd : DiscreteTopology T] [hTf : Finite T] [hT : Fact (IsNilpotent (ℓ : T))]

include hTd hTf hT

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes
(`T`-coefficient): the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained
by inserting the unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def boundedConstructibleBaseChangeUnitStep :
    boundedConstructibleLowerStar ℓ T f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj T) ℓ g ⟶
      (boundedConstructibleLowerStar ℓ T f ⋙ boundedConstructibleUpperStar
        (Profinite.continuousMapRingObj T) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ T f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStar ℓ T f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj T) ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f').unit

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes (`T`-coefficient): `Functor.squareTransport` applied to the pullback comparison `θ_sq`,
under `Rf_*` on the left and `Rf'_*` on the right. -/
noncomputable def boundedConstructibleBaseChangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar ℓ T f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj T) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ T f') ≅
      (boundedConstructibleLowerStar ℓ T f ⋙ boundedConstructibleUpperStar
        (Profinite.continuousMapRingObj T) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ T f') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ T f)
    (boundedConstructibleLowerStar ℓ T f') (boundedConstructiblePullbackSquareComparison
      (Profinite.continuousMapRingObj T) ℓ sq)

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes (`T`-coefficient): the natural transformation obtained by contracting the counit of the
adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def boundedConstructibleBaseChangeCounitStep :
    (boundedConstructibleLowerStar ℓ T f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj T) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ T f') ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ T f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f).counit
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ g' ⋙
      boundedConstructibleLowerStar ℓ T f') ≫
    (Functor.leftUnitor _).hom

variable {f g f' g'} in
/-- The *base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories of module objects
over `Λ`, assembled as the composite of the unit insertion, the square transport, and the
counit contraction (`T`-coefficient).

Proper base change asserts that this morphism is an isomorphism for a cartesian square with `f`
proper; no such hypothesis is built into the definition. -/
@[no_expose]
noncomputable def boundedConstructibleBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStar ℓ T f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj T) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ T f' :=
  boundedConstructibleBaseChangeUnitStep ℓ T f g f' ≫
    (boundedConstructibleBaseChangeSquareStep ℓ T sq).hom ≫
      boundedConstructibleBaseChangeCounitStep ℓ T f f' g'

variable {f g f' g'} in
private theorem boundedConstructibleBaseChange_def (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ T sq =
      boundedConstructibleBaseChangeUnitStep ℓ T f g f' ≫
        (boundedConstructibleBaseChangeSquareStep ℓ T sq).hom ≫
          boundedConstructibleBaseChangeCounitStep ℓ T f f' g' :=
  rfl

variable {f g f' g'} in
/-- The defining equation of `boundedConstructibleBaseChange` (`T`-coefficient): the composite of
the unit insertion, the square transport and the counit contraction. -/
theorem boundedConstructibleBaseChange_eq_unit_square_counit (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ T sq =
      boundedConstructibleBaseChangeUnitStep ℓ T f g f' ≫
        (boundedConstructibleBaseChangeSquareStep ℓ T sq).hom ≫
          boundedConstructibleBaseChangeCounitStep ℓ T f f' g' :=
  boundedConstructibleBaseChange_def ℓ T sq

variable {f g f' g'} in
/-- The base-change morphism `BC_sq` is the square exchange `Adjunction.squareExchange` of the
pullback comparison `θ_sq` under the adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`
(`T`-coefficient). -/
theorem boundedConstructibleBaseChange_eq_squareExchange (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ T sq =
      Adjunction.squareExchange
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f')
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ g)
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ g')
        (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj T) ℓ sq) := by
  refine (boundedConstructibleBaseChange_eq_unit_square_counit ℓ T sq).trans ?_
  exact (Adjunction.squareExchange_eq_unit_square_counit
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f')
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ g)
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ g')
    (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj T) ℓ sq)).symm

variable {f g f' g'} in
/-- The base-change morphism `BC_sq` is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the pullback comparison `θ_sq` under the
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*` (`T`-coefficient). -/
lemma boundedConstructibleBaseChange_eq_exchangeRight (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ T sq =
      Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f')
        (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj T) ℓ sq) := by
  unfold boundedConstructibleBaseChange boundedConstructibleBaseChangeUnitStep
    boundedConstructibleBaseChangeSquareStep boundedConstructibleBaseChangeCounitStep
    Adjunction.exchangeRight
  rfl

-- Match the restricted functors without unfolding their derived implementations.
attribute [local irreducible] boundedConstructibleUpperStar boundedConstructibleLowerStar
  boundedConstructibleUpperStarLowerStarAdjunction boundedConstructiblePullbackSquareComparison

end BaseChange

end FiniteDiscreteRingObj

/-! ### The coefficient ring `O̲`, `O` the closed unit ball of a finite extension of `ℚ_ℓ` -/

namespace UnitBallRingObj

section BaseChange

variable {E : Type} [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [hE : FiniteDimensional ℚ_[ℓ] E]
  (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]

include hE hO

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes
(`O`-coefficient): the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained
by inserting the unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def boundedConstructibleBaseChangeUnitStep :
    boundedConstructibleLowerStar ℓ O f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj O) ℓ g ⟶
      (boundedConstructibleLowerStar ℓ O f ⋙ boundedConstructibleUpperStar
        (Profinite.continuousMapRingObj O) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ O f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStar ℓ O f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj O) ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f').unit

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes (`O`-coefficient): `Functor.squareTransport` applied to the pullback comparison `θ_sq`,
under `Rf_*` on the left and `Rf'_*` on the right. -/
noncomputable def boundedConstructibleBaseChangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar ℓ O f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj O) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ O f') ≅
      (boundedConstructibleLowerStar ℓ O f ⋙ boundedConstructibleUpperStar
        (Profinite.continuousMapRingObj O) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ O f') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ O f)
    (boundedConstructibleLowerStar ℓ O f') (boundedConstructiblePullbackSquareComparison
      (Profinite.continuousMapRingObj O) ℓ sq)

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes (`O`-coefficient): the natural transformation obtained by contracting the counit of the
adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def boundedConstructibleBaseChangeCounitStep :
    (boundedConstructibleLowerStar ℓ O f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj O) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ O f') ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ O f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f).counit
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ g' ⋙
      boundedConstructibleLowerStar ℓ O f') ≫
    (Functor.leftUnitor _).hom

variable {f g f' g'} in
/-- The *base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories of module objects
over `Λ`, assembled as the composite of the unit insertion, the square transport, and the
counit contraction (`O`-coefficient).

Proper base change asserts that this morphism is an isomorphism for a cartesian square with `f`
proper; no such hypothesis is built into the definition. -/
@[no_expose]
noncomputable def boundedConstructibleBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStar ℓ O f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj O) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ O f' :=
  boundedConstructibleBaseChangeUnitStep ℓ O f g f' ≫
    (boundedConstructibleBaseChangeSquareStep ℓ O sq).hom ≫
      boundedConstructibleBaseChangeCounitStep ℓ O f f' g'

variable {f g f' g'} in
private theorem boundedConstructibleBaseChange_def (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ O sq =
      boundedConstructibleBaseChangeUnitStep ℓ O f g f' ≫
        (boundedConstructibleBaseChangeSquareStep ℓ O sq).hom ≫
          boundedConstructibleBaseChangeCounitStep ℓ O f f' g' :=
  rfl

variable {f g f' g'} in
/-- The defining equation of `boundedConstructibleBaseChange` (`O`-coefficient): the composite of
the unit insertion, the square transport and the counit contraction. -/
theorem boundedConstructibleBaseChange_eq_unit_square_counit (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ O sq =
      boundedConstructibleBaseChangeUnitStep ℓ O f g f' ≫
        (boundedConstructibleBaseChangeSquareStep ℓ O sq).hom ≫
          boundedConstructibleBaseChangeCounitStep ℓ O f f' g' :=
  boundedConstructibleBaseChange_def ℓ O sq

variable {f g f' g'} in
/-- The base-change morphism `BC_sq` is the square exchange `Adjunction.squareExchange` of the
pullback comparison `θ_sq` under the adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`
(`O`-coefficient). -/
theorem boundedConstructibleBaseChange_eq_squareExchange (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ O sq =
      Adjunction.squareExchange
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f')
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ g)
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ g')
        (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj O) ℓ sq) := by
  refine (boundedConstructibleBaseChange_eq_unit_square_counit ℓ O sq).trans ?_
  exact (Adjunction.squareExchange_eq_unit_square_counit
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f')
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ g)
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ g')
    (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj O) ℓ sq)).symm

variable {f g f' g'} in
/-- The base-change morphism `BC_sq` is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the pullback comparison `θ_sq` under the
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*` (`O`-coefficient). -/
lemma boundedConstructibleBaseChange_eq_exchangeRight (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ O sq =
      Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f')
        (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj O) ℓ sq) := by
  unfold boundedConstructibleBaseChange boundedConstructibleBaseChangeUnitStep
    boundedConstructibleBaseChangeSquareStep boundedConstructibleBaseChangeCounitStep
    Adjunction.exchangeRight
  rfl

-- Match the restricted functors without unfolding their derived implementations.
attribute [local irreducible] boundedConstructibleUpperStar boundedConstructibleLowerStar
  boundedConstructibleUpperStarLowerStarAdjunction boundedConstructiblePullbackSquareComparison

end BaseChange

end UnitBallRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
