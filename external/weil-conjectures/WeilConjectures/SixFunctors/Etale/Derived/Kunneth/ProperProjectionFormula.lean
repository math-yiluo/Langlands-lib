/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange

/-!
# The projection formula for proper morphisms

For a proper morphism `f : X ⟶ Y` and a coefficient ring `Λ` which is torsion as an additive
group, the projection map

`Rf_* E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^* K)`

(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`) is an isomorphism for all
`E ∈ D(X_ét, Λ)` and `K ∈ D(Y_ét, Λ)`, unbounded (blueprint
`proposition-proper-direct-image-constructible-complexes--9`, Stacks 0F0G).

The proof checks the claim at the geometric points `x : Spec Ω ⟶ Y`, `Ω` an algebraic closure
of a residue field of `Y`, which jointly detect isomorphisms of `D(Y_ét, Λ)`
(`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map`). The
projection map commutes with base change
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`), and by
unbounded proper base change (`theorem-results-from-etale-theory--1`) the pullback of the projection
map to `x` is the projection map of the geometric fibre `f' : X ×_Y Spec Ω ⟶ Spec Ω`. The fibre is a
proper `Ω`-scheme, so it has finite cohomological dimension
(`theorem-results-from-etale-theory--6`), and over the separably closed field `Ω` the projection map
is an isomorphism by `proposition-open-direct-image-preserves-finite`.

The blueprint proves the statement instead by checking it on `K = Λ` and passing to homotopy
colimits; the argument above uses the same inputs `theorem-results-from-etale-theory--6`,
`proposition-open-direct-image-preserves-finite` (through
`proposition-open-direct-image-preserves-finite`) together with
`theorem-results-from-etale-theory--1`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map`
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_isProper`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Geometric points detect isomorphisms of `D(Y_ét, Λ)`**: a morphism `φ` of the unbounded
derived category whose derived pullbacks to all the geometric points `Spec Ω ⟶ Y`, `Ω` an
algebraic closure of a residue field of `Y`, are isomorphisms is an isomorphism. -/
theorem isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map {Y : Scheme.{u}}
    {M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (h : ∀ y : Y, IsIso ((L((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ])).map φ)) :
    IsIso φ := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun y ↦ Y.algClosurePoint y)
    (fun y ↦ ⟨y, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _ fun y ↦ ?_
  have h' : IsIso (D((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ]).map φ) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ _) φ).1 (h y)
  exact (NatIso.isIso_map_iff
    (((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ]).map φ))

/-- The pullback of the projection map of a proper morphism `f : X ⟶ Y` to a geometric point
`x : Spec Ω ⟶ Y`, `Ω` separably closed, is an isomorphism: by proper base change it is the
projection map of the geometric fibre `X ×_Y Spec Ω ⟶ Spec Ω`
(`theorem-results-from-etale-theory--1`), which is an isomorphism over a separably closed field
(`proposition-open-direct-image-preserves-finite`, with `theorem-results-from-etale-theory--6`). -/
theorem isIso_leftDerivedUpperStar_map_rightDerivedLowerStarProjectionMap_of_isProper
    (hΛ : IsAddTorsion Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Y)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((L((x)^*[ModuleCat.{u + 1} Λ])).map
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app L)) := by
  have sq := IsPullback.of_hasPullback f x
  have : IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
    isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ hΛ sq
  have : CompactSpace (pullback f x : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  have : IsLocallyNoetherian (pullback f x : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f x)
  -- over the separably closed field `Ω`, the projection map is an isomorphism
  -- (`proposition-open-direct-image-preserves-finite`)
  have : IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ)
      (pullback.snd f x)).app ((L((pullback.fst f x)^*[ModuleCat.{u + 1} Λ])).obj E)).app
        ((L((x)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
    isIso_rightDerivedLowerStarProjectionMap_of_isSepClosed Λ (pullback.snd f x)
      (hasFiniteCohomologicalDimension_of_isSepClosed Λ hΛ (pullback.snd f x)) _ _
  exact IsIso.of_isIso_fac_right
    (rightDerivedLowerStarProjectionMap_derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq E L)

/-- Blueprint `proposition-proper-direct-image-constructible-complexes--9`: projection formula for
proper morphisms.

Let `f : X ⟶ Y` be a proper morphism and `Λ` a ring which is torsion as an additive group. For
`E ∈ D(X_ét, Λ)` and `K ∈ D(Y_ét, Λ)`, unbounded, the projection map
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`)

`Rf_* E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^* K)`

is an isomorphism. -/
theorem isIso_rightDerivedLowerStarProjectionMap_of_isProper (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    IsIso (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f) := by
  have (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E) := by
    have (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
        IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app L) :=
      isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map Λ _ fun y ↦
        isIso_leftDerivedUpperStar_map_rightDerivedLowerStarProjectionMap_of_isProper Λ hΛ f _ E L
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

end Etale

end AlgebraicGeometry
