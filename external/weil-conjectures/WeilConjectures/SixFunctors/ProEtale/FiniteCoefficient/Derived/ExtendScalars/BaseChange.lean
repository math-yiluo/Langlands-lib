/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.UpperStarCoherence

/-!
# Derived scalar extension and the derived base change maps

Let `S` be an algebra over a noetherian commutative ring `R` and write `Ψ = - ⊗ᴸ_R S` for the
derived extension of scalars `L(sheafExtendScalars (algebraMap R S) X)` of pro-étale sheaves.
For a commutative square of schemes
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
the derived base change maps `Lg^* Rf_* ⟶ Rf'_* Lg'^*`
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`) with coefficients `R` and `S` are compatible
with `Ψ`, the commutations `Lg^* Ψ ≅ Ψ Lg^*` of `Ψ` with the derived pullbacks
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`) and the base change maps
`Ψ Rf_* ⟶ Rf_* Ψ` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarExtendScalarsMap`): the cube
formed by these maps commutes. All maps are mates of isomorphisms of derived pullbacks, and the
corresponding cube of derived pullbacks commutes by the coherence of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso` with the composition and
congruence isomorphisms (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`).

## Main results

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso_hom_app_square`: the cube of
  derived pullbacks.
- `AlgebraicGeometry.ProEtale.derivedBaseChangeMap_extendScalars_app`: the cube of base change
  maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **Derived scalar extension and the square isomorphisms of derived pullbacks.** For a
commutative square `g' ≫ f = f' ≫ g`, the commutations of `Ψ` with the derived pullbacks
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`) are compatible with the
square isomorphisms `Lf'^* Lg^* ≅ Lg'^* Lf^*`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso`). -/
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_square (sq : CommSq g' f' f g)
    (M : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    L((f')^*[ModuleCat.{u + 1} S]).map ((leftDerivedUpperStarExtendScalarsIso R S g).hom.app M) ≫
        (leftDerivedUpperStarExtendScalarsIso R S f').hom.app
          (L((g)^*[ModuleCat.{u + 1} R]).obj M) ≫
        L(sheafExtendScalars (algebraMap R S) X').map
          ((leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} R) sq).hom.app M) =
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} S) sq).hom.app
          (L(sheafExtendScalars (algebraMap R S) Y).obj M) ≫
        L((g')^*[ModuleCat.{u + 1} S]).map
          ((leftDerivedUpperStarExtendScalarsIso R S f).hom.app M) ≫
        (leftDerivedUpperStarExtendScalarsIso R S g').hom.app
          (L((f)^*[ModuleCat.{u + 1} R]).obj M) := by
  rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} S) f' g).hom.app
    (L(sheafExtendScalars (algebraMap R S) Y).obj M))]
  simp only [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← leftDerivedUpperStarExtendScalarsIso_hom_app_comp_assoc,
    ← Functor.map_comp_assoc _ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} R) f' g).hom.app M),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    ← leftDerivedUpperStarExtendScalarsIso_hom_app_comp,
    leftDerivedUpperStarExtendScalarsIso_hom_app_congr_assoc]

/-- **Derived scalar extension commutes with the derived base change maps.** For a commutative
square `g' ≫ f = f' ≫ g` of schemes and `K` in `D(X_proét, R)`, the two composites
`Lg^* Ψ (Rf_* K) ⟶ Rf'_* Ψ (Lg'^* K)`
```
Lg^* Ψ Rf_* K ──α_g──▶ Ψ Lg^* Rf_* K ──Ψ(BC)──▶ Ψ Rf'_* Lg'^* K ──β_{f'}──▶ Rf'_* Ψ Lg'^* K
Lg^* Ψ Rf_* K ──Lg^* β_f──▶ Lg^* Rf_* Ψ K ──BC──▶ Rf'_* Lg'^* Ψ K ──Rf'_* α_{g'}──▶ Rf'_* Ψ Lg'^* K
```
agree, where `BC` is the derived base change map
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`), `α` the commutation of `Ψ` with the
derived pullbacks and `β` the base change map of `Ψ` along `Rf_*`. This is an input for the
compatibility of compact cohomology with the change of coefficients (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`). -/
theorem derivedBaseChangeMap_extendScalars_app (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S g).hom.app (R((f)_*[ModuleCat.{u + 1} R]).obj K) ≫
        L(sheafExtendScalars (algebraMap R S) Y').map
          ((derivedBaseChangeMap (ModuleCat.{u + 1} R) sq).app K) ≫
        (rightDerivedLowerStarExtendScalarsMap R S f').app
          (L((g')^*[ModuleCat.{u + 1} R]).obj K) =
      L((g)^*[ModuleCat.{u + 1} S]).map ((rightDerivedLowerStarExtendScalarsMap R S f).app K) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} S) sq).app
          (L(sheafExtendScalars (algebraMap R S) X).obj K) ≫
        R((f')_*[ModuleCat.{u + 1} S]).map
          ((leftDerivedUpperStarExtendScalarsIso R S g').hom.app K) :=
  mateEquiv_app_cube (derivedUpperStarLowerStarAdjunction _ f)
    (derivedUpperStarLowerStarAdjunction _ f') (derivedUpperStarLowerStarAdjunction _ f)
    (derivedUpperStarLowerStarAdjunction _ f') (leftDerivedUpperStarSquareIso _ sq).hom
    (leftDerivedUpperStarSquareIso _ sq).hom (leftDerivedUpperStarExtendScalarsIso R S f).hom
    (leftDerivedUpperStarExtendScalarsIso R S f').hom
    (leftDerivedUpperStarExtendScalarsIso R S g).hom
    (leftDerivedUpperStarExtendScalarsIso R S g').hom
    (leftDerivedUpperStarExtendScalarsIso_hom_app_square R S sq) K

end AlgebraicGeometry.ProEtale
