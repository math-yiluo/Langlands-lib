/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange

/-!
# The projection formula morphism

Inputs of the ordinary Künneth formula (blueprint subsection
`proposition-ordinary-external-kunneth--1`) about the projection formula morphism
`Rf_* E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^* K)`.

## Main definitions and results

- `AlgebraicGeometry.Etale.projectionFormulaMap` (`definition-projection-formula-map--1`).
- `AlgebraicGeometry.Etale.projectionFormulaMap_derivedBaseChangeMap`
  (`lem-kun-proj-formula-natural`).
- `AlgebraicGeometry.Etale.isIso_projectionFormulaMap_of_isProper`
(`corollary-open-direct-image-over-field--2`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

/-- Blueprint `definition-projection-formula-map--1`: for a morphism of schemes `f : X ⟶ Y`,
`E ∈ D(X_ét)` and `K ∈ D(Y_ét)`, the projection-formula morphism

`PF_f(E, K) : Rf_* E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^* K)`

is the morphism adjoint (along `Lf^* ⊣ Rf_*`) to the composite
`Lf^*(Rf_* E ⊗ᴸ K) ≅ Lf^* Rf_* E ⊗ᴸ Lf^* K ⟶ E ⊗ᴸ Lf^* K` of the monoidality isomorphism of
`Lf^*` and `ε ⊗ 1`, `ε` being the counit
(`AlgebraicGeometry.Etale.homEquiv_symm_projectionFormulaMap`). It is the component of the
natural transformation `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`. -/
noncomputable def projectionFormulaMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((-⊗ᴸ-(Y)[A]).obj (R((f)_*[A]).obj E)).obj K ⟶
      R((f)_*[A]).obj (((-⊗ᴸ-(X)[A]).obj E).obj (L((f)^*[A]).obj K)) :=
  ((rightDerivedLowerStarProjectionMap A f).app E).app K

/-- The projection-formula morphism is adjoint to the composite of the monoidality isomorphism
of `Lf^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`) and `ε ⊗ 1`. -/
lemma homEquiv_symm_projectionFormulaMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedUpperStarLowerStarAdjunction A f).homEquiv _ _).symm
        (projectionFormulaMap A f E K) =
      ((leftDerivedUpperStarTensorComparison A f).app (R((f)_*[A]).obj E)).app K ≫
        ((-⊗ᴸ-(X)[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E)).app
          (L((f)^*[A]).obj K) :=
  homEquiv_symm_rightDerivedLowerStarProjectionMap A f E K

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Blueprint `lem-kun-proj-formula-natural`: the projection formula commutes with base change.
For a commutative (for instance cartesian) square `g' ≫ f = f' ≫ g`, `E ∈ D(X_ét)` and
`K ∈ D(Y_ét)`, the square
```
Lg^*(Rf_*E ⊗ᴸ K) ──Lg^* PF_f──▶ Lg^*Rf_*(E ⊗ᴸ Lf^*K) ──Ex──▶ Rf'_*Lg'^*(E ⊗ᴸ Lf^*K)
       │                                                          │
       ▼                                                          ▼
Lg^*Rf_*E ⊗ᴸ Lg^*K ──Ex ⊗ 1──▶ Rf'_*Lg'^*E ⊗ᴸ Lg^*K ──PF_f'──▶ Rf'_*(Lg'^*E ⊗ᴸ Lf'^*Lg^*K)
```
commutes, where the vertical arrows are the monoidality isomorphisms of the derived pullbacks,
`Ex` is the base change map `AlgebraicGeometry.Etale.derivedBaseChangeMap`, and the bottom row
ends with the identification `Lf'^*Lg^* ≅ Lg'^*Lf^*`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`). -/
lemma projectionFormulaMap_derivedBaseChangeMap (sq : CommSq g' f' f g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map (projectionFormulaMap A f E K) ≫
        (derivedBaseChangeMap A sq).app (((-⊗ᴸ-(X)[A]).obj E).obj (L((f)^*[A]).obj K)) ≫
        R((f')_*[A]).map (((leftDerivedUpperStarTensorComparison A g').app E).app
          (L((f)^*[A]).obj K)) =
      ((leftDerivedUpperStarTensorComparison A g).app (R((f)_*[A]).obj E)).app K ≫
        ((-⊗ᴸ-(Y')[A]).map ((derivedBaseChangeMap A sq).app E)).app (L((g)^*[A]).obj K) ≫
        projectionFormulaMap A f' (L((g')^*[A]).obj E) (L((g)^*[A]).obj K) ≫
        R((f')_*[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj E)).map
          ((derivedSquareUpperStarIso A sq).hom.app K)) :=
  rightDerivedLowerStarProjectionMap_derivedBaseChangeMap A sq E K

/-- Blueprint `corollary-open-direct-image-over-field--2`: the projection formula for a proper
morphism with torsion coefficients. Let `f : X ⟶ Y` be proper and `Λ` a ring which is torsion as an
additive group (for instance `Λ = ℤ/n`). Then for all `E ∈ D(X_ét, Λ)` and `K ∈ D(Y_ét, Λ)` the
projection-formula morphism `Rf_* E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^* K)` is an isomorphism.

The blueprint states this with integer coefficients, for `E ∈ D⁺(X_ét, ℤ)` with torsion
cohomology and `K ∈ D⁺(Y_ét, ℤ)`. That version is not available in this development; we state
the projection formula with coefficients in a torsion ring instead, which is the form used by
the Künneth formula with finite coefficients. It holds without boundedness assumptions
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_isProper`, which uses
proper base change). -/
theorem isIso_projectionFormulaMap_of_isProper (Λ : Type (u + 1)) [CommRing Λ]
    (hΛ : IsAddTorsion Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (projectionFormulaMap (ModuleCat.{u + 1} Λ) f E K) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ hΛ f
  dsimp [projectionFormulaMap]
  infer_instance

end Etale

end AlgebraicGeometry
