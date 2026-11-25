/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal

/-!
# The derived internal hom out of the comparison pullback of a dualizable complex

Let `Λ` be a noetherian commutative ring, `X` a scheme, and `D`, `P` objects of `D(X_ét, Λ)`
forming an exact pairing. The levelwise comparison pullback `ν^* = D(ν^*)` is strong monoidal,
so `ν^*D` is a left dual of `ν^*P` in `D(X_proét, Λ)`, and hence
`RHom(ν^*P, ν^*N) ≅ ν^*D ⊗ᴸ ν^*N ≅ ν^*(D ⊗ᴸ N)`. In particular `RHom(ν^*P, ν^*N)` is of étale
origin as soon as `D ⊗ᴸ N` is bounded below.

## Main definitions

- `AlgebraicGeometry.ProEtale.mapDerivedCategoryComparisonUpperStarMonoidal`: the strong monoidal
  structure on `D(ν^*)`, whose comonoidal structure is the derived tensor comparison.
- `AlgebraicGeometry.ProEtale.derivedHomMapDerivedCategoryIsoOfExactPairing`: the isomorphism
  `RHom(ν^*P, ν^*N) ≅ ν^*(D ⊗ᴸ N)`.

## Main statements

- `AlgebraicGeometry.ProEtale.plusEtaleOrigin_derivedHom_mapDerivedCategory_of_exactPairing`:
  `RHom(ν^*P, ν^*N)` is bounded below of étale origin if `D ⊗ᴸ N` is bounded below.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

/-- The strong monoidal structure on the levelwise comparison pullback
`D(ν^*) : D(X_ét) ⥤ D(X_proét)`, whose comonoidal structure is the derived tensor comparison
`CategoryTheory.Functor.mapDerivedCategoryTensorComparison` of the strong monoidal functor `ν^*`
(`CategoryTheory.Functor.mapDerivedCategoryOplaxMonoidal`); its structure maps are invertible. -/
@[instance_reducible]
noncomputable def mapDerivedCategoryComparisonUpperStarMonoidal [(ν^*(X)[A]).PreservesFlat] :
    (D(ν^*(X)[A])).Monoidal :=
  letI := (ν^*(X)[A]).mapDerivedCategoryOplaxMonoidal
  haveI := (ν^*(X)[A]).isIso_mapDerivedCategoryOplaxMonoidal_η
  haveI (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      IsIso (Functor.OplaxMonoidal.δ D(ν^*(X)[A]) K M) := by
    rw [Functor.mapDerivedCategoryOplaxMonoidal_δ]
    infer_instance
  Functor.Monoidal.ofOplaxMonoidal _

variable {A X}

/-- For an exact pairing of `D` and `P` in `D(X_ét)`, the isomorphism
`RHom(ν^*P, ν^*N) ≅ ν^*(D ⊗ᴸ N)`: as `ν^*` is strong monoidal
(`AlgebraicGeometry.ProEtale.mapDerivedCategoryComparisonUpperStarMonoidal`), `ν^*D` is a left
dual of `ν^*P`, so `RHom(ν^*P, -) ≅ ν^*D ⊗ᴸ -`, and `ν^*D ⊗ᴸ ν^*N ≅ ν^*(D ⊗ᴸ N)`. -/
noncomputable def derivedHomMapDerivedCategoryIsoOfExactPairing [(ν^*(X)[A]).PreservesFlat]
    (D P N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) [ExactPairing D P] :
    ((ProEtale.derivedHom A X).obj (op (D(ν^*(X)[A]).obj P))).obj (D(ν^*(X)[A]).obj N) ≅
      D(ν^*(X)[A]).obj (((Etale.derivedTensor A X).obj D).obj N) :=
  letI := mapDerivedCategoryComparisonUpperStarMonoidal A X
  letI := ExactPairing.map D(ν^*(X)[A]) D P
  MonoidalClosed.ihomObjIsoTensor (D(ν^*(X)[A]).obj D) (D(ν^*(X)[A]).obj P)
      (D(ν^*(X)[A]).obj N) ≪≫ Functor.Monoidal.μIso D(ν^*(X)[A]) D N

end General

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ] {X : Scheme.{u}}

/-- For an exact pairing of `D` and `P` in `D(X_ét, Λ)` and `N` with `D ⊗ᴸ N` bounded below,
`RHom(ν^*P, ν^*N)` is bounded below of étale origin: it is isomorphic to `ν^*(D ⊗ᴸ N)`
(`AlgebraicGeometry.ProEtale.derivedHomMapDerivedCategoryIsoOfExactPairing`). -/
theorem plusEtaleOrigin_derivedHom_mapDerivedCategory_of_exactPairing
    (D P N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [ExactPairing D P]
    (hDN : _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj D).obj N)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X
      (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
        (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj P))).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj N)) :=
  ObjectProperty.prop_of_iso _ (derivedHomMapDerivedCategoryIsoOfExactPairing D P N).symm
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hDN)

end AlgebraicGeometry.ProEtale
