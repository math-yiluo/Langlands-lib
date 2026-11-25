/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom

/-!
# The comparison pullback and the derived internal hom

Let `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` be the comparison pullback, which is strong monoidal
(`AlgebraicGeometry.ProEtale.monoidal_comparisonUpperStar`). Its derived tensor comparison
`CategoryTheory.Functor.leftDerivedTensorComparison` identifies `ν^*(K ⊗ᴸ M)` with
`ν^*K ⊗ᴸ ν^*M`. Passing to right adjoints gives the projection formula
`RHom(K, Rν_* N) ≅ Rν_* RHom(ν^* K, N)` for the comparison morphism.

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`:
  the isomorphism `ν^*(K ⊗ᴸ M) ≅ ν^*K ⊗ᴸ ν^*M` for the levelwise functor `D(ν^*)`.
- `AlgebraicGeometry.ProEtale.rightDerivedComparisonLowerStarCompDerivedHomIso`: the projection
  formula `RHom(K, Rν_* N) ≅ Rν_* RHom(ν^* K, N)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X : Scheme.{u}}

/-- For a fixed `K : D(X_ét)`, the isomorphism `ν^*(K ⊗ᴸ M) ≅ ν^*K ⊗ᴸ ν^*M` of functors of `M`,
for the levelwise functor `D(ν^*)`, obtained from the derived tensor comparison
`CategoryTheory.Functor.leftDerivedTensorComparison` of the strong monoidal functor `ν^*`. -/
noncomputable def derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    [(ν^*(X)[A]).PreservesFlat] (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedTensor A X).obj K ⋙ D(ν^*(X)[A]) ≅
      D(ν^*(X)[A]) ⋙ (ProEtale.derivedTensor A X).obj (D(ν^*(X)[A]).obj K) :=
  Functor.isoWhiskerLeft _ (ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (asIso (ν^*(X)[A]).leftDerivedTensorComparison).app K ≪≫
    Functor.isoWhiskerRight (ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.isoWhiskerLeft D(ν^*(X)[A]) ((ProEtale.derivedTensor A X).mapIso
      ((ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory.app K))

/-- The **projection formula for the comparison morphism**:
`RHom(K, Rν_* N) ≅ Rν_* RHom(ν^* K, N)`, naturally in `N : D(X_proét)`. The two sides are right
adjoint to `G ↦ ν^*(K ⊗ᴸ G)` and to `G ↦ ν^*K ⊗ᴸ ν^*G`, which agree because `ν^*` is strong
monoidal. -/
noncomputable def rightDerivedComparisonLowerStarCompDerivedHomIso [(ν^*(X)[A]).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    R(ν_*(X)[A]) ⋙ (Etale.derivedHom A X).obj (Opposite.op K) ≅
      (ProEtale.derivedHom A X).obj (Opposite.op (D(ν^*(X)[A]).obj K)) ⋙ R(ν_*(X)[A]) :=
  ((Etale.derivedTensorHomAdjunction A K).comp (derivedComparisonAdjunction A X)).rightAdjointUniq
    (((derivedComparisonAdjunction A X).comp
      (ProEtale.derivedTensorHomAdjunction A (D(ν^*(X)[A]).obj K))).ofNatIsoLeft
        (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A K).symm)

end AlgebraicGeometry.ProEtale
