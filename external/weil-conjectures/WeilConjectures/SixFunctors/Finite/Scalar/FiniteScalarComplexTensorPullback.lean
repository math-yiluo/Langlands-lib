/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalTensor

/-! # Typed complex tensor pullback comparisons

Source: Stacks Tags 00YV and 07A6.
(blueprint: def-sf-finite-scalar-complex-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

/-- Uncurry the signed-total comparison before specializing the coefficient categories.
Source: Stacks Tag 07A4, totalization of the ordinary tensor comparison.
(blueprint: def-sf-finite-scalar-complex-tensor-pullback). -/
@[irreducible] def finiteScalarComplexTensorPullbackForFunctor
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    (L : C ⥤ D) [L.Additive] [L.IsLeftAdjoint] [L.Monoidal] :
    finiteScalarRepresentativeTotalTensor C ⋙
        L.mapHomologicalComplex (.up ℤ) ⟶
      ((L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ))) ⋙
        finiteScalarRepresentativeTotalTensor D :=
  (finiteScalarUncurryPostcomposeIso
    ((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
    (L.mapHomologicalComplex (.up ℤ))).hom ≫
    uncurry.map (HomologicalComplex.mapBifunctorComparisonNatTrans
      (F := curriedTensor C) (F' := curriedTensor D) (G₁ := L) (G₂ := L) (G := L)
      (c₁ := .up ℤ) (c₂ := .up ℤ) (Functor.OplaxMonoidal.δNatTrans L) (.up ℤ))

/-- The uncurried total comparison retains the native complex component.
Source: the two published bifunctor-comparison component equations, Stacks Tag 07A4.
(blueprint: def-sf-finite-scalar-complex-tensor-pullback). -/
theorem finiteScalarComplexTensorPullbackForFunctor_app
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    (L : C ⥤ D) [L.Additive] [L.IsLeftAdjoint] [L.Monoidal] (P Q : CochainComplex C ℤ) :
    (finiteScalarComplexTensorPullbackForFunctor L).app (P, Q) =
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) L).app P).app Q := by
  simp only [finiteScalarComplexTensorPullbackForFunctor, NatTrans.comp_app,
    finiteScalarUncurryPostcomposeIso_hom_app, uncurry_map_app,
    HomologicalComplex.mapBifunctorComparisonNatTrans_app_app,
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app]
  exact CategoryTheory.Category.id_comp _

/-- Fix the coefficient-category data of the ordinary pullback tensor comparison.
Source: Stacks Tag 07A4, ordinary inverse image and tensor products.
(blueprint: def-sf-finite-scalar-complex-tensor-pullback). -/
@[irreducible] def finiteScalarFixedComplexTensorPullbackForCoefficients
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :=
  finiteScalarComplexTensorPullbackForFunctor (ProEtale.upperStar B p)

end WeilConjectures
