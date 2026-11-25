/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel
public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # Ordinary tensor and quotient augmentation data

Source: Bhatt--Scholze 3.4.10, 6.5.5; Stacks 06YY, 07A4, 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open Opposite CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenFactorCoherence.TensorCompletionConstruction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
open IntegralAmbient
attribute [local implicit_reducible] PurCompactSupport.completed

/-- Flat-term K-flat representatives are good integral representatives.
Source: Stacks 06YY (blueprint: def-sf-tensor-quotient-chain-data). -/
theorem flat_good (P : Cx l E X)
    (hP : proEtaleFlatRepresentatives X ((PurCompactSupport.completed l E).ring X) P) :
    integralOperationsGoodComplex l E X P :=
  ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1, hP.2⟩

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- The recorded ordinary tensor restricted to flat-term K-flat representatives.
Source: Stacks 07A4 (blueprint: def-sf-tensor-quotient-chain-data). -/
@[irreducible] def ordinaryModel :
    ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X) where
  tensor := by with_unfolding_all exact ambientOrdinaryTensor l E X
  representative := by
    let i : (proEtaleFlatRepresentatives X
        ((PurCompactSupport.completed l E).ring X)).FullSubcategory ⥤
        ObjectProperty.FullSubcategory
          (CochainComplex.IsKFlatIndependentCoefficients
            (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) :
              ObjectProperty (Cx l E X)) :=
      ObjectProperty.ιOfLE (fun P hP ↦ (flat_good l E X P hP).1)
    with_unfolding_all
      exact Functor.isoWhiskerLeft (i.prod i) (ambientTensorModelComparison l E X)

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- Naturality of the quotient Roos augmentation.
Source: Stacks 0941 (blueprint: def-sf-tensor-quotient-chain-data). -/
theorem completionChain_naturality {P Q : Cx l E X} (f : P ⟶ Q) :
    f ≫ IntegralOnSlice.roosUnit.{u, u} l E X none Q =
      IntegralOnSlice.roosUnit.{u, u} l E X none P ≫
        (IntegralOnSlice.roos.{u, u} l E X none).map f :=
  IntegralOnSlice.sliceRoosUnit_natural.{u, u} l E X none f

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- The natural quotient Roos augmentation of a complex.
Source: Stacks 0941 (blueprint: def-sf-tensor-quotient-chain-data). -/
@[irreducible] def completionChain :
    𝟭 (Cx l E X) ⟶ IntegralOnSlice.roos.{u, u} l E X none where
  app P := IntegralOnSlice.roosUnit.{u, u} l E X none P
  naturality {_ _} f := completionChain_naturality l E X f

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- Whisker the quotient augmentation and transport it along a strict tower isomorphism.
Source: Stacks 0941 (blueprint: def-sf-tensor-quotient-chain-data). -/
@[irreducible] def augmentTensor
    (T : Cx l E X × Cx l E X ⥤ Cx l E X)
    (S : Cx l E X × Cx l E X ⥤ (ℕᵒᵖ ⥤ Cx l E X))
    (d : T ⋙ IntegralOnSlice.tower.{u, u} l E X none ≅ S) :
    T ⟶ S ⋙ integralOperationsRoosFunctor :=
  Functor.whiskerLeft T (completionChain l E X) ≫
    Functor.whiskerRight d.hom integralOperationsRoosFunctor

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- The tensor augmentation using the specified normalized strict tensor tower.
Source: Bhatt--Scholze 3.4.10 (blueprint: def-sf-tensor-quotient-chain-data). -/
@[irreducible] def quotientChain : constructibleTensorTotal l E X ⟶
    integralOperationsTensorComplexFunctor l E X :=
  augmentTensor l E X
    (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X))
    (integralOperationsTensorTowerFunctor l E X) (tensorTowerIso l E X)

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- Each component is the previously constructed tensor operation unit.
Source: Stacks 07A4, 0941 (blueprint: def-sf-tensor-quotient-chain-data). -/
theorem quotientChain_app (P Q : Cx l E X) :
    (quotientChain l E X).app (P, Q) = tensorOperationUnit l E X P Q := by
  unfold quotientChain augmentTensor completionChain tensorOperationUnit
  rfl

end WeilConjectures.OpenFactorCoherence.TensorCompletionConstruction
