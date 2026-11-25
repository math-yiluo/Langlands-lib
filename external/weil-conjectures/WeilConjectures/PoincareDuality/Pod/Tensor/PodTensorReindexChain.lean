/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence

/-! # Explicit tensor Roos chain maps and their localizations

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4, 0941. -/

@[expose] public noncomputable section
set_option autoImplicit false
-- Preserve sharing of the dependent functor and representative aliases.
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCompletedTensor
  completedIntegralCoefficientSheafUnrestricted Scheme.residueField
  sfIntegralConstructible podReindexCalculus integralOperationsTensorTowerFunctor
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor
  integralOperationsTensorOnGood integralOperationsGoodLocalization
  PodReindexFamily.constructible podOrdinaryReindex integralOperationsRoosFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section TensorModelSpecialization
-- These proofs use only functoriality and never the underlying section construction.
attribute [local irreducible] isoSectionwiseModuleInverseImage

/-- The explicit Roos chain map underlying one completed tensor reindexing.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: def-pod-tensor-reindex-chain).
The chain map is the specified reindexing comparison followed by the Roos image
of the specified strict tensor-tower map.
A named record for the explicit chain map and its defining equation.
Keeping these fields in a structure shares their dependent types during checking. -/
structure PodTensorReindexChainDatum
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [(isoReductionIntegralInverse l E g).Additive]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) where
  val : (isoReductionIntegralComplex l E g).obj
        (integralOperationsRoosFunctor.obj
          ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))) ⟶
      integralOperationsRoosFunctor.obj ((integralOperationsTensorTowerFunctor l E X).obj
        (((podGoodReindex l E g D).obj P).obj, ((podGoodReindex l E g D).obj Q).obj))
  property : val = (D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).hom ≫
    integralOperationsRoosFunctor.map (T.tower P Q).hom

/-- The explicit datum described by `PodTensorReindexChainDatum`.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: def-pod-tensor-reindex-chain). -/
@[irreducible] def podTensorReindexChainData
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [(isoReductionIntegralInverse l E g).Additive]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    PodTensorReindexChainDatum l E g D T P Q :=
  ⟨(D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).hom ≫
    integralOperationsRoosFunctor.map (T.tower P Q).hom, rfl⟩

/-- The map field of the explicitly constructed reindexing datum. -/
abbrev podTensorReindexChain
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [(isoReductionIntegralInverse l E g).Additive]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :=
  (podTensorReindexChainData l E g D T P Q).val

end TensorModelSpecialization
end WeilConjectures
