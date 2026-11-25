/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorReindexPoint

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

/-- The tensor Model law in terms of the named localized Roos map.
Source: blueprint Steps 1 and 5; Stacks 07A4
(blueprint: lem-pod-tensor-reindex-derived-model).
Proof: unfold the two explicitly constructed chain and localized maps; the
assertion is exactly the supplied Model equation, retaining its heterogeneous
form so no coefficient or category structure has to be changed. -/
theorem podTensorReindexDerived_model
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [(isoReductionIntegralInverse l E g).Additive]
    [PreservesFiniteLimits (isoReductionIntegralInverse l E g)]
    [PreservesFiniteColimits (isoReductionIntegralInverse l E g)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (ht : PodCompletedTensorReindex.Model l E g D T)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)) :
    HEq ((podOrdinaryReindex l E g).map
        ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
        podTensorReindexDerived l E g D T P Q)
      ((T.tensor (⟨_, hP⟩ : sfIntegralConstructibleCategory l E Y)
        (⟨_, hQ⟩ : sfIntegralConstructibleCategory l E Y)).hom ≫
        (integralCompletedTensor l E X).map
          (Prod.mkHom ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj)
            ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
        (integralCompletedTensorComparison l E X).hom.app
          ((podGoodReindex l E g D).obj P, (podGoodReindex l E g D).obj Q)) := by
  unfold podTensorReindexDerived podTensorReindexDerivedData
    podTensorReindexChain podTensorReindexChainData
  exact ht P Q hP hQ

end TensorModelSpecialization
end WeilConjectures
