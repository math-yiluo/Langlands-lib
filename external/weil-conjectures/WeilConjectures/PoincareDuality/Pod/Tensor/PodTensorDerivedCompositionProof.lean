/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorDerivedComposition
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorChainComposition
import WeilConjectures.PoincareDuality.Pod.Reindex.PodReindexDerivedPasting
import WeilConjectures.PoincareDuality.Pod.Reindex.PodReindexDerivedFactors

/-! # Composition of normalized strict tensor tower maps

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-composition-tensor-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
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
  sfIntegralConstructible podReindexCalculus isoReductionCompletedMap
  integralOperationsTensorTowerFunctor
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Localization carries the strict Roos composition equation to the derived model maps.
Source: blueprint Steps 1 and 5; Stacks 015F, 07A4, 0941
(blueprint: lem-pod-tensor-derived-composition).
Proof: naturality of the exact derived-functor factor moves the first chain map
past the second factor. Compatibility of the compositor with those factors then
reduces the desired identity to the localization of the assumed chain equation.
Functoriality of localization finishes. No tensor Model law is used here. -/
theorem podTensorDerivedComposition
    (A : PodReindexFamily l E)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [(isoReductionIntegralInverse l E f).Additive]
    [PreservesFiniteLimits (isoReductionIntegralInverse l E f)]
    [PreservesFiniteColimits (isoReductionIntegralInverse l E f)]
    [(isoReductionIntegralInverse l E h).Additive]
    [PreservesFiniteLimits (isoReductionIntegralInverse l E h)]
    [PreservesFiniteColimits (isoReductionIntegralInverse l E h)]
    [(isoReductionIntegralInverse l E (h ≫ f)).Additive]
    [PreservesFiniteLimits (isoReductionIntegralInverse l E (h ≫ f))]
    [PreservesFiniteColimits (isoReductionIntegralInverse l E (h ≫ f))]
    (P Q : (integralOperationsGoodComplex l E V).FullSubcategory)
    (hc : PodTensorChainComposition l E A h f P Q) :
    PodTensorDerivedComposition l E A h f P Q := by
  unfold PodTensorDerivedComposition
  intro α FP FQ
  exact podReindexDerivedPastingMaps
    (isoReductionIntegralInverse l E f) (isoReductionIntegralInverse l E h)
    (isoReductionIntegralInverse l E (h ≫ f)) (A.composition h f)
    (integralOperationsRoosFunctor.obj
      ((integralOperationsTensorTowerFunctor l E V).obj (P.obj, Q.obj)))
    (podTensorReindexChain l E f (A.completion f) (A.tensor f) P Q)
    (podTensorReindexChain l E h (A.completion h) (A.tensor h) FP FQ)
    (podTensorReindexChain l E (h ≫ f) (A.completion (h ≫ f)) (A.tensor (h ≫ f)) P Q)
    (integralOperationsRoosFunctor.map
      ((integralOperationsTensorTowerFunctor l E Z).map
        (Prod.mkHom (α.hom.app P.obj) (α.hom.app Q.obj))))
    (podTensorReindexDerived l E f (A.completion f) (A.tensor f) P Q)
    (podTensorReindexDerived l E h (A.completion h) (A.tensor h) FP FQ)
    (podTensorReindexDerived l E (h ≫ f) (A.completion (h ≫ f))
      (A.tensor (h ≫ f)) P Q)
    (podTensorReindexDerivedData l E f (A.completion f) (A.tensor f) P Q).property
    (podTensorReindexDerivedData l E h (A.completion h) (A.tensor h) FP FQ).property
    (podTensorReindexDerivedData l E (h ≫ f) (A.completion (h ≫ f))
      (A.tensor (h ≫ f)) P Q).property
    (podReindexDerivedFactors l E A h f _) hc
end WeilConjectures
