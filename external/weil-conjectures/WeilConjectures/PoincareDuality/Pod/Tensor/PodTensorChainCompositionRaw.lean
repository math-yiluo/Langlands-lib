/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorTowerComposition
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRawComposition
import WeilConjectures.PoincareDuality.Pod.Reindex.PodReindexRoosPasting

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

attribute [local irreducible] isoSectionwiseModuleInverseImage
attribute [local irreducible] HasDerivedCategory.standard integralCompletedTensor
  completedIntegralCoefficientSheafUnrestricted Scheme.residueField
  sfIntegralConstructible podReindexCalculus isoReductionCompletedMap
  integralOperationsTensorTowerFunctor
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Realizing the strict tensor-tower composition square gives the full Roos square.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-tensor-chain-composition-raw).
Proof: apply normalized Roos composition for arbitrary compatible strict towers
with the three prescribed tensor tower maps. The assumed tower equation supplies
the compatibility hypothesis. The resulting maps are precisely the explicitly
constructed tensor Roos maps. Both cone coordinates were retained in the general
Roos composition theorem. No localization or derived tensor map occurs. -/
theorem podTensorChainCompositionRaw
    (A : PodReindexFamily l E)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [(isoReductionIntegralInverse l E f).Additive]
    [(isoReductionIntegralInverse l E h).Additive]
    [(isoReductionIntegralInverse l E (h ≫ f)).Additive]
    (hf : PodCompletionReindex.Laws l E f (A.completion f))
    (hh : PodCompletionReindex.Laws l E h (A.completion h))
    (hhf : PodCompletionReindex.Laws l E (h ≫ f) (A.completion (h ≫ f)))
    (P Q : (integralOperationsGoodComplex l E V).FullSubcategory)
    (ht : PodTensorTowerComposition l E A h f P Q) :
    PodTensorRawComposition l E A h f P Q := by
  unfold PodTensorRawComposition
  intro α FP FQ CY CW
  let K := (integralOperationsTensorTowerFunctor l E Z).obj
    (((podGoodReindex l E h (A.completion h)).obj FP).obj,
      ((podGoodReindex l E h (A.completion h)).obj FQ).obj)
  let L := (integralOperationsTensorTowerFunctor l E Z).obj
    (((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj P).obj,
      ((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj Q).obj)
  exact podReindexRoosPasting l E A h f hf hh hhf CY CW
    (K := K) (L := L)
    ((A.tensor f).tower P Q).hom ((A.tensor h).tower FP FQ).hom
    ((A.tensor (h ≫ f)).tower P Q).hom
    ((integralOperationsTensorTowerFunctor l E Z).map
      (Prod.mkHom (α.hom.app P.obj) (α.hom.app Q.obj))) ht
end WeilConjectures
