/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorTowerComposition
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorChainComposition
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorChainCompositionRaw

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

private theorem roos_equation_congr
    {C D T : Type*} [Category C] [Category D] [Category T]
    (G : C ⥤ D) (R : T ⥤ D)
    {A B : C} {A' : D} {t₃ t₄ : T}
    (a : A' ⟶ G.obj A) {cf cf' : A ⟶ B} {cg cg' : G.obj B ⟶ R.obj t₃}
    {cc cc' : A' ⟶ R.obj t₄} (u : t₄ ⟶ t₃)
    (hf : cf = cf') (hg : cg = cg') (hc : cc = cc')
    (h : PodRoosCompositionEquation G R a cf' cg' cc' u) :
    PodRoosCompositionEquation G R a cf cg cc u := by
  rw [hf, hg, hc]
  exact h

-- Check the three specified coefficient transports together.
/-- Realizing the strict tensor-tower composition square gives the full Roos square.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-tensor-chain-composition).
Proof: apply normalized Roos composition for arbitrary compatible strict towers
with the three prescribed tensor tower maps. The assumed tower equation supplies
the compatibility hypothesis. The resulting maps are precisely the explicitly
constructed tensor Roos maps. Both cone coordinates were retained in the general
Roos composition theorem. No localization or derived tensor map occurs. -/
theorem podTensorChainComposition
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
    PodTensorChainComposition l E A h f P Q := by
  unfold PodTensorChainComposition
  intro α FP FQ
  have hr := podTensorChainCompositionRaw l E A h f hf hh hhf P Q ht
  unfold PodTensorRawComposition at hr
  have hcf := (podTensorReindexChainData l E f (A.completion f) (A.tensor f) P Q).property
  have hcg := (podTensorReindexChainData l E h (A.completion h) (A.tensor h) FP FQ).property
  have hcc := (podTensorReindexChainData l E (h ≫ f)
    (A.completion (h ≫ f)) (A.tensor (h ≫ f)) P Q).property
  change podTensorReindexChain l E f (A.completion f) (A.tensor f) P Q = _ at hcf
  change podTensorReindexChain l E h (A.completion h) (A.tensor h) FP FQ = _ at hcg
  change podTensorReindexChain l E (h ≫ f) (A.completion (h ≫ f))
    (A.tensor (h ≫ f)) P Q = _ at hcc
  exact roos_equation_congr (isoReductionIntegralComplex l E h)
    integralOperationsRoosFunctor _ _ hcf hcg hcc hr

end WeilConjectures
