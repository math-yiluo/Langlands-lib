/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorDerivedComposition

/-! # Tensor composition from localized Roos models

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4, 0941. -/

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
  sfIntegralConstructible podReindexCalculus integralOperationsTensorTowerFunctor
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor
  integralOperationsTensorOnGood integralOperationsGoodLocalization
  PodReindexFamily.constructible podOrdinaryReindex integralOperationsRoosFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The completed tensor composition equation on fixed good representatives.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: def-pod-tensor-good-composition).
This names the exact equation on the localizations of the supplied complexes. -/
def PodTensorGoodComposition
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
    (hP : sfIntegralConstructible l E V (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E V (DerivedCategory.Q.obj Q.obj))
    : Prop :=
    let M : sfIntegralConstructibleCategory l E V := ⟨_, hP⟩
    let N : sfIntegralConstructibleCategory l E V := ⟨_, hQ⟩
    (A.compositionDerived l E h f).hom.app
        ((integralCompletedTensor l E V).obj (M.obj, N.obj)) ≫
      (podOrdinaryReindex l E h).map ((A.tensor f).tensor M N).hom ≫
      ((A.tensor h).tensor ((A.constructible l E f).obj M)
        ((A.constructible l E f).obj N)).hom =
    ((A.tensor (h ≫ f)).tensor M N).hom ≫ (integralCompletedTensor l E Z).map
      (Prod.mkHom ((A.compositionDerived l E h f).hom.app M.obj)
        ((A.compositionDerived l E h f).hom.app N.obj))

end WeilConjectures
