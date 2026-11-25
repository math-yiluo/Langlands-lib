/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorDerivedComposition
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorGoodComposition
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorCompositionOfModels
import WeilConjectures.PoincareDuality.Pod.Reindex.PodReindexDerivedFactors
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorReindexPointModel
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

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

section TensorModelSpecialization
-- These proofs use only functoriality and never the underlying section construction.
attribute [local irreducible] isoSectionwiseModuleInverseImage

-- Keep the three coefficient reindexings together while checking the model squares.
/-- Tensor composition on good representatives follows from the localized Roos equation.
Source: blueprint Steps 1 and 5; Stacks 015F, 07A4, 0941
(blueprint: lem-pod-tensor-composition-on-good).
Proof: apply the three Model squares. Transport constructibility across the
factor isomorphisms to apply the intermediate tensor Naturality law. Naturality
of the representative tensor comparison supplies the final square, while
compatibility of the exact derived-functor factors supplies the two input squares.
The assumed localized Roos equation supplies the output square. Cancel the
invertible comparison at the output; the resulting equation is the tensor
composition equation on these two good representatives. -/
theorem podTensorCompositionOnGood
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
    (htf : PodCompletedTensorReindex.Laws l E f (A.completion f) (A.tensor f))
    (hth : PodCompletedTensorReindex.Laws l E h (A.completion h) (A.tensor h))
    (hthf : PodCompletedTensorReindex.Laws l E (h ≫ f)
      (A.completion (h ≫ f)) (A.tensor (h ≫ f)))
    (P Q : (integralOperationsGoodComplex l E V).FullSubcategory)
    (hP : sfIntegralConstructible l E V (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E V (DerivedCategory.Q.obj Q.obj))
    (hderived : PodTensorDerivedComposition l E A h f P Q) :
    PodTensorGoodComposition l E A h f P Q hP hQ := by
  unfold PodTensorGoodComposition
  intro M N
  let F := podOrdinaryReindex l E f
  let G := podOrdinaryReindex l E h
  let H := podOrdinaryReindex l E (h ≫ f)
  let B₀ := integralCompletedTensor l E V
  let B₁ := integralCompletedTensor l E W
  let B₂ := integralCompletedTensor l E Z
  let K₀ := integralOperationsTensorComplexFunctor l E V
  let K₁ := integralOperationsTensorComplexFunctor l E W
  let K₂ := integralOperationsTensorComplexFunctor l E Z
  let β₀ := integralCompletedTensorComparison l E V
  let β₁ := integralCompletedTensorComparison l E W
  let β₂ := integralCompletedTensorComparison l E Z
  let κ := A.compositionDerived l E h f
  let α := NatIso.mapHomologicalComplex (A.composition h f) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
    (Iso.refl (isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h))
    (.up ℤ)).symm
  let FP := (podGoodReindex l E f (A.completion f)).obj P
  let FQ := (podGoodReindex l E f (A.completion f)).obj Q
  let GP := (podGoodReindex l E h (A.completion h)).obj FP
  let GQ := (podGoodReindex l E h (A.completion h)).obj FQ
  let HP := (podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj P
  let HQ := (podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj Q
  let p : HP ⟶ GP := ObjectProperty.homMk (α.hom.app P.obj)
  let q : HQ ⟶ GQ := ObjectProperty.homMk (α.hom.app Q.obj)
  let e₀ : B₀.obj (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ⟶
      DerivedCategory.Q.obj (K₀.obj (P.obj, Q.obj)) := β₀.hom.app (P, Q)
  let eF : B₁.obj (DerivedCategory.Q.obj FP.obj, DerivedCategory.Q.obj FQ.obj) ⟶
      DerivedCategory.Q.obj (K₁.obj (FP.obj, FQ.obj)) := β₁.hom.app (FP, FQ)
  let eG : B₂.obj (DerivedCategory.Q.obj GP.obj, DerivedCategory.Q.obj GQ.obj) ⟶
      DerivedCategory.Q.obj (K₂.obj (GP.obj, GQ.obj)) := β₂.hom.app (GP, GQ)
  let eH : B₂.obj (DerivedCategory.Q.obj HP.obj, DerivedCategory.Q.obj HQ.obj) ⟶
      DerivedCategory.Q.obj (K₂.obj (HP.obj, HQ.obj)) := β₂.hom.app (HP, HQ)
  have : IsIso eG := by dsimp only [eG]; infer_instance
  let fP : F.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj FP.obj :=
    (isoReductionIntegralInverse l E f).mapDerivedCategoryFactors.app P.obj
  let fQ : F.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj FQ.obj :=
    (isoReductionIntegralInverse l E f).mapDerivedCategoryFactors.app Q.obj
  let gP : G.obj (DerivedCategory.Q.obj FP.obj) ≅ DerivedCategory.Q.obj GP.obj :=
    (isoReductionIntegralInverse l E h).mapDerivedCategoryFactors.app FP.obj
  let gQ : G.obj (DerivedCategory.Q.obj FQ.obj) ≅ DerivedCategory.Q.obj GQ.obj :=
    (isoReductionIntegralInverse l E h).mapDerivedCategoryFactors.app FQ.obj
  let cP : H.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj HP.obj :=
    (isoReductionIntegralInverse l E (h ≫ f)).mapDerivedCategoryFactors.app P.obj
  let cQ : H.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj HQ.obj :=
    (isoReductionIntegralInverse l E (h ≫ f)).mapDerivedCategoryFactors.app Q.obj
  let : (sfIntegralConstructible l E W).IsClosedUnderIsomorphisms :=
    sfIntegralConstructible_isClosedUnderIsomorphisms l E W
  let MF : sfIntegralConstructibleCategory l E W :=
    ⟨_, (sfIntegralConstructible l E W).prop_of_iso fP
      ((A.constructible l E f).obj M).property⟩
  let NF : sfIntegralConstructibleCategory l E W :=
    ⟨_, (sfIntegralConstructible l E W).prop_of_iso fQ
      ((A.constructible l E f).obj N).property⟩
  let r : (A.constructible l E f).obj M ⟶ MF := ObjectProperty.homMk fP.hom
  let s : (A.constructible l E f).obj N ⟶ NF := ObjectProperty.homMk fQ.hom
  let df := podTensorReindexDerived l E f (A.completion f) (A.tensor f) P Q
  let dg := podTensorReindexDerived l E h (A.completion h) (A.tensor h) FP FQ
  let dc := podTensorReindexDerived l E (h ≫ f) (A.completion (h ≫ f))
    (A.tensor (h ≫ f)) P Q
  have hmodelF := podTensorReindexDerived_model l E f (A.completion f)
    (A.tensor f) htf.2.2.2.2.1 P Q hP hQ
  have hmodelG := podTensorReindexDerived_model l E h (A.completion h)
    (A.tensor h) hth.2.2.2.2.1 FP FQ MF.property NF.property
  have hmodelH := podTensorReindexDerived_model l E (h ≫ f) (A.completion (h ≫ f))
    (A.tensor (h ≫ f)) hthf.2.2.2.2.1 P Q hP hQ
  have hn := hth.2.2.2.1 ((A.constructible l E f).obj M)
    ((A.constructible l E f).obj N) MF NF r s
  have hβ := β₂.hom.naturality (Prod.mkHom p q)
  have hm := podReindexDerivedFactors l E A h f P.obj
  have hq := podReindexDerivedFactors l E A h f Q.obj
  have hk := hderived
  exact podTensorCompositionOfModels F G H κ B₀ B₁ B₂
    e₀ eF eG eH
    fP fQ gP gQ cP cQ df dg dc
    (DerivedCategory.Q.map p.hom) (DerivedCategory.Q.map q.hom)
    (DerivedCategory.Q.map (K₂.map (Prod.mkHom p.hom q.hom)))
    ((A.tensor f).tensor M N).hom
    ((A.tensor h).tensor ((A.constructible l E f).obj M)
      ((A.constructible l E f).obj N)).hom
    ((A.tensor h).tensor MF NF).hom ((A.tensor (h ≫ f)).tensor M N).hom
    hmodelF hmodelG hmodelH hn hβ hm hq hk

end TensorModelSpecialization

end WeilConjectures
