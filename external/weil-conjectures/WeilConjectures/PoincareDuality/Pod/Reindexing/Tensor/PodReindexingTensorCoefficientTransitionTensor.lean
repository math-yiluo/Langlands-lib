/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexCoefficientTransition.PodReindexingTensorCoefficientTransitionCore
import WeilConjectures.CategoryTheory.SmoothPurity.FunctorSquareTowerDescent
import all WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionDescentData
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionReindexNormalizationDiagram
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionScalarNormalizationDiagram
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionMixedNormalizationDiagram
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionRepresentativeSquareDiagram
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionChainSquareDiagram

/-! # Completed tensor square for scalar/reindexing transitions

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] podTensorReindexAdditive podTensorScalarZero podTensorMixedLeftZero
  podTensorMixedRightZero
  podTensorReindexLimits podTensorReindexColimits
attribute [local irreducible] integralCompletedTensor integralOrdinaryScalar
  integralOperationsTensorTowerFunctor scalarTensorChain scalarTensorOrdinary
  integralOperationsRoos completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor SheafOfModules.monoidalCategory
attribute [local implicit_reducible] podOrdinaryReindex podGoodReindex
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor integralOperationsTensorOnGood
  scalarReductionSourceDerived integralTowerHasDerivedCategory
  integralOperationsCommHasDerivedCategory
  podTensorScalarGoodFunctor podTensorScalarGoodComparison podTensorReindexGoodComparison
  podTensorGoodConstructibleLocalization
  podTensorGoodConstructible podTensorMixedTensorIso podTensorGoodCoefficientTransition
  podTensorTensorReindexDerivedChain
  podTensorTensorScalarDerivedChain podTensorTensorMixedDerivedChain

attribute [local implicit_reducible]
  podTensorDiagramInputInclusion
  podTensorDiagramReindexFunctor
  podTensorDiagramScalarFunctor
  podTensorDiagramMixedFunctor
  podTensorDiagramSourceLocalization
  podTensorDiagramReindexLocalization
  podTensorDiagramTargetLocalization
  podTensorDiagramGoodInclusion
  podTensorDiagramGoodReindex
  podTensorDiagramGoodScalar
  podTensorDiagramGoodMixed
  podTensorDiagramGoodTransition
  podTensorDiagramPairReindex
  podTensorDiagramPairScalar
  podTensorDiagramPairMixed
  podTensorDiagramDerivedTransition
  podTensorDiagramPairTransition
  podTensorDiagramSourceTensor
  podTensorDiagramReindexTensor
  podTensorDiagramTargetTensor
  podTensorDiagramSourceRepresentative
  podTensorDiagramReindexRepresentative
  podTensorDiagramTargetRepresentative
  podTensorDiagramSourceComparison
  podTensorDiagramReindexComparison
  podTensorDiagramTargetComparison
  podTensorDiagramReindexFactor
  podTensorDiagramPairReindexFactor
  podTensorDiagramScalarFactor
  podTensorDiagramPairScalarFactor
  podTensorDiagramMixedFactor
  podTensorDiagramPairMixedFactor
  podTensorDiagramReindexChain
  podTensorDiagramScalarChain
  podTensorDiagramMixedChain
  podTensorDiagramReindexComparisonIso
  podTensorDiagramScalarComparisonIso
  podTensorDiagramMixedComparisonIso

private theorem associatorComponent
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : A) {Z : D}
    (f : (F ⋙ G ⋙ H).obj K ⟶ Z) :
    (Functor.associator F G H).hom.app K ≫ f = f := by
  exact Category.id_comp f

/-- The normalized completed tensor square of a coefficient transition.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-tensor).

Proof: on simultaneous flat quotient resolutions, both routes send every
homogeneous pure tensor to the same scalar tensor by balanced associativity.
The formula commutes with quotient transitions and with the signed total
differential.  Applying the full Roos realization and the normalized tensor
comparisons gives the displayed derived equality for all constructible inputs.
-/
theorem podReindexingTensorCoefficientTransition_tensor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S) :
    ∀ M N : sfIntegralConstructibleCategory l E Y,
      (integralOrdinaryDerivedScalar l E L ι X).map (T.tensor M N).hom ≫
        (scalarTensorOrdinary l E L ι X).hom.app
          ((podOrdinaryReindex l E g).obj M.obj, (podOrdinaryReindex l E g).obj N.obj) ≫
        (integralCompletedTensor l L X).map
          (Prod.mkHom ((S.derived l E L ι g D D').hom.app M.obj)
            ((S.derived l E L ι g D D').hom.app N.obj)) =
      (S.derived l E L ι g D D').hom.app
          ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
        (podOrdinaryReindex l L g).map
          ((scalarTensorOrdinary l E L ι Y).hom.app (M.obj, N.obj)) ≫
        (T'.tensor ⟨_, S.sourceConstructible M⟩ ⟨_, S.sourceConstructible N⟩).hom := by
  let I := podTensorDiagramInputInclusion l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let F := podTensorDiagramReindexFunctor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let G := podTensorDiagramScalarFunctor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let H := podTensorDiagramMixedFunctor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let q₀ := podTensorDiagramSourceLocalization l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let q₁ := podTensorDiagramReindexLocalization l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let q₂ := podTensorDiagramTargetLocalization l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let J := podTensorDiagramGoodInclusion l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let k := podTensorDiagramGoodReindex l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let h := podTensorDiagramGoodScalar l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let m := podTensorDiagramGoodMixed l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let κ := podTensorDiagramGoodTransition l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let A := podTensorDiagramPairReindex l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let B := podTensorDiagramPairScalar l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let C := podTensorDiagramPairMixed l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let b := podTensorDiagramDerivedTransition l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let a := podTensorDiagramPairTransition l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let U₀ := podTensorDiagramSourceTensor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let U₁ := podTensorDiagramReindexTensor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let U₂ := podTensorDiagramTargetTensor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let t₀ := podTensorDiagramSourceRepresentative l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let t₁ := podTensorDiagramReindexRepresentative l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let t₂ := podTensorDiagramTargetRepresentative l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let r₀ := podTensorDiagramSourceComparison l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let r₁ := podTensorDiagramReindexComparison l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let r₂ := podTensorDiagramTargetComparison l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let η₀ := podTensorDiagramReindexFactor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let η := podTensorDiagramPairReindexFactor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let θ₀ := podTensorDiagramScalarFactor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let θ := podTensorDiagramPairScalarFactor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let ζ₀ := podTensorDiagramMixedFactor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let ζ := podTensorDiagramPairMixedFactor l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let c := podTensorDiagramReindexChain l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let d := podTensorDiagramScalarChain l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let e := podTensorDiagramMixedChain l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let α := podTensorDiagramReindexComparisonIso l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let β := podTensorDiagramScalarComparisonIso l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let γ := podTensorDiagramMixedComparisonIso l E g D hD T hT L ι D' hD' T' hT' S _hcore
  let : q₀.EssSurj := goodConstructibleLocalization_essSurj l E Y
  let : (q₀.prod q₀).EssSurj := ⟨fun M ↦
    ⟨(q₀.objPreimage M.1, q₀.objPreimage M.2),
      ⟨(q₀.objObjPreimageIso M.1).prod (q₀.objObjPreimageIso M.2)⟩⟩⟩
  have hd := functorSquareTowerDescent (q₀.prod q₀) (q₁.prod q₁) (q₂.prod q₂)
    (k.prod k) (h.prod h) (m.prod m) (NatIso.prod κ κ)
    A B C a F G H b U₀ U₁ U₂ t₀ t₁ t₂ r₀ r₁ r₂ η θ ζ c d e α β γ
    (faithfulRestriction (q₀.prod q₀))
    (podTensorReindexRepresentativeNormalizationDiagram l E g D hD T hT L ι D' hD' T' hT' S _hcore)
    (podTensorScalarRepresentativeNormalizationDiagram l E g D hD T hT L ι D' hD' T' hT' S _hcore)
    (podTensorMixedRepresentativeNormalizationDiagram l E g D hD T hT L ι D' hD' T' hT' S _hcore)
    (podTensorCoefficientRepresentativeSquareDiagram l E g D hD T hT L ι D' hD' T' hT' S _hcore)
    (podTensorMixedRepresentativeChainSquareDiagram l E g D hD T hT L ι D' hD' T' hT' S _hcore)
  intro M N
  have hz := hd (M, N)
  dsimp only [α, γ, podTensorDiagramInputInclusion, podTensorDiagramReindexFunctor,
    podTensorDiagramScalarFunctor, podTensorDiagramMixedFunctor,
      podTensorDiagramSourceLocalization, podTensorDiagramReindexLocalization,
        podTensorDiagramTargetLocalization, podTensorDiagramGoodInclusion,
          podTensorDiagramGoodReindex, podTensorDiagramGoodScalar, podTensorDiagramGoodMixed,
            podTensorDiagramGoodTransition, podTensorDiagramPairReindex,
              podTensorDiagramPairScalar, podTensorDiagramPairMixed,
                podTensorDiagramDerivedTransition, podTensorDiagramPairTransition,
                  podTensorDiagramSourceTensor, podTensorDiagramReindexTensor,
                    podTensorDiagramTargetTensor, podTensorDiagramSourceRepresentative,
                      podTensorDiagramReindexRepresentative, podTensorDiagramTargetRepresentative,
                        podTensorDiagramSourceComparison, podTensorDiagramReindexComparison,
                          podTensorDiagramTargetComparison, podTensorDiagramReindexFactor,
                            podTensorDiagramPairReindexFactor, podTensorDiagramScalarFactor,
                              podTensorDiagramPairScalarFactor, podTensorDiagramMixedFactor,
                                podTensorDiagramPairMixedFactor, podTensorDiagramReindexChain,
                                  podTensorDiagramScalarChain, podTensorDiagramMixedChain,
                                    podTensorDiagramReindexComparisonIso,
                                      podTensorDiagramScalarComparisonIso,
                                        podTensorDiagramMixedComparisonIso, Iso.trans_hom,
                                          NatTrans.comp_app] at hz
  simp only [associatorComponent] at hz
  dsimp only [podTensorTensorReindexIso, podTensorMixedTensorIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hz
  dsimp only [F, G, H, I, U₀, U₁, U₂, A, B, C, a, b, β, NatIso.prod_hom,
    NatTrans.prod, isoWhiskerLeft_hom, whiskerLeft_app, Functor.prod_obj,
    Functor.comp_obj, ObjectProperty.ι_obj, podTensorDiagramInputInclusion,
      podTensorDiagramReindexFunctor, podTensorDiagramScalarFunctor, podTensorDiagramMixedFunctor,
        podTensorDiagramSourceLocalization, podTensorDiagramReindexLocalization,
          podTensorDiagramTargetLocalization, podTensorDiagramGoodInclusion,
            podTensorDiagramGoodReindex, podTensorDiagramGoodScalar, podTensorDiagramGoodMixed,
              podTensorDiagramGoodTransition, podTensorDiagramPairReindex,
                podTensorDiagramPairScalar, podTensorDiagramPairMixed,
                  podTensorDiagramDerivedTransition, podTensorDiagramPairTransition,
                    podTensorDiagramSourceTensor, podTensorDiagramReindexTensor,
                      podTensorDiagramTargetTensor, podTensorDiagramSourceRepresentative,
                        podTensorDiagramReindexRepresentative,
                          podTensorDiagramTargetRepresentative, podTensorDiagramSourceComparison,
                            podTensorDiagramReindexComparison, podTensorDiagramTargetComparison,
                              podTensorDiagramReindexFactor, podTensorDiagramPairReindexFactor,
                                podTensorDiagramScalarFactor, podTensorDiagramPairScalarFactor,
                                  podTensorDiagramMixedFactor, podTensorDiagramPairMixedFactor,
                                    podTensorDiagramReindexChain, podTensorDiagramScalarChain,
                                      podTensorDiagramMixedChain,
                                        podTensorDiagramReindexComparisonIso,
                                          podTensorDiagramScalarComparisonIso,
                                            podTensorDiagramMixedComparisonIso] at hz
  simpa only [Category.assoc] using hz

end WeilConjectures
