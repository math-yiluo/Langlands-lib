/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorDescentDiagram
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionMixedNormalization

/-! # Completed tensor square for scalar/reindexing transitions

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-tensor-mixed-normalization-diagram).
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

/-- The hγ compatibility for the named tensor descent diagram.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: lem-pod-tensor-mixed-normalization-diagram).
Proof: Apply the scalar normalization on the source. Scalar localization factors preserve
  constructibility. Apply the target-field tensor Model law, and use tensor naturality to move
    both scalar factors. Paste these three equalities and cancel the associator component. -/
theorem podTensorMixedRepresentativeNormalizationDiagram
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S) :
  ∀ P, (podTensorDiagramMixedFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).map
    ((podTensorDiagramSourceComparison l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).hom.app P) ≫
      (podTensorDiagramMixedChain l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore) P =
      (podTensorDiagramMixedComparisonIso l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).hom.app
        (((podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
          (podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S
        _hcore)).obj P)
            ≫ (podTensorDiagramTargetTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).map
              ((podTensorDiagramPairMixedFactor l E g D _hD T _hT L ι D' _hD' T' _hT' S
                _hcore).hom.app P) ≫
        (podTensorDiagramTargetComparison l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).hom.app
          (((podTensorDiagramGoodMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore).prod
            (podTensorDiagramGoodMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore)).obj P) := by
  let I := podTensorDiagramInputInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let F := podTensorDiagramReindexFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let G := podTensorDiagramScalarFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let H := podTensorDiagramMixedFunctor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let q₀ := podTensorDiagramSourceLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let q₁ := podTensorDiagramReindexLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let q₂ := podTensorDiagramTargetLocalization l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let J := podTensorDiagramGoodInclusion l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let k := podTensorDiagramGoodReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let h := podTensorDiagramGoodScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let m := podTensorDiagramGoodMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let κ := podTensorDiagramGoodTransition l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let A := podTensorDiagramPairReindex l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let B := podTensorDiagramPairScalar l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let C := podTensorDiagramPairMixed l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let b := podTensorDiagramDerivedTransition l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let a := podTensorDiagramPairTransition l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let U₀ := podTensorDiagramSourceTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let U₁ := podTensorDiagramReindexTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let U₂ := podTensorDiagramTargetTensor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let t₀ := podTensorDiagramSourceRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let t₁ := podTensorDiagramReindexRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let t₂ := podTensorDiagramTargetRepresentative l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let r₀ := podTensorDiagramSourceComparison l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let r₁ := podTensorDiagramReindexComparison l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let r₂ := podTensorDiagramTargetComparison l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let η₀ := podTensorDiagramReindexFactor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let η := podTensorDiagramPairReindexFactor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let θ₀ := podTensorDiagramScalarFactor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let θ := podTensorDiagramPairScalarFactor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let ζ₀ := podTensorDiagramMixedFactor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let ζ := podTensorDiagramPairMixedFactor l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let c := podTensorDiagramReindexChain l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let d := podTensorDiagramScalarChain l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let e := podTensorDiagramMixedChain l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let α := podTensorDiagramReindexComparisonIso l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let β := podTensorDiagramScalarComparisonIso l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  let γ := podTensorDiagramMixedComparisonIso l E g D _hD T _hT L ι D' _hD' T' _hT' S _hcore
  change ∀ P, H.map (r₀.hom.app P) ≫ e P =
      γ.hom.app ((q₀.prod q₀).obj P) ≫ U₂.map (ζ.hom.app P) ≫
        r₂.hom.app ((m.prod m).obj P)
  intro P
  have hh := podTensorMixedRepresentativeNormalization l E g D _hD T _hT L ι D' _hD' T' _hT' S
    _hcore
    P.1.obj P.2.obj P.1.property P.2.property
  dsimp only [γ, podTensorDiagramMixedComparisonIso, Iso.trans_hom,
    NatTrans.comp_app]
  simp only [associatorComponent]
  dsimp only [
    podTensorDiagramInputInclusion,
    podTensorDiagramReindexFunctor,
    podTensorDiagramScalarFunctor,
    podTensorDiagramMixedFunctor,
    podTensorDiagramSourceLocalization,
    podTensorDiagramReindexLocalization,
    podTensorDiagramTargetLocalization,
    podTensorDiagramGoodInclusion,
    podTensorDiagramGoodReindex,
    podTensorDiagramGoodScalar,
    podTensorDiagramGoodMixed,
    podTensorDiagramGoodTransition,
    podTensorDiagramPairReindex,
    podTensorDiagramPairScalar,
    podTensorDiagramPairMixed,
    podTensorDiagramDerivedTransition,
    podTensorDiagramPairTransition,
    podTensorDiagramSourceTensor,
    podTensorDiagramReindexTensor,
    podTensorDiagramTargetTensor,
    podTensorDiagramSourceRepresentative,
    podTensorDiagramReindexRepresentative,
    podTensorDiagramTargetRepresentative,
    podTensorDiagramSourceComparison,
    podTensorDiagramReindexComparison,
    podTensorDiagramTargetComparison,
    podTensorDiagramReindexFactor,
    podTensorDiagramPairReindexFactor,
    podTensorDiagramScalarFactor,
    podTensorDiagramPairScalarFactor,
    podTensorDiagramMixedFactor,
    podTensorDiagramPairMixedFactor,
    podTensorDiagramReindexChain,
    podTensorDiagramScalarChain,
    podTensorDiagramMixedChain,
    podTensorDiagramReindexComparisonIso,
    podTensorDiagramScalarComparisonIso,
    podTensorDiagramMixedComparisonIso,
    I,
    F,
    G,
    H,
    q₀,
    q₁,
    q₂,
    J,
    k,
    h,
    m,
    κ,
    A,
    B,
    C,
    b,
    a,
    U₀,
    U₁,
    U₂,
    t₀,
    t₁,
    t₂,
    r₀,
    r₁,
    r₂,
    η₀,
    η,
    θ₀,
    θ,
    ζ₀,
    ζ,
    c,
    d,
    e,
    α,
    β,
    γ,
    podTensorMixedTensorIso,
    podTensorTensorReindexIso,
    podTensorReindexGoodComparison,
    podTensorScalarGoodComparison,
    podTensorGoodConstructibleLocalization,
    integralOperationsGoodLocalization,
    Functor.comp_obj,
    Functor.comp_map,
    Functor.prod_obj,
    Functor.prod_map,
    NatIso.prod_hom,
    NatTrans.prod,
    isoWhiskerLeft_hom,
    isoWhiskerRight_hom,
    whiskerLeft_app,
    whiskerRight_app,
    NatIso.ofComponents_hom_app,
    Iso.trans_hom,
    NatTrans.comp_app,
    ObjectProperty.ι_obj,
    ObjectProperty.ι_map,
    ObjectProperty.isoMk_hom,
    ObjectProperty.lift,
    ObjectProperty.homMk_hom,
    CategoryTheory.prod_comp_fst,
    CategoryTheory.prod_comp_snd,
    Iso.app_hom,
    Functor.mapIso_hom]
  simpa only [prod_comp, Functor.comp_map, Category.assoc] using hh

end WeilConjectures
