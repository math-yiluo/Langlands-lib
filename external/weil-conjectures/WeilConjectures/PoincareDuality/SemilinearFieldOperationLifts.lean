/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.PoincareDuality.PullbackIdentitiesScalarExtension
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.DeligneLaumon.IsomorphismFieldTransport

/-! # Semilinear Frobenius transport and field-operation lifts

Source: blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, sentence 1; sec-six-functors/sk-rem-sf-pf-done,
lem-fix-weil-operations.proof.md, first paragraph
(blueprint: lem-pod-semilinear-field-operation-lifts).

The fixed-pair functors are the existing IsoAlgebra transports. The specifications
record their object, structure and arrow formulas. Partial internal Hom retains
its precise permitted-pair domain. Exactness refers to underlying derived functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry Opposite
open CategoryTheory.SuppliedExchangeProjection
open scoped TensorProduct
namespace WeilConjectures

/-- The tensor lift uses the existing product of fixed pairs and the existing
transport. Source: blueprint sec-Weil-complexes, proof sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodTensorWeilLiftSpec
    {C : Type a} [Category.{b} C] (P : C ⥤ C) (T : C × C ⥤ C)
    (μ : T ⋙ P ≅ P.prod P ⋙ T) : Prop :=
  (IsoAlgebra.prod ⋙ IsoAlgebra.mapOfNatIso μ) ⋙ IsoAlgebra.forget P =
    ((IsoAlgebra.forget P).prod (IsoAlgebra.forget P)) ⋙ T ∧
  (∀ K L : IsoAlgebra P,
    ((IsoAlgebra.prod ⋙ IsoAlgebra.mapOfNatIso μ).obj (K, L)).str =
      μ.app (K.carrier, L.carrier) ≪≫ T.mapIso (K.str.prod L.str)) ∧
  ∀ (K K' L L' : IsoAlgebra P) (u : K ⟶ K') (v : L ⟶ L'),
    ((IsoAlgebra.prod ⋙ IsoAlgebra.mapOfNatIso μ).map (Prod.mkHom u v)).hom.f =
      T.map (Prod.mkHom u.hom.f v.hom.f)

/-- Retain exactly the original partial internal-Hom domain on underlying objects.
Source: blueprint sec-Weil-complexes, proof sentence 1, internal-Hom qualification
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podWeilHomPairs {C : Type a} [Category.{b} C] (P : C ⥤ C)
    (J : ObjectProperty (Cᵒᵖ × C)) : ObjectProperty ((IsoAlgebra P)ᵒᵖ × IsoAlgebra P) :=
  fun KL ↦ J (op KL.1.unop.carrier, KL.2.carrier)

/-- Forget structures on a permitted pair, retaining its actual domain witness.
Source: blueprint sec-Weil-complexes, proof sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podWeilHomPairForget {C : Type a} [Category.{b} C] (P : C ⥤ C)
    (J : ObjectProperty (Cᵒᵖ × C)) :
    (podWeilHomPairs P J).FullSubcategory ⥤ J.FullSubcategory :=
  J.lift ((podWeilHomPairs P J).ι ⋙
    ((IsoAlgebra.forget P).op.prod (IsoAlgebra.forget P))) (fun KL ↦ KL.property)

/-- The Hom structure is H(theta_M inverse,theta_N) after the canonical comparison.
The functor is defined only on the original permitted pairs, and forgetting fixes
its entire object and arrow action. Source: blueprint sec-Weil-complexes, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodHomWeilLiftSpec
    {C : Type a} [Category.{b} C] (P : C ⥤ C) (J : ObjectProperty (Cᵒᵖ × C))
    (H : J.FullSubcategory ⥤ C)
    (hJ : ∀ K : J.FullSubcategory, J ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P J J hJ ⋙ H) : Prop :=
  ∃ L : (podWeilHomPairs P J).FullSubcategory ⥤ IsoAlgebra P,
    L ⋙ IsoAlgebra.forget P = podWeilHomPairForget P J ⋙ H ∧
    (∀ K : (podWeilHomPairs P J).FullSubcategory,
      HEq (L.obj K).str.hom
        (κ.hom.app ((podWeilHomPairForget P J).obj K) ≫
          H.map (X := (podPairPullback P J J hJ).obj
              ((podWeilHomPairForget P J).obj K))
            (Y := (podWeilHomPairForget P J).obj K)
            (ObjectProperty.homMk
              (Prod.mkHom K.obj.1.unop.str.inv.op K.obj.2.str.hom)))) ∧
    ∀ (K K' : (podWeilHomPairs P J).FullSubcategory) (u : K ⟶ K'),
      HEq (L.map u).hom.f (H.map ((podWeilHomPairForget P J).map u))

/-- The tensor and partial-Hom formulas define functors with the stipulated variances.
The input J can retain any already-proved finite-Tor or site-perfect restriction;
only its preservation by P is used, and no larger Hom domain is asserted.
Source: blueprint sec-Weil-complexes, sentence 1, node proof steps 7--9
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: tensor uses IsoAlgebra.prod followed by mapOfNatIso. Bifunctoriality,
the two arrow equations and naturality of mu give the tensor arrow equation.
For Hom, send a pair to the permitted underlying pair with structure
(theta_M inverse).op times theta_N; the arrow equation follows by multiplying
the first arrow equation by both inverses. Apply mapOfNatIso to kappa.
The output structure is kappa followed by H(theta_M inverse,theta_N).
Identities and composition are the bifunctor laws, including the reversed
first variable. Forgetting recovers the original tensor and partial Hom. -/
theorem pod_tensor_hom_field_operation_lifts
    {C : Type a} [Category.{b} C] (P : C ⥤ C) (T : C × C ⥤ C)
    (μ : T ⋙ P ≅ P.prod P ⋙ T) (J : ObjectProperty (Cᵒᵖ × C))
    (H : J.FullSubcategory ⥤ C)
    (hJ : ∀ K : J.FullSubcategory, J ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P J J hJ ⋙ H) :
    PodTensorWeilLiftSpec P T μ ∧ PodHomWeilLiftSpec P J H hJ κ := by
  constructor
  · refine ⟨rfl, ?_, fun _ _ _ _ _ _ ↦ rfl⟩
    intro K L
    simp only [Functor.comp_obj, IsoAlgebra.mapOfNatIso_obj_str,
      IsoAlgebra.prod_obj_carrier, IsoAlgebra.prod_obj_str]
  · let R : (IsoAlgebra P)ᵒᵖ × IsoAlgebra P ⥤ IsoAlgebra (P.op.prod P) :=
      (IsoAlgebra.opFunctor.prod (𝟭 (IsoAlgebra P))) ⋙ IsoAlgebra.prod
    let A : (podWeilHomPairs P J).FullSubcategory ⥤
        IsoAlgebra (podPairPullback P J J hJ) :=
      { obj := fun K ↦ IsoAlgebra.mk ((podWeilHomPairForget P J).obj K)
          (J.isoMk (R.obj K.obj).str)
        map := fun u ↦ ObjectProperty.homMk
          { f := (podWeilHomPairForget P J).map u
            h := by
              apply ObjectProperty.hom_ext J
              exact (R.map u.hom).hom.h } }
    refine ⟨A ⋙ IsoAlgebra.mapOfNatIso κ, rfl, ?_, ?_⟩
    · intro K
      rfl
    · intro K K' u
      rfl

section CompositionElaboration
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] commonStagePullbackComparison rationalDerivedPullback
  commonStageDerivedPullback Scheme.residueField

attribute [local irreducible] rationalDerivedInternalHom commonStageDerivedInternalHom

-- Retain the category wrappers used by the common-stage operation interface.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

attribute [local irreducible] sfIntegralConstructible Linear.homModule
  ObjectProperty.FullSubcategory.category
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

/-- The rational Frobenius square component through the canonical compositors.
Source: blueprint sec-Weil-complexes, sentence 1, proof step 4
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podRationalSquarePullbackComponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y) (h : gX ≫ f = f ≫ gY)
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E gX).obj ((rationalDerivedPullback l E f).obj K) ≅
      (rationalDerivedPullback l E f).obj ((rationalDerivedPullback l E gY).obj K) :=
  (pullbackTensorRationalComposition l E f gX K).symm ≪≫
    eqToIso (congrArg (fun m : X ⟶ Y ↦ (rationalDerivedPullback l E m).obj K) h) ≪≫
    pullbackTensorRationalComposition l E gY f K

/-- The same square component in the actual common-stage category, through the
canonical common-stage compositors. Source: blueprint sec-Weil-complexes, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podCommonSquarePullbackComponent
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y) (h : gX ≫ f = f ≫ gY)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω gX).obj ((commonStageDerivedPullback l Ω f).obj K) ≅
      (commonStageDerivedPullback l Ω f).obj ((commonStageDerivedPullback l Ω gY).obj K) :=
  (pullbackTensorCommonComposition l Ω f gX K).symm ≪≫
    eqToIso (congrArg (fun m : X ⟶ Y ↦ (commonStageDerivedPullback l Ω m).obj K) h) ≪≫
    pullbackTensorCommonComposition l Ω gY f K

private theorem pod_map_heq
    {C B : Type*} [Category* C] [Category* B] (F : C ⥤ B)
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

attribute [local irreducible] Preadditive.homGroup
  ScalarLocalization.category ScalarLocalization.linear

end CompositionElaboration

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]

/-- Integral and rational Frobenius transport, using the existing prime-invertibility
data, canonical inverse-image realization, and the actual inverse scheme map.
Source: blueprint sec-Weil-complexes, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodRationalFrobeniusTransportSpec
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl T₀ x
  (∃ ε : constructibleIntegralPullback l E (D.geometricFrobenius T₀).asIso.hom ⋙
      constructibleIntegralPullback l E (D.geometricFrobenius T₀).asIso.inv ≅ 𝟭 _,
    ∀ K : sfIntegralConstructibleCategory l E (D.geometricFiber T₀).left,
      HEq ((sfIntegralConstructible l E (D.geometricFiber T₀).left).ι.map (ε.hom.app K))
        (pullbackIdentityEpsilon l E (D.geometricFrobenius T₀).asIso.hom K).hom) ∧
  Nonempty (constructibleIntegralPullback l E (D.geometricFrobenius T₀).asIso.inv ⋙
    constructibleIntegralPullback l E (D.geometricFrobenius T₀).asIso.hom ≅ 𝟭 _) ∧
  (∃ h : ∀ K : DerivedCategory (scalarReductionSource l E (D.geometricFiber T₀).left),
      sfIntegralConstructible l E (D.geometricFiber T₀).left K →
        sfIntegralConstructible l E (D.geometricFiber T₀).left
          ((isomorphismIntegralTermwiseInverseImage l E
            (D.geometricFrobenius T₀).asIso.hom).obj K),
    Nonempty (constructibleIntegralPullback l E (D.geometricFrobenius T₀).asIso.hom ≅
      (sfIntegralConstructible l E (D.geometricFiber T₀).left).lift
        ((sfIntegralConstructible l E (D.geometricFiber T₀).left).ι ⋙
          isomorphismIntegralTermwiseInverseImage l E (D.geometricFrobenius T₀).asIso.hom)
        (fun K ↦ h K.obj K.property))) ∧
  (podCompletedModuleInverseImage l E (D.geometricFrobenius T₀).asIso.hom).Additive ∧
  PreservesFiniteLimits
    (podCompletedModuleInverseImage l E (D.geometricFrobenius T₀).asIso.hom) ∧
  PreservesFiniteColimits
    (podCompletedModuleInverseImage l E (D.geometricFrobenius T₀).asIso.hom) ∧
  (podCompletedModuleInverseImage l E (D.geometricFrobenius T₀).asIso.hom).IsEquivalence ∧
  (sfWeilFrobeniusPullback D l hl T₀ E).IsEquivalence ∧
  (∃ (δ : constructibleIntegralPullback l E (D.geometricFrobenius T₀).asIso.hom ⋙
        constructibleIntegralPullback l E (D.geometricFrobenius T₀).asIso.inv ≅ 𝟭 _)
      (ε : sfWeilFrobeniusPullback D l hl T₀ E ⋙
        rationalDerivedPullback l E (D.geometricFrobenius T₀).asIso.inv ≅ 𝟭 _),
    (∀ K, HEq ((sfIntegralConstructible l E (D.geometricFiber T₀).left).ι.map
        (δ.hom.app K)) (pullbackIdentityEpsilon l E (D.geometricFrobenius T₀).asIso.hom K).hom) ∧
    ∀ K : sfRationalConstructibleCategory l E (D.geometricFiber T₀).left,
      HEq (ε.hom.app K)
        ((sfRationalConstructibleLocalization l E (D.geometricFiber T₀).left).map
          (δ.hom.app K.obj))) ∧
  Nonempty (rationalDerivedPullback l E (D.geometricFrobenius T₀).asIso.inv ⋙
    sfWeilFrobeniusPullback D l hl T₀ E ≅ 𝟭 _) ∧
  ∃ s : (sfWeilFrobeniusPullback D l hl T₀ E).CommShift ℤ,
    (fun [_s : (sfWeilFrobeniusPullback D l hl T₀ E).CommShift ℤ] ↦
      (sfWeilFrobeniusPullback D l hl T₀ E).IsTriangulated) (_s := s)

/-- Both coefficient stages use the actual inverse scheme map, and their underlying
pullbacks are exact equivalences. Tensor and Hom comparisons below are fixed to
the recorded canonical transport maps, rather than arbitrary isomorphisms.
Source: blueprint sec-Weil-complexes, sentence 1, node proof steps 2--3 and 7--8
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodFieldOperationTransportSpec
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl T₀ x
  PodRationalFrobeniusTransportSpec D l hl T₀ E ∧
  (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).IsEquivalence ∧
  (∃ ε : sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω ⋙
      commonStageDerivedPullback l Ω (D.geometricFrobenius T₀).asIso.inv ≅ 𝟭 _,
    ∀ A : AlgebraicallyClosedCoefficients.Index l Ω,
      ∃ δ : sfWeilFrobeniusPullback D l hl T₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) ⋙
        rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
          (D.geometricFrobenius T₀).asIso.inv ≅ 𝟭 _,
        ∀ K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber T₀).left A,
          HEq (ε.hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion A).obj K))
            ((GeneralAlgebraicallyClosedCoefficients.inclusion A).map (δ.hom.app K))) ∧
  Nonempty (commonStageDerivedPullback l Ω (D.geometricFrobenius T₀).asIso.inv ⋙
    sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω ≅ 𝟭 _) ∧
  (∃ s : (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).CommShift ℤ,
    (fun [_s : (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).CommShift ℤ] ↦
      (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).IsTriangulated) (_s := s)) ∧
  (∃ μ : rationalDerivedTensor l E (D.geometricFiber T₀).left ⋙
        sfWeilFrobeniusPullback D l hl T₀ E ≅
      (sfWeilFrobeniusPullback D l hl T₀ E).prod
        (sfWeilFrobeniusPullback D l hl T₀ E) ⋙
          rationalDerivedTensor l E (D.geometricFiber T₀).left,
    (∀ K L, μ.app (K, L) =
      canonicalRationalPullbackTensor l E (D.geometricFrobenius T₀).asIso.hom K L) ∧
    PodTensorWeilLiftSpec (sfWeilFrobeniusPullback D l hl T₀ E)
      (rationalDerivedTensor l E (D.geometricFiber T₀).left) μ) ∧
  (∃ μ : commonStageDerivedTensor l Ω (D.geometricFiber T₀).left ⋙
        sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω ≅
      (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).prod
        (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω) ⋙
          commonStageDerivedTensor l Ω (D.geometricFiber T₀).left,
    (∀ K L, μ.app (K, L) =
      canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius T₀).asIso.hom K L) ∧
    PodTensorWeilLiftSpec (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω)
      (commonStageDerivedTensor l Ω (D.geometricFiber T₀).left) μ) ∧
  (∃ κ : rationalDerivedInternalHom l E (D.geometricFiber T₀).left ⋙
        sfWeilFrobeniusPullback D l hl T₀ E ≅
      podPairPullback (sfWeilFrobeniusPullback D l hl T₀ E)
        (constructibleRationalHomPairs l E (D.geometricFiber T₀).left)
        (constructibleRationalHomPairs l E (D.geometricFiber T₀).left)
        (podRationalPairs_pullback l E (D.geometricFrobenius T₀).asIso.hom) ⋙
          rationalDerivedInternalHom l E (D.geometricFiber T₀).left,
    (∀ K, κ.hom.app K = podRationalHomComparison l E (D.geometricFrobenius T₀).asIso.hom K) ∧
    PodHomWeilLiftSpec (sfWeilFrobeniusPullback D l hl T₀ E)
      (constructibleRationalHomPairs l E (D.geometricFiber T₀).left)
      (rationalDerivedInternalHom l E (D.geometricFiber T₀).left)
      (podRationalPairs_pullback l E (D.geometricFrobenius T₀).asIso.hom) κ) ∧
  ∃ κ : commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left ⋙
        sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω ≅
      podPairPullback (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω)
        (commonStageHomPairs l Ω (D.geometricFiber T₀).left)
        (commonStageHomPairs l Ω (D.geometricFiber T₀).left)
        (podCommonPairs_pullback l Ω (D.geometricFrobenius T₀).asIso.hom) ⋙
          commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left,
    (∀ K, κ.hom.app K = podCommonHomComparison l Ω (D.geometricFrobenius T₀).asIso.hom K) ∧
    PodHomWeilLiftSpec (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω)
      (commonStageHomPairs l Ω (D.geometricFiber T₀).left)
      (commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left)
      (podCommonPairs_pullback l Ω (D.geometricFrobenius T₀).asIso.hom) κ

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence commonStageTensorComparison
  operationStageTransitionIso commonStageDerivedTensor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem pod_field_transport
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    PodFieldOperationTransportSpec D l hl T₀ E Ω := by
  let i := fun x ↦ sfWeilPrimeInvertible D l hl T₀ x
  let : ∀ x : (D.geometricFiber T₀).left,
      Invertible (l : (D.geometricFiber T₀).left.residueField x) := i
  let : (D.geometricFiber T₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber T₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber T₀).left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (LocallyOfFiniteType
      (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber T₀).left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (QuasiCompact
      (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : IsIso (D.geometricFrobenius T₀).asIso.hom := (D.geometricFrobenius T₀).asIso.isIso_hom
  obtain ⟨iX, iY, H⟩ := isomorphismFieldTransport D l hl Ω
    (D.geometricFrobenius T₀).asIso.hom
  have hiX : iX = i := Subsingleton.elim _ _
  have hiY : iY = i := Subsingleton.elim _ _
  cases hiX
  cases hiY
  obtain ⟨hX, hY, hE, _, S, R, _, ⟨U⟩, ⟨V⟩⟩ := H
  obtain ⟨A⟩ := (hE E).1
  obtain ⟨B⟩ := (hE E).2
  have ht := isomorphismIntegralDerivedPullback_termwise l E
    (D.geometricFrobenius T₀).asIso.hom
  obtain ⟨h, ht, _⟩ := ht
  have hrat : PodRationalFrobeniusTransportSpec D l hl T₀ E := by
    unfold PodRationalFrobeniusTransportSpec
    dsimp only [sfWeilFrobeniusPullback]
    rw [← IsIso.Iso.inv_hom (D.geometricFrobenius T₀).asIso]
    refine ⟨⟨A.epsilon, ?_⟩, ?_, ⟨h, ht⟩, inferInstance, inferInstance,
      inferInstance, (podCompletedInverseImage_equivalence l E
        (D.geometricFrobenius T₀).asIso.hom).1, A.rationalEquivalence,
      ⟨A.epsilon, A.rationalEpsilon, ?_, A.rational_epsilon_formula⟩, ?_,
      ⟨A.rationalShift, A.rationalExact⟩⟩
    · intro K
      exact A.epsilon_formula K
    · simpa only [IsIso.inv_inv, IsIso.Iso.inv_hom, IsIso.Iso.inv_inv] using
        Nonempty.intro B.epsilon
    · intro K
      exact A.epsilon_formula K
    · simpa only [IsIso.inv_inv, IsIso.Iso.inv_hom, IsIso.Iso.inv_inv,
        sfWeilFrobeniusPullback] using Nonempty.intro B.rationalEpsilon
  have tensor := derivedPullbackTensorIso l E (D.geometricFrobenius T₀).asIso.hom 0 Ω
  obtain ⟨μ, hμ⟩ := tensor.2.2.2.2.2.2.1
  obtain ⟨ν, hν⟩ := tensor.2.2.2.2.2.2.2.1
  have homs := derivedAutomorphismHomEvaluation l E (D.geometricFrobenius T₀).asIso.hom 0 Ω
  obtain ⟨κ, hκ⟩ := homs.2.2.1
  obtain ⟨ρ, hρ⟩ := homs.2.2.2.1
  unfold PodFieldOperationTransportSpec
  dsimp only [sfWeilFrobeniusPullback, sfCommonStageWeilFrobeniusPullback]
  rw [← IsIso.Iso.inv_hom (D.geometricFrobenius T₀).asIso]
  refine ⟨hrat, U.equivalence, ⟨U.epsilon, ?_⟩, ?_, ⟨U.shift, U.exact⟩,
    ⟨μ, hμ, ?_⟩, ⟨ν, hν, ?_⟩, ⟨κ, hκ, ?_⟩, ⟨ρ, hρ, ?_⟩⟩
  · intro L
    set_option backward.isDefEq.respectTransparency false in
    refine ⟨(S L).rationalEpsilon, ?_⟩
    intro K
    exact U.epsilon_formula ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)
  · simpa only [IsIso.inv_inv, IsIso.Iso.inv_hom, IsIso.Iso.inv_inv,
      sfCommonStageWeilFrobeniusPullback] using Nonempty.intro V.epsilon
  · exact (pod_tensor_hom_field_operation_lifts _ _ μ _ _ _ κ).1
  · exact (pod_tensor_hom_field_operation_lifts _ _ ν _ _ _ ρ).1
  · exact (pod_tensor_hom_field_operation_lifts _ _ μ _ _ _ κ).2
  · exact (pod_tensor_hom_field_operation_lifts _ _ ν _ _ _ ρ).2

/-- Semilinear Frobenius geometry, exact field transport, and the canonical tensor
and internal-Hom lifts on both models. The covariant lifts, including the specified
Ex_* and Ex_!, are `pod_supplied_field_operation_lifts`; their explicit object and
arrow calculation is `pod_covariant_field_operation_lift`.
Source: blueprint main-20261015, prop-weil-operations.proof.md, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts).

Proof (the original nine steps, with existing field-transport records reused):
1. Apply lem-weil-frobenius-square-cartesian to the geometric scalar extension.
The upper structure map is g_T followed by a_T. Commutativity and f being over k
make the left vertical arrow a map between precisely those restructured corners;
no k-linearity of g_T is asserted, including when a model is nonseparated.
2. The exact inverse-image equivalence on completed modules identifies integral
pullback with termwise transport (lem-weil-proetale-isomorphism-inverse-image and
lem-weil-isomorphism-derived-pullback). Compose lambda for g and its inverse
with the inverse-image counit to obtain the normalized epsilon and its reverse.
3. Localize the integral inverse equations linearly on Hom tensor E. At common
stages represent an arrow over one finite field. Scalar compatibility of the
inverse identities (lem-pod-pullback-identities-scalar-extension) and the specified
operation scalar comparisons turn its naturality square into that finite-stage
square. Identity extensions and tower cocycles preserve its class. Exactness
comes from the exact module transport, integral triangles and common-stage triangles.
4. For pullback compose the inverse compositor for (g_X,f) with that for (f,g_Y).
Integral composition is lem-pod-integral-pullback-composition; its scalar equation
descends to rational and common stages, with the same comparison on every arrow.
5. The mate of its inverse is exactly Ex_* of def-exchange-projection. Horizontal
equivalences make it invertible by lem-weil-mate-iso-along-equivalences. For Ex_!,
the proper mate is invertible by the same argument; compose it with the supplied
open comparison and the compactification identifications on the preserved domain.
6. The covariant calculation is pod_covariant_field_operation_lift. Applying it
to those comparisons gives pod_supplied_field_operation_lifts, with the actual
supplied-domain units, counits, compactification and coefficient normalizations.
7. The canonical tensor comparison is lem-pur-derived-pullback-tensor-iso.
Tensoring the two structure maps after it gives the tensor lift and its arrow law.
8. Lem-pod-derived-automorphism-hom-evaluation supplies the evaluation-defined Hom
comparison, natural on exactly the permitted pairs. Apply the inverse structure
in the first variable and the forward structure in the second. The inverse
intertwining equation and comparison naturality give the Hom arrow law.
9. The forgetful equalities retain every original object and arrow. Finite-Tor
field categories equal the bounded constructible categories by definition.
Any previously imposed site-perfect first-variable subdomain remains a restriction
of the same permitted-pair functor. No new constructibility or triangulation
of fixed pairs is inferred. -/
theorem semilinearFieldOperationLifts
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    IsPullback (D.geometricFrobenius X₀).asIso.hom
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
      (D.geometricFrobenius Y₀).asIso.hom ∧
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left ≫
        (D.geometricFrobenius Y₀).asIso.hom ≫ (D.geometricFiber Y₀).hom =
      (D.geometricFrobenius X₀).asIso.hom ≫ (D.geometricFiber X₀).hom ∧
    PodFieldOperationTransportSpec D l hl X₀ E Ω ∧
    PodFieldOperationTransportSpec D l hl Y₀ E Ω := by
  have hgeom := D.frobenius_square_cartesian X₀ Y₀ f₀
  refine ⟨hgeom.2.2.2.2.2.1, ?_, pod_field_transport D l hl X₀ E Ω,
    pod_field_transport D l hl Y₀ E Ω⟩
  have hc : (D.geometricFrobenius X₀).asIso.hom ≫
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left ≫
        (D.geometricFrobenius Y₀).asIso.hom := hgeom.2.2.2.2.1
  rw [← Category.assoc, ← hc, Category.assoc]
  congr 1
  exact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap D.k₀ D.k)))).map f₀).w

end WeilConjectures
