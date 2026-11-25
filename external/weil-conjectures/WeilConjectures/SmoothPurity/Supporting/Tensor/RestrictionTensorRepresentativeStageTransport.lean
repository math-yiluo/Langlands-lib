/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

import WeilConjectures.SmoothPurity.Rational.RationalPullbackStageCoherence
import WeilConjectures.SmoothPurity.Supporting.Tensor.MixedTensorStageComponent
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackEndpoint
import WeilConjectures.SmoothPurity.Common.CommonStageTensorEndpoint
import WeilConjectures.SmoothPurity.Supporting.Tensor.RestrictionTensorNormalizedSquare
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all Mathlib.Logic.Small.Defs

/-! # Stage transport of restriction tensor representatives

Source: lemma-section-normal-bundle--1, common-stage subargument, steps 3--5
(blueprint: lem-pur-restriction-tensor-representative-transport).

The stage-level transport identity used by the quotient representative theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory Stage transition
  WeilConjectures.commonStagePullbackObject WeilConjectures.commonStageTensorObject

set_option allowUnsafeReducibility true in
attribute [local reducible] stageSystem

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  ScalarLocalization.category ScalarLocalization.composition
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue sfRationalScalarComp
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.normalizedAssociator
  AlgebraicallyClosedCoefficients.coefficientInclusion
  ObjectProperty.FullSubcategory.category sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  sfRationalScalarExtension commonStageDerivedPullback commonStageDerivedTensor
  rationalPullbackScalarComparison rationalTensorScalarComparison
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A stage transport equality gives equality of the corresponding pair-category
representatives. -/
theorem pairRepresentative_eq_of_stage_transport
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category* (C i)]
    (S : StageSystem C) {A B : S.PairCategory} {H L : I}
    (hA : A.stage ≤ H) (hB : B.stage ≤ H) (h : H ≤ L)
    (u : A.toStage hA ⟶ B.toStage hB)
    (v : A.toStage (hA.trans h) ⟶ B.toStage (hB.trans h))
    (hv : v = S.tr h u) :
    StageSystem.PairCategory.mkHom H hA hB u =
      StageSystem.PairCategory.mkHom L (hA.trans h) (hB.trans h) v := by
  rw [hv]
  exact (StageSystem.PairCategory.mkHom_tr h u).symm

/-- Prescribed pullback and tensor endpoints transport the mixed-square representative. -/
private theorem mixedTensorRepresentative_transport
    {I : Type*} [Preorder I]
    {C : I → Type*} [∀ i, Category* (C i)]
    {D : I → Type*} [∀ i, Category* (D i)]
    (SX : StageSystem C) (SY : StageSystem D)
    (R : ∀ i, C i ⥤ D i) (TX : ∀ i, C i × C i ⥤ C i)
    (TY : ∀ i, D i × D i ⥤ D i)
    (p : ∀ {i j : I} (h : i ≤ j), R i ⋙ SY.T h ≅ SX.T h ⋙ R j)
    (coh : StageSystem.pairFunctorCoherent SX SY R p)
    (tX : ∀ {i j : I} (h : i ≤ j), TX i ⋙ SX.T h ≅
      (SX.T h).prod (SX.T h) ⋙ TX j)
    (tY : ∀ {i j : I} (h : i ≤ j), TY i ⋙ SY.T h ≅
      (SY.T h).prod (SY.T h) ⋙ TY j)
    (mu : ∀ i, TX i ⋙ R i ≅ (R i).prod (R i) ⋙ TY i)
    (square : ∀ {i j : I} (h : i ≤ j) (M N : C i),
      (SY.T h).map ((mu i).hom.app (M, N)) ≫
          (tY h).hom.app ((R i).obj M, (R i).obj N) ≫
          (TY j).map (Prod.mkHom ((p h).hom.app M) ((p h).hom.app N)) =
        (p h).hom.app ((TX i).obj (M, N)) ≫
          (R j).map ((tX h).hom.app (M, N)) ≫
          (mu j).hom.app ((SX.T h).obj M, (SX.T h).obj N))
    (q : ∀ (P : SX.PairCategory) (K : I) (k : P.stage ≤ K),
      (SY.T k).obj ((R P.stage).obj P.obj) ≅ (R K).obj (P.toStage k))
    (hq : ∀ P K k, q P K k = (p k).app P.obj)
    (A B : SX.PairCategory) (H : I) (hA : A.stage ≤ H) (hB : B.stage ≤ H)
    (qX : ∀ (K : I) (k : H ≤ K),
      (SX.T k).obj ((TX H).obj (A.toStage hA, B.toStage hB)) ≅
        (TX K).obj (A.toStage (hA.trans k), B.toStage (hB.trans k)))
    (qY : ∀ (K : I) (k : H ≤ K),
      (SY.T k).obj ((TY H).obj
        ((SY.T hA).obj ((R A.stage).obj A.obj),
          (SY.T hB).obj ((R B.stage).obj B.obj))) ≅
        (TY K).obj ((SY.T (hA.trans k)).obj ((R A.stage).obj A.obj),
          (SY.T (hB.trans k)).obj ((R B.stage).obj B.obj)))
    (hqX : ∀ K k, qX K k =
      (tX k).app (A.toStage hA, B.toStage hB) ≪≫
        (TX K).mapIso (Iso.prod ((SX.assoc hA k).app A.obj)
          ((SX.assoc hB k).app B.obj)))
    (hqY : ∀ K k, qY K k =
      (tY k).app ((SY.T hA).obj ((R A.stage).obj A.obj),
        (SY.T hB).obj ((R B.stage).obj B.obj)) ≪≫
        (TY K).mapIso (Iso.prod ((SY.assoc hA k).app ((R A.stage).obj A.obj))
          ((SY.assoc hB k).app ((R B.stage).obj B.obj))))
    (L : I) (h : H ≤ L) :
    let c := fun (K : I) (k : H ≤ K) ↦
      (q ⟨H, (TX H).obj (A.toStage hA, B.toStage hB)⟩ K k ≪≫
        (R K).mapIso (qX K k)).hom ≫
        (mu K).hom.app (A.toStage (hA.trans k), B.toStage (hB.trans k)) ≫
        (qY K k ≪≫ (TY K).mapIso
          (Iso.prod (q A K (hA.trans k)) (q B K (hB.trans k)))).inv
    c L h = SY.tr h (c H le_rfl) := by
  intro c
  let d := (mu H).hom.app (A.toStage hA, B.toStage hB) ≫
    (TY H).map (Prod.mkHom (q A H hA).inv (q B H hB).inv)
  have hc (K : I) (k : H ≤ K) : c K k = (SY.T k).map d := by
    dsimp only [c]
    rw [hq _ K k, hqX K k, hqY K k]
    exact mixedTensorStageComponent SX SY R TX TY p coh tX tY mu square A B
      (q A) (q B) (hq A) (hq B) H K hA hB k
  exact (hc L h).trans ((SY.tr_map h d).symm.trans
    (congrArg (SY.tr h) (hc H le_rfl).symm))

/--
At the level of the finite coefficient stage, the mixed scalar square and the
naturality of the tensor comparison identify the representative at an extension
with the stage-system transport of the representative at the original stage.
This is the component calculation: expand the two endpoint comparisons, use the
mixed square to move the pullback comparison through the tensor comparison, and
cancel inverse comparison isomorphisms.  The coefficient tower equations identify
the remaining comparisons with the direct ones, while the scalar associator
cocycle and naturality of `mu` identify the outer conjugates.  Different stages
are retained as transition maps; no literal equality of coefficient fields is
used. -/
theorem restrictionTensorRepresentativeStageTransport
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    let R := fun E : Index l Ω ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f
    let T := fun (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (E : Index l Ω) ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) W
    let b := fun (E L : Index l Ω) (h : E ≤ L) ↦
      rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f
    let theta := fun (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (E L : Index l Ω) (h : E ≤ L) ↦
      rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W
    let S := fun A B : Pair l Ω X ↦
      commonStagePullbackObject l Ω f (commonStageTensorObject l Ω X A B)
    let U := fun A B : Pair l Ω X ↦ commonStageTensorObject l Ω Y
      (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B)
    let a := fun (A B : Pair l Ω X) (L : Index l Ω) (h : (S A B).stage ≤ L) ↦
      commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω X A B) L h ≪≫
        (R L).mapIso (commonStageTensorComparison l Ω X A B L h)
    let z := fun (A B : Pair l Ω X) (L : Index l Ω) (h : (U A B).stage ≤ L) ↦
      commonStageTensorComparison l Ω Y
        (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B) L h ≪≫
      (T Y L).mapIso (Iso.prod
        (commonStagePullbackComparison l Ω f A L
          (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h))
        (commonStagePullbackComparison l Ω f B L
          (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h)))
    ∀ (mu : ∀ E : Index l Ω, T X E ⋙ R E ≅ (R E).prod (R E) ⋙ T Y E),
      (∀ (E L : Index l Ω) (h : E ≤ L) (M N : Stage l Ω X E),
        (transition l Ω Y E L h).map ((mu E).hom.app (M, N)) ≫
          (theta Y E L h).hom.app ((R E).obj M, (R E).obj N) ≫
          (T Y L).map (Prod.mkHom ((b E L h).hom.app M) ((b E L h).hom.app N)) =
        (b E L h).hom.app ((T X E).obj (M, N)) ≫
          (R L).map ((theta X E L h).hom.app (M, N)) ≫
          (mu L).hom.app ((transition l Ω X E L h).obj M,
            (transition l Ω X E L h).obj N)) →
      ∀ (A B : Pair l Ω X) (L : Index l Ω) (h : (S A B).stage ≤ L),
        let H := (S A B).stage
        let c := fun (K : Index l Ω) (hK : H ≤ K) ↦
          (a A B K hK).hom ≫
            (mu K).hom.app
              (A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                A.stage B.stage).1.trans hK),
               B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                A.stage B.stage).2.trans hK)) ≫ (z A B K hK).inv
        c L h = (stageSystem l Ω Y).tr h (c H le_rfl) := by
  intro R T b theta S U a z mu mixed A B L h H c
  exact mixedTensorRepresentative_transport
    (C := Stage l Ω X) (D := Stage l Ω Y)
    (stageSystem l Ω X) (stageSystem l Ω Y) R (T X) (T Y)
    (fun {_ _} k ↦ rationalPullbackStageComparison l Ω f k)
    (rationalPullbackStageComparison_coherent l Ω f)
    (fun {_ _} k ↦ rationalTensorStageComparison l Ω X k)
    (fun {_ _} k ↦ rationalTensorStageComparison l Ω Y k) mu
    (fun {E K} k ↦ restrictionTensorNormalizedSquare l Ω f mu mixed E K k)
    (fun P K k ↦ commonStagePullbackComparison l Ω f P K k)
    (fun P K k ↦ (commonStagePullback_endpoint l Ω f P K k).symm)
    A B H
    ((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1
    ((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2
    (fun K k ↦ commonStageTensorComparison l Ω X A B K k)
    (fun K k ↦ commonStageTensorComparison l Ω Y
      (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B) K k)
    (fun K k ↦ (commonStageTensor_endpoint l Ω X A B K k).symm)
    (fun K k ↦ (commonStageTensor_endpoint l Ω Y
      (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B) K k).symm)
    L h

end WeilConjectures
