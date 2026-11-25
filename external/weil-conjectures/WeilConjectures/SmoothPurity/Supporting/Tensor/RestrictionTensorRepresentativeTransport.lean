/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SmoothPurity.Supporting.Tensor.RestrictionTensorRepresentativeStageTransport

/-! # Enlargement of restriction tensor representatives

Source: lemma-section-normal-bundle--1, common-stage subargument
(blueprint: lem-pur-restriction-tensor-representative-transport).

The component calculation from steps 3--5 of the common-stage restriction tensor
argument. It compares two representatives of a single component; no natural
transformation or choice of a colimit component is part of the assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
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
attribute [local reducible] stageCategory
  WeilConjectures.commonStagePullbackObject WeilConjectures.commonStageTensorObject

namespace WeilConjectures

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  sfRationalScalarExtension commonStageDerivedPullback commonStageDerivedTensor
  rationalPullbackScalarComparison rationalTensorScalarComparison
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The mixed tensor square identifies the class of the compositum representative
with its class at every larger finite field.
Source: lemma-section-normal-bundle--1, common-stage subargument, steps 3--5
(blueprint: lem-pur-restriction-tensor-representative-transport).
Proof: write c_H as mu_H followed by the tensor of the inverse pullback scalar
comparisons. At L, tensor comparison naturality moves the scalar extension of
these inverse comparisons past theta. Cancel the two pullback comparisons in
the mixed square. The pullback scalar tower equations identify each remaining
input comparison with the direct one from its original field to L. Naturality
of mu_L moves both input associators past mu_L. The resulting expression is
exactly the source and target associator conjugate of c_H. The pair-category
transport rule therefore identifies the two classes, including L=H. -/
theorem restrictionTensorRepresentativeTransport
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
        ofHom (S A B) (U A B) H le_rfl le_rfl (c H le_rfl) =
          ofHom (S A B) (U A B) L h h (c L h) := by
  intro R T b theta S U a z mu hmu A B L h H c
  have hs := restrictionTensorRepresentativeStageTransport l Ω f mu hmu A B L h
  exact pairRepresentative_eq_of_stage_transport (stageSystem l Ω Y) _ _ h _ _ hs

end WeilConjectures
