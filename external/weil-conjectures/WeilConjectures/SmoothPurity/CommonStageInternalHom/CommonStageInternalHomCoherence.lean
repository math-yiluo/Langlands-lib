/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Common.CommonStageInternalHomData
import all WeilConjectures.SmoothPurity.CommonStageInternalHom.CommonStageInternalHomCoherenceLemmas

/-! The missing normalized Hom comparison coherence for common-stage transport.
Source: the common-stage internal-Hom paragraph of prose-03-02.
(blueprint: lem-weil-common-stage-internal-hom-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.auxLemma false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open Opposite CategoryTheory AlgebraicGeometry

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  rationalDerivedInternalHom sfRationalScalarExtension ScalarLocalization.category
  StageSystem.PairCategory.mkHom
  commonStageHomComparison rationalHomScalarComparison operationStageTransitionIso
  scalarAssociator GeneralAlgebraicallyClosedCoefficients.associator
  sfRationalScalarComp sfRationalScalarUnit
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue ScalarLocalization.composition
  sfIntegralConstructible ScalarLocalization.linear ScalarLocalization.preadditive
  Linear.homModule Preadditive.homGroup Preadditive.fullSubcategory
  Linear.fullSubcategory sfIntegralConstructibleLinear

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

set_option allowUnsafeReducibility true in
attribute [local reducible] ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  commonStageHomObject commonStageHomPairAtStage rationalHomScalarPair

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (W : Scheme.{u})

namespace CommonStageInternalHom

attribute [local irreducible] rawComparison
set_option allowUnsafeReducibility true in
attribute [local reducible] scalarPairs

variable (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
  (L : Index l Ω)
  (h : (commonStageHomObject l Ω W P).stage ≤ L)
  (h' : (commonStageHomObject l Ω W Q).stage ≤ L)
  (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
    (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
  (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
    (commonStageHomPairAtStage l Ω W Q L h').obj.2)

private def pairStep (P : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L)
    (M : Index l Ω) (k : L ≤ M) :
    rationalHomScalarPair l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k) W (commonStageHomPairAtStage l Ω W P L h) ≅
        commonStageHomPairAtStage l Ω W P M (h.trans k) :=
  ObjectProperty.isoMk _ (Iso.prod
    (inputStep l Ω W P.obj.1.unop
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h) k).symm.op
    (inputStep l Ω W P.obj.2
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans h) k))

attribute [local irreducible] inputStep pairStep

private def stepComparison (P : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L)
    (M : Index l Ω) (k : L ≤ M) :
    ((stageSystem l Ω W).T k).obj
      ((rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).obj
        (commonStageHomPairAtStage l Ω W P L h)) ≅
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω M) W).obj
        (commonStageHomPairAtStage l Ω W P M (h.trans k)) :=
  (operationStageTransitionIso l Ω W L M k).app _ ≪≫
    (rawComparison l Ω W k).app (commonStageHomPairAtStage l Ω W P L h) ≪≫
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω M) W).mapIso
      (pairStep l Ω W P L h M k)

private theorem step_naturality (M : Index l Ω) (k : L ≤ M) :
    ((stageSystem l Ω W).T k).map
      ((rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map
        (ObjectProperty.homMk
          (X := commonStageHomPairAtStage l Ω W P L h)
          (Y := commonStageHomPairAtStage l Ω W Q L h') (Prod.mkHom a.op b))) ≫
      (stepComparison l Ω W Q L h' M k).hom =
    (stepComparison l Ω W P L h M k).hom ≫
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω M) W).map
        (ObjectProperty.homMk
          (X := commonStageHomPairAtStage l Ω W P M (h.trans k))
          (Y := commonStageHomPairAtStage l Ω W Q M (h'.trans k))
          (Prod.mkHom ((stageSystem l Ω W).tr k a).op
            ((stageSystem l Ω W).tr k b))) := by
  apply comparison_naturality (operationStageTransitionIso l Ω W L M k)
    (rawComparison l Ω W k) (pairStep l Ω W P L h M k)
    (pairStep l Ω W Q L h' M k) _ _
  apply ObjectProperty.hom_ext
  apply Prod.ext
  · have ht := inverse_naturality _ _ _ _ (inputStep_naturality l Ω W
      Q.obj.1.unop P.obj.1.unop
      (((Padic.finiteCoefficientFields_properties l Ω).1
        Q.obj.1.unop.stage Q.obj.2.stage).1.trans h')
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h) k a)
    simpa only [scalarPairs, pairStep, ObjectProperty.isoMk, ObjectProperty.homMk,
      Iso.prod_hom, Iso.op_hom, Iso.symm_hom, ObjectProperty.FullSubcategory.comp_hom,
      prod_comp, Prod.mkHom, Quiver.Hom.unop_op, op_comp] using
      congrArg Quiver.Hom.op ht
  · have ht := inputStep_naturality l Ω W P.obj.2 Q.obj.2
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans h)
      (((Padic.finiteCoefficientFields_properties l Ω).1
        Q.obj.1.unop.stage Q.obj.2.stage).2.trans h') k b
    simpa only [scalarPairs, pairStep, ObjectProperty.isoMk, ObjectProperty.homMk,
      Iso.prod_hom, Iso.op_hom, Iso.symm_hom, ObjectProperty.FullSubcategory.comp_hom,
      prod_comp, Prod.mkHom] using ht

private theorem pairStep_tower
    (P : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    {E L M : Index l Ω} (hi : (commonStageHomObject l Ω W P).stage ≤ E)
    (h : E ≤ L) (k : L ≤ M) :
    (scalarPairs l Ω W k).mapIso (pairStep l Ω W P E hi L h) ≪≫
        pairStep l Ω W P L (hi.trans h) M k =
      scalarPairsAssoc l Ω W h k (commonStageHomPairAtStage l Ω W P E hi) ≪≫
        pairStep l Ω W P E hi M (h.trans k) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  apply Prod.ext
  · have ht := congrArg Iso.inv (inputStep_tower l Ω W P.obj.1.unop
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans hi) h k)
    simpa only [scalarPairs, pairStep, scalarPairsAssoc, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, ObjectProperty.isoMk, ObjectProperty.homMk,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Iso.prod_hom, Iso.op_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, prod_comp,
      op_comp, Quiver.Hom.unop_op, rationalHomScalarPair, Prod.mkHom] using
      congrArg Quiver.Hom.op ht
  · have ht := congrArg Iso.hom (inputStep_tower l Ω W P.obj.2
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans hi) h k)
    simpa only [scalarPairs, pairStep, scalarPairsAssoc, Iso.trans_hom,
      Functor.mapIso_hom, ObjectProperty.isoMk, ObjectProperty.homMk,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Iso.prod_hom, Iso.op_hom, Iso.symm_hom, Iso.app_hom, prod_comp,
      rationalHomScalarPair, Prod.mkHom] using ht

private theorem step_tower
    (P : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    {E L M : Index l Ω} (hi : (commonStageHomObject l Ω W P).stage ≤ E)
    (h : E ≤ L) (k : L ≤ M) :
    ((stageSystem l Ω W).T k).map (stepComparison l Ω W P E hi L h).hom ≫
        (stepComparison l Ω W P L (hi.trans h) M k).hom =
      ((stageSystem l Ω W).assoc h k).hom.app
          ((rationalDerivedInternalHom l (Coefficient.{u} l Ω E) W).obj
            (commonStageHomPairAtStage l Ω W P E hi)) ≫
        (stepComparison l Ω W P E hi M (h.trans k)).hom := by
  unfold stepComparison
  apply comparison_tower_glue
    (operationStageTransitionIso l Ω W E L h)
    (operationStageTransitionIso l Ω W L M k)
    (operationStageTransitionIso l Ω W E M (h.trans k))
    (rawComparison l Ω W h) (rawComparison l Ω W k) (rawComparison l Ω W (h.trans k))
    (associator l Ω W E L M h k) ((stageSystem l Ω W).assoc h k)
    (commonStageHomPairAtStage l Ω W P E hi)
    (pairStep l Ω W P E hi L h) (pairStep l Ω W P L (hi.trans h) M k)
    (pairStep l Ω W P E hi M (h.trans k))
    (scalarPairsAssoc l Ω W h k (commonStageHomPairAtStage l Ω W P E hi))
  · simpa only [Iso.trans_hom, Functor.mapIso_hom] using
      congrArg Iso.hom (pairStep_tower l Ω W P hi h k)
  · exact rationalHomComparison_tower l Ω W h k (commonStageHomPairAtStage l Ω W P E hi)
  · have he := @transition_tower (Index l Ω) inferInstance
      (Stage l Ω W) (stageCategory l Ω W)
      (fun {E L} h ↦ transition l Ω W E L h)
      (fun {E L M} h k ↦ associator l Ω W E L M h k)
      (stageSystem l Ω W)
      (fun {E L} h ↦ by
        simpa only [stageSystem] using
          (stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)
      (fun {E L M} h k ↦ by
        simpa only [stageSystem] using
          (stageSystem_existsUnique l Ω W).exists.choose_spec.2 E L M h k)
      E L M h k
      ((rationalDerivedInternalHom l (Coefficient.{u} l Ω E) W).obj
        (commonStageHomPairAtStage l Ω W P E hi))
    simpa only [operationStageTransitionIso] using he

private theorem comparison_eq_step
    (P : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    commonStageHomComparison l Ω W P L h =
      stepComparison l Ω W P (commonStageHomObject l Ω W P).stage le_rfl L h := by
  unfold commonStageHomComparison stepComparison rawComparison pairStep inputStep
  rfl

private theorem comparison_tower
    (P : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L)
    (M : Index l Ω) (k : L ≤ M) :
    ((stageSystem l Ω W).T k).map (commonStageHomComparison l Ω W P L h).hom ≫
      (stepComparison l Ω W P L h M k).hom =
    ((stageSystem l Ω W).assoc h k).hom.app (commonStageHomObject l Ω W P).obj ≫
      (commonStageHomComparison l Ω W P M (h.trans k)).hom := by
  rw [comparison_eq_step, comparison_eq_step]
  exact step_tower l Ω W P le_rfl h k

/-- The normalized Hom comparison square at one coefficient extension.
Source: the common-stage internal-Hom paragraph of prose-03-02;
The specified rational scalar Hom tower and naturality supply the finite-stage equations.
(blueprint: lem-weil-common-stage-internal-hom-coherence).

Proof: expand each comparison into its operation-stage transition, normalized rational Hom
comparison, and the two recorded stage associators. The scalar Hom tower equation and its
naturality identify the middle square; functoriality of derived internal Hom cancels the
inverse first associator and forward second associator. The remaining operation-stage
transition and stage-system associators are exactly the displayed transport isomorphisms. -/
theorem commonStageHomComparison_hom_square
    (M : Index l Ω) (k : L ≤ M) :
    let cP_L := commonStageHomComparison l Ω W P L h
    let cQ_L := commonStageHomComparison l Ω W Q L h'
    let cP_M := commonStageHomComparison l Ω W P M (h.trans k)
    let cQ_M := commonStageHomComparison l Ω W Q M (h'.trans k)
    ((stageSystem l Ω W).assoc h k).inv.app
          (commonStageHomObject l Ω W P).obj ≫
      ((stageSystem l Ω W).T k).map
        (cP_L.hom ≫
          (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map
            (ObjectProperty.homMk
              (X := commonStageHomPairAtStage l Ω W P L h)
              (Y := commonStageHomPairAtStage l Ω W Q L h') (Prod.mkHom a.op b)) ≫
          cQ_L.inv) ≫
      ((stageSystem l Ω W).assoc h' k).hom.app
          (commonStageHomObject l Ω W Q).obj =
    cP_M.hom ≫
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω M) W).map
        (ObjectProperty.homMk
          (X := commonStageHomPairAtStage l Ω W P M (h.trans k))
          (Y := commonStageHomPairAtStage l Ω W Q M (h'.trans k))
          (Prod.mkHom ((stageSystem l Ω W).tr k a).op
            ((stageSystem l Ω W).tr k b))) ≫
      cQ_M.inv := by
  exact conjugate_square ((stageSystem l Ω W).T k)
    (((stageSystem l Ω W).assoc h k).app (commonStageHomObject l Ω W P).obj)
    (((stageSystem l Ω W).assoc h' k).app (commonStageHomObject l Ω W Q).obj)
    (commonStageHomComparison l Ω W P L h) (commonStageHomComparison l Ω W Q L h')
    (commonStageHomComparison l Ω W P M (h.trans k))
    (commonStageHomComparison l Ω W Q M (h'.trans k))
    (stepComparison l Ω W P L h M k) (stepComparison l Ω W Q L h' M k) _ _
    (comparison_tower l Ω W P L h M k) (comparison_tower l Ω W Q L h' M k)
    (step_naturality l Ω W P Q L h h' a b M k)

end CommonStageInternalHom
end WeilConjectures
