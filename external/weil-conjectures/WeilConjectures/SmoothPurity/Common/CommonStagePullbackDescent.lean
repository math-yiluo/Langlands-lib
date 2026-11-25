/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Common.CommonStagePullbackData

import WeilConjectures.SmoothPurity.Rational.RationalPullbackStageCoherence
import WeilConjectures.SmoothPurity.NormalizedPairDescent.PairDescentPrescribedComponents

/-! # Coherent comparisons and descent for common-stage pullback

These are the existing complete pullback proofs, isolated after profiling the item.
(blueprint: lem-weil-common-stage-pullback-comparison-data;
lem-weil-common-stage-pullback-descent-from-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue integralDerivedPullback integralCompletedTensor
  integralDerivedInternalHom sfRationalScalarExtension
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar
  rationalDerivedPullback rationalDerivedTensor rationalDerivedInternalHom
  ScalarLocalization.composition StageSystem.PairCategory.mkHom sfIntegralConstructible
  ScalarLocalization.linear ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear
  sfConstructibleIntegralScalarExtension sfIntegralScalarComp sfIntegralScalarUnit
  operationStageTransitionIso commonStagePullbackComparison ScalarLocalization.category

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/- The scalar comparisons form a coherent stage-system morphism.  The proof is
   the tower coherence calculation for the normalized rational pullback
   comparisons (blueprint: lem-weil-common-stage-pullback-comparison-data).
   The normalized scalar-extension tower calculation supplies the comparison
   components and their pairFunctorCoherent equation. -/
theorem commonStagePullback_comparison_data {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ b : ∀ {E L : Index l Ω} (h : E ≤ L),
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) f) ⋙
          (stageSystem l Ω X).T h ≅
        (stageSystem l Ω Y).T h ⋙
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) f),
      (∀ {E L : Index l Ω} (h : E ≤ L)
        (P : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
        HEq ((b h).hom.app P)
          ((commonStagePullbackComparison l Ω f ⟨E, P⟩ L h).hom) ∧
        HEq ((b h).inv.app P)
          ((commonStagePullbackComparison l Ω f ⟨E, P⟩ L h).inv)) ∧
      (∀ {E L M : Index l Ω} (h : E ≤ L) (h' : L ≤ M)
        (P : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
        ((stageSystem l Ω X).T h').map ((b h).hom.app P) ≫
          (b h').hom.app (((stageSystem l Ω Y).T h).obj P) ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω M) f).map
            (((stageSystem l Ω Y).assoc h h').hom.app P) =
        (((stageSystem l Ω X).assoc h h').hom.app
            ((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).obj P) ≫
          (b (h.trans h')).hom.app P)) := by
  refine ⟨fun {_ _} h ↦ rationalPullbackStageComparison l Ω f h, ?_,
    rationalPullbackStageComparison_coherent l Ω f⟩
  intro E L h P
  have hi : (rationalPullbackStageComparison l Ω f h).app P =
      commonStagePullbackComparison l Ω f ⟨E, P⟩ L h := by
    apply Iso.ext
    unfold rationalPullbackStageComparison commonStagePullbackComparison
      operationStageTransitionIso
    simp only [Iso.app_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
      commonStagePullbackObject]
  exact ⟨heq_of_eq (congrArg Iso.hom hi), heq_of_eq (congrArg Iso.inv hi)⟩

/-- Descent from a fixed coherent pullback comparison family.
Source: the common-stage pullback paragraph of the blueprint.
(blueprint: lem-weil-common-stage-pullback-descent-from-data).
The proof applies the StageSystem coefficient-pair descent constructor and then
rewrites the descended representative formula using the supplied comparison
components. -/
theorem commonStagePullback_descent_from_data {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (b : ∀ {E L : Index l Ω} (h : E ≤ L),
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) f) ⋙
          (stageSystem l Ω X).T h ≅
        (stageSystem l Ω Y).T h ⋙
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) f))
    (hb : ∀ {E L : Index l Ω} (h : E ≤ L)
        (P : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
        HEq ((b h).hom.app P)
          ((commonStagePullbackComparison l Ω f ⟨E, P⟩ L h).hom) ∧
        HEq ((b h).inv.app P)
          ((commonStagePullbackComparison l Ω f ⟨E, P⟩ L h).inv))
    (hcoh : ∀ {E L M : Index l Ω} (h : E ≤ L) (h' : L ≤ M)
        (P : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
        ((stageSystem l Ω X).T h').map ((b h).hom.app P) ≫
          (b h').hom.app (((stageSystem l Ω Y).T h).obj P) ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω M) f).map
            (((stageSystem l Ω Y).assoc h h').hom.app P) =
        (((stageSystem l Ω X).assoc h h').hom.app
            ((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).obj P) ≫
          (b (h.trans h')).hom.app P)) :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X,
      (∀ P, F.obj P = commonStagePullbackObject l Ω f P) ∧
      (∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
        (L : Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
        (a : P.toStage hP ⟶ Q.toStage hQ),
        HEq (F.map (X := P) (Y := Q) (ofHom P Q L hP hQ a))
          (ofHom (commonStagePullbackObject l Ω f P)
            (commonStagePullbackObject l Ω f Q) L hP hQ
            ((commonStagePullbackComparison l Ω f P L hP).hom ≫
              (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map a ≫
              (commonStagePullbackComparison l Ω f Q L hQ).inv))) := by
  dsimp only [ofHom, StageHom, stageTransition, commonStagePullbackObject]
  have H := @NormalizedPairDescent.existsUnique (Index l Ω) inferInstance inferInstance
    (Stage l Ω Y) (fun E ↦ stageCategory l Ω Y E)
    (Stage l Ω X) (fun E ↦ stageCategory l Ω X E)
    (stageSystem l Ω Y) (stageSystem l Ω X)
    (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f) b hcoh
    (fun P L h ↦ commonStagePullbackComparison l Ω f P L h)
    (by
      intro P L h
      cases P with
      | mk E P => exact hb h P)
  exact H

end WeilConjectures
