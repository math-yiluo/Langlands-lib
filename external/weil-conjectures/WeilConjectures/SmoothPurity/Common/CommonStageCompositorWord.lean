/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackCoefficientUnit
import WeilConjectures.SmoothPurity.Common.CommonStageRationalCompositionNaturality
import all Mathlib.Logic.Small.Defs
import WeilConjectures.SmoothPurity.Common.CommonStageNormalizedComposition

/-! # The literal-stage representative of the common compositor

Source: purity/trace equivariance proof Step 1, canonical pullback compositors.
(blueprint: lem-pur-common-stage-compositor-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

-- Use the same cached category structures as the coefficient comparison APIs.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
  GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.category StageSystem.instCategoryPairCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  StageSystem.ι sfRationalConstructibleLocalization ScalarLocalization.localization
  commonStagePullbackObject

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback
  constructibleIntegralPullback Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  sfRationalScalarExtension rationalPullbackScalarComparison sfRationalScalarComp

set_option allowUnsafeReducibility true in
attribute [local semireducible] GeneralAlgebraicallyClosedCoefficients.Stage

-- Give the cached stage categories the rational functor's actual object and map data.
private def stagePull (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : AlgebraicallyClosedCoefficients.Index l Ω) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E where
  obj := (rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).obj
  map := (rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).map
  map_id K := (rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).map_id K
  map_comp a b := (rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).map_comp a b

private def stageComp (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : AlgebraicallyClosedCoefficients.Index l Ω) {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z E) :
    (stagePull l Ω E (f ≫ g)).obj K ≅
      (stagePull l Ω E f).obj ((stagePull l Ω E g).obj K) where
  hom := (pullbackTensorRationalComposition l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) g f K).hom
  inv := (pullbackTensorRationalComposition l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) g f K).inv
  hom_inv_id := (pullbackTensorRationalComposition l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) g f K).hom_inv_id
  inv_hom_id := (pullbackTensorRationalComposition l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) g f K).inv_hom_id

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage stagePull stageComp

set_option allowUnsafeReducibility true in
attribute [local semireducible] GeneralAlgebraicallyClosedCoefficients.Stage

private def stageUnit (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W).T (le_refl E) ≅
      𝟭 (GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E) :=
  operationStageTransitionIso l Ω W E E le_rfl ≪≫
    GeneralAlgebraicallyClosedCoefficients.unitor l Ω W E

attribute [local irreducible] stageUnit commonStagePullbackComparison
  operationStageTransitionIso GeneralAlgebraicallyClosedCoefficients.unitor

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage

private theorem comparison_self (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    commonStagePullbackComparison l Ω f P P.stage le_rfl ≪≫
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u}
        l Ω P.stage) f).mapIso ((stageUnit l Ω Y P.stage).app P.obj) =
      (stageUnit l Ω X P.stage).app (commonStagePullbackObject l Ω f P).obj := by
  unfold stageUnit
  exact commonStagePullbackComparison_self_unit l Ω f P

/-- The normalized common-stage compositor word equals the rational pullback
composition map at the original coefficient stage.
Source: blueprint purity/trace equivariance Step 1, normalized composition.
(blueprint: lem-pur-common-stage-compositor-word).
Proof: apply the generic normalized-composition cancellation theorem to the three
common-stage boundary comparisons. Their self-transition equations come from the
coefficient-unit theorem. Rational pullback naturality supplies the composition
isomorphism component. -/
-- The component is now assembled at the literal stage.
theorem commonStageCompositor_word (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    ((commonStagePullbackComparison l Ω (f ≫ g) P P.stage le_rfl).hom ≫
      (pullbackTensorRationalComposition l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g f
        (P.toStage le_rfl)).hom ≫
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).map
        (commonStagePullbackComparison l Ω g P P.stage le_rfl).inv ≫
      (commonStagePullbackComparison l Ω f
        (commonStagePullbackObject l Ω g P) P.stage le_rfl).inv) =
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T
        (le_refl P.stage)).map
        (pullbackTensorRationalComposition l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g f P.obj).hom := by
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage
  let G := stagePull l Ω P.stage g
  let F := stagePull l Ω P.stage f
  let H := stagePull l Ω P.stage (f ≫ g)
  let α : H ≅ G ⋙ F := NatIso.ofComponents
    (fun K ↦ stageComp l Ω P.stage f g K)
    (fun {_ _} a ↦ commonStageRationalComposition_naturality l E g f a)
  have he := @commonStageNormalizedComposition
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z P.stage)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y P.stage)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X P.stage)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Z P.stage)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y P.stage)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X P.stage)
    G F H
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T (le_refl P.stage))
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T (le_refl P.stage))
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T (le_refl P.stage))
    (stageUnit l Ω Z P.stage) (stageUnit l Ω Y P.stage) (stageUnit l Ω X P.stage)
    α P.obj
    (commonStagePullbackComparison l Ω (f ≫ g) P P.stage le_rfl)
    (commonStagePullbackComparison l Ω g P P.stage le_rfl)
    (commonStagePullbackComparison l Ω f (commonStagePullbackObject l Ω g P)
      P.stage le_rfl)
    (comparison_self l Ω (f ≫ g) P) (comparison_self l Ω g P)
    (comparison_self l Ω f (commonStagePullbackObject l Ω g P))
  exact he

end WeilConjectures
