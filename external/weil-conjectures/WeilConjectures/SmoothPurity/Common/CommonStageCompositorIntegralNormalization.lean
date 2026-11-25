/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Common.CommonStageCompositorRepresentative

/-! # Integral normalization of the common-stage compositor

Source: purity/trace equivariance proof Step 1, canonical pullback compositors.
(blueprint: lem-pur-common-stage-compositor-integral-normalization).
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

private theorem normalization_map_heq
    {C B : Type*} [Category* C] [Category* B] (F : C ⥤ B)
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

/-- The common-stage compositor is the localized integral compositor at the
object's original coefficient stage.
Source: blueprint purity/trace equivariance Step 1, normalized pullback composition.
(blueprint: lem-pur-common-stage-compositor-integral-normalization).
Proof: the literal-stage representative theorem identifies the common compositor
with the inclusion of its rational compositor. The rational compositor's defining
normalization identifies its hom with the localization of the integral compositor.
The rational pullback object formulas identify both endpoints; functoriality of
heterogeneous equality carries this identification through the stage inclusion. -/
theorem commonStageCompositor_integral (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    HEq (pullbackTensorCommonComposition l Ω g f P).hom
      ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) P.stage).map
        (pullbackTensorRationalComposition l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g f P.obj).hom) := by
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage
  have hc := (pullbackTensorCommonComposition_existsUnique l Ω g f P).exists.choose_spec
    P.stage le_rfl
  have hrep := commonStageCompositor_representative l Ω f g P
  have hrep := commonStageCompositor_representative l Ω f g P
  exact hc.trans (heq_of_eq hrep)

end WeilConjectures
