/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackCoefficientUnit
import WeilConjectures.SmoothPurity.Common.CommonStageCompositorWord
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
/-- At the original coefficient stage the common compositor is the inclusion of
its rational compositor, with all three boundary comparisons retained.
Source: blueprint purity/trace equivariance Step 1, normalized composition.
(blueprint: lem-pur-common-stage-compositor-representative).
Proof: rational compositor naturality follows by tensor induction from integral
naturality and the prescribed scalar-localization formulas. Apply the literal-stage
coefficient-unit equation to each boundary comparison. Substitute these three
equations; naturality cancels the middle unit and the remaining target unit
conjugation is exactly the self-transition of the rational compositor. Passing to
the representative class gives its inclusion map. No stage enlargement is needed. -/
theorem commonStageCompositor_representative (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    GeneralAlgebraicallyClosedCoefficients.ofHom
      (commonStagePullbackObject l Ω (f ≫ g) P)
      (commonStagePullbackObject l Ω f (commonStagePullbackObject l Ω g P))
      P.stage le_rfl le_rfl
      ((commonStagePullbackComparison l Ω (f ≫ g) P P.stage le_rfl).hom ≫
        (pullbackTensorRationalComposition l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g f
            (P.toStage le_rfl)).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).map
          (commonStagePullbackComparison l Ω g P P.stage le_rfl).inv ≫
        (commonStagePullbackComparison l Ω f (commonStagePullbackObject l Ω g P)
          P.stage le_rfl).inv) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) P.stage).map
        (pullbackTensorRationalComposition l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g f P.obj).hom := by
  exact (congrArg (fun a ↦ GeneralAlgebraicallyClosedCoefficients.ofHom
    (commonStagePullbackObject l Ω (f ≫ g) P)
    (commonStagePullbackObject l Ω f (commonStagePullbackObject l Ω g P))
    P.stage le_rfl le_rfl a)
    (commonStageCompositor_word l Ω f g P)).trans rfl

end WeilConjectures
