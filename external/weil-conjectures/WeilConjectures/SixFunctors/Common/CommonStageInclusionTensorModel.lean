/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

/-! # Finite-stage models of the common tensor

Source: thm-sf-pf-field.proof.md, Compatibility and the common coefficient field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear
  rationalDerivedTensor commonStageTensorComparison operationStageTransitionIso
  sfRationalScalarExtension sfConstructibleIntegralScalarExtension
  sfIntegralScalarComp sfIntegralScalarUnit

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
  [∀ x : W, Invertible (l : W.residueField x)] (E : Index l Ω)

set_option backward.isDefEq.respectTransparency false in
/-- The common tensor on two included objects, extended back to their finite stage.
Source: thm-sf-pf-field.proof.md, common finite coefficient field paragraph
(blueprint: def-sf-common-stage-inclusion-tensor-model). -/
@[irreducible] def commonInclusionTensorModel (K L : Stage l Ω W E) :
    (commonStageDerivedTensor l Ω W).obj
        ((inclusion (l := l) (Ω := Ω) (Y := W) E).obj K,
          (inclusion (l := l) (Ω := Ω) (Y := W) E).obj L) ≅
      (inclusion (l := l) (Ω := Ω) (Y := W) E).obj
        ((rationalDerivedTensor l (Coefficient.{u} l Ω E) W).obj
          (((stageSystem l Ω W).T (le_rfl : E ≤ E)).obj K,
           ((stageSystem l Ω W).T (le_rfl : E ≤ E)).obj L)) := by
  let I := inclusion (l := l) (Ω := Ω) (Y := W) E
  let P := I.obj K
  let Q := I.obj L
  have h : (commonStageTensorObject l Ω W P Q).stage ≤ E := by
    change E.val ⊔ E.val ≤ E.val
    exact sup_le le_rfl le_rfl
  exact eqToIso ((commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1 P Q) ≪≫
    (stageSystem l Ω W).isoToStage (commonStageTensorObject l Ω W P Q) h ≪≫
    I.mapIso (commonStageTensorComparison l Ω W P Q E h)

end WeilConjectures
