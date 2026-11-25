/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Common.CommonProjectionTensorComparison
import all Mathlib.Logic.Small.Defs
/-! # Normalization of the supplied tensor comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] rationalDerivedTensor rationalDerivedPullback
  commonStageDerivedTensor commonStageDerivedPullback

/-- The supplied inclusion tensorator is the canonical tensorator in normalized coordinates.
Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-common-projection-tensor-comparison-normalization).
Proof: the coefficient invertibility instances are unique. Substitute their
identity, unfold the supplied tensorator, and remove its three equality transports. -/
theorem commonProjectionTensorComparison_heq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X : SixFunctorSpace D)
    [hX : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)] :
    HEq (commonProjectionTensorComparison H E X)
      (commonInclusionTensorComparison C.l C.Qbar X.obj.left E) := by
  have hi : hX = (fun x ↦ (sixFunctorSpace_coefficient_invertible C X x).some) :=
    Subsingleton.elim _ _
  cases hi
  unfold commonProjectionTensorComparison
  iterate 3 apply (cast_heq _ _).trans
  rfl

end WeilConjectures
