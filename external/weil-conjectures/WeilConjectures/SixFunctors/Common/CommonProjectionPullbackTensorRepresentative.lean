/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison

/-! # Finite-stage representative of the common pullback tensor

Source: thm-sf-pf-field.proof.md, Compatibility; the representative formula
in `canonicalCommonStagePullbackTensor_existsUnique`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

/-- The canonical common pullback/tensor comparison is represented at every
finite coefficient stage by `pullbackTensorAtCommonStage`.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-pullback-tensor-representative).

Proof: unfold the unique-choice definition of the canonical comparison and apply
the representative clause of `canonicalCommonStagePullbackTensor_existsUnique`.
The statement is strictly pointwise at one finite stage and supplies the
finite-stage equation used by the coefficient comparison square. -/
theorem canonicalCommonStagePullbackTensor_formula
    {l : ℕ} [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : (commonStageTensorObject l Ω Y P Q).stage ≤ L) :
    HEq (canonicalCommonStagePullbackTensor l Ω f P Q).hom
      (ofHom (commonStagePullbackObject l Ω f
        (commonStageTensorObject l Ω Y P Q))
        (commonStageTensorObject l Ω X
          (commonStagePullbackObject l Ω f P)
          (commonStagePullbackObject l Ω f Q))
        L h h (pullbackTensorAtCommonStage l Ω f P Q L h).hom) := by
  change HEq (pullbackTensorUniqueChoice
      ((canonicalCommonStagePullbackTensor_existsUnique l Ω f P Q)) ).hom _
  exact (canonicalCommonStagePullbackTensor_existsUnique l Ω f P Q).exists.choose_spec L h

end WeilConjectures
