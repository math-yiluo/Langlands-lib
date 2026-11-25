/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorRationalCompositionCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageCompositionFiniteRepresentative

/-! Common-stage coefficient component of pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; this is the common-stage part of
`lem-pur-pullback-tensor-composition-coherence`.
(blueprint: lem-pur-pullback-tensor-composition-coherence)

Choose one finite coefficient field containing the stages of both inputs and all
objects in the diagram. The representative formulas for common-stage pullback,
tensor, comparison, and composition reduce both routes to the rational equation.
The endpoint comparison maps are the same on both routes and the intermediate
ones cancel; passage to the colimit Hom group then gives the claimed equality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Common-stage component of higher pullback/tensor composition coherence.
Source: Stacks 07A4 and 0941; finite-stage representative descent.
(blueprint: lem-pur-pullback-tensor-composition-coherence). -/
theorem pullbackTensorCommonStageCompositionCoherence {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    ∀ M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      canonicalCommonStagePullbackTensor_composition l Ω f h M N := by
  intro M N
  obtain ⟨L, hA, hB, r, hl, hr⟩ :=
    commonStageCompositionFiniteRepresentative l Ω f h M N
  exact eq_of_heq (hl.trans hr.symm)

end WeilConjectures
