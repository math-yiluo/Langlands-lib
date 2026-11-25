/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitExistence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitUniqueness

/-! Integral unit coherence for the completed pullback tensor comparison.

Source: Stacks Project, Tags 07A4 and 0941; the integral part of
`lem-pur-pullback-tensor-unit-coherence`.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence)

The existence and uniqueness halves are supplied by the normalized reduction
construction and the cancellation lemma, respectively.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

theorem pullbackTensorIntegralUnitCoherence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    canonicalIntegralPullbackTensor_unit l E f := by
  unfold canonicalIntegralPullbackTensor_unit
  obtain ⟨ε, hε⟩ := canonicalIntegralPullbackTensor_unit_exists l E f
  refine ⟨ε, hε, ?_⟩
  intro δ hδ
  exact canonicalIntegralPullbackTensor_unit_unique l E f ε δ hε hδ |>.symm

end WeilConjectures
