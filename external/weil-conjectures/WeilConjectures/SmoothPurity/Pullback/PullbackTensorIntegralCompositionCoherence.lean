/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.Integral.IntegralPullbackTensorCompositionReduced

/-! Integral coefficient component of pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; this is the integral part of
`lem-pur-pullback-tensor-composition-coherence`.
(blueprint: lem-pur-pullback-tensor-composition-coherence)

The proof uses flat-term K-flat representatives in the normalized quotient tower.
The finite pullback/tensor composition square is the pure-tensor calculation; it
is preserved by quotient transitions and therefore by the completed realization.
The coherent reduction identifies the resulting map with the prescribed integral
comparison, and fully faithful reduction reflects the equality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Integral component of higher pullback/tensor composition coherence.
Source: Stacks 07A4 and 0941; quotient-tower composition calculation.
(blueprint: lem-pur-pullback-tensor-composition-coherence). -/
theorem pullbackTensorIntegralCompositionCoherence {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    ∀ M N : sfIntegralConstructibleCategory l E Y,
      canonicalIntegralPullbackTensor_composition l E f h M N := by
  intro M N
  change _ = _
  have hfaithful := (integralSystemReduction_fullyFaithful l E Z).2
  apply hfaithful.map_injective
  exact integralPullbackTensorCompositionReduced l E f h M N

end WeilConjectures
