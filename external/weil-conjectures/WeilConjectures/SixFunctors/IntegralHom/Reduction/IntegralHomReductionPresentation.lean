/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionComponents
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionNormalization

/-! # One normalized integral reduction presentation

This is the fixed-level coefficient-extension part of
`lem-sf-integral-hom-models-exist`.

Source: Stacks Tags 07A4 and 07A6; blueprint order 2478, proof step 3
(blueprint: lem-sf-integral-hom-models-exist-reduction).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- A normalized reduction presentation exists at each fixed quotient level.

Source: Stacks Tags 07A4 and 07A6; blueprint order 2478, proof step 3
(blueprint: lem-sf-integral-hom-models-exist-reduction).

Proof: ordinary scalar extension and restriction have unit `x ↦ 1 ⊗ x`.
Balanced tensor associativity identifies the comparison with multiplication of
coefficient factors. Apply the left-derived universal property to the same
source tensor presentation; the resulting counit square is the normalization
field of `ReductionPresentation`.
-/
theorem reduction_presentation_exists_at
    (a : TensorPresentation.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ) :
    Nonempty (ReductionPresentation l E Y D hl a n) := by
  obtain ⟨target⟩ := reduction_target_exists l E Y n
  obtain ⟨m, _⟩ := reduction_normalization_exists l E Y D hl a n target
  exact ⟨m⟩

end WeilConjectures.IntegralHom
