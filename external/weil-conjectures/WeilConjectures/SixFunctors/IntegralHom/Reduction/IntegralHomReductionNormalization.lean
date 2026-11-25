/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionNormalizationData

/-! # Normalization component of an integral reduction presentation

This is the sectionwise and derived counit square required by
`ReductionPresentation.normalization`.
(blueprint: lem-sf-integral-hom-reduction-normalization).
(blueprint: lem-sf-integral-hom-models-exist-reduction-normalization).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local irreducible] reductionCounit reductionUnit integralDerivedReduction
  integralReductionChangeOfRings

/-- A normalized comparison exists for a fixed target.

Source: Stacks Tags 07A4 and 07A6; blueprint order 2478, proof step 3.
Proof: apply scalar extension and restriction to K-flat representatives. The
ordinary unit is `x ↦ 1 ⊗ x`; balanced tensor associativity gives the invertible
chain comparison and its pure-tensor equation. The derived counit square follows
from the left-derived universal property and the canonical tensor pullback.
-/
theorem reduction_normalization_exists
    (a : TensorPresentation.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ)
    (target : TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) :
    Nonempty {m : ReductionPresentation l E Y D hl a n //
      m.target = target} := by
  letI : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  letI : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  letI : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  letI : HasDerivedCategory (Modules.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (Modules.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) := HasDerivedCategory.standard _
  obtain ⟨mu, hmu⟩ := @reduction_normalization_data_exists l _ E _ _ _ Y D hl
    (essentiallySmallSelf _) (integralCoefficientAbSheafify Y)
    (integralCoefficientAbLocallyBijective Y) a n target
  exact ⟨⟨target, mu, hmu⟩, rfl⟩

end WeilConjectures.IntegralHom
