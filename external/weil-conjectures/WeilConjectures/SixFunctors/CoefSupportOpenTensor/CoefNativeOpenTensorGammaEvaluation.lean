/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefOpenTensorEvaluationData
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorGammaEvaluationComponent

/-! # Evaluation compatibility of native open tensor models

Source: Stacks 0GL1, 07A4; support-open-tensor steps 5--6.
(blueprint: lem-coef-native-open-tensor-gamma-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- For fixed native open tensor representatives, exact finite evaluation identifies
the system gamma with the canonical finite gamma. This is the generator calculation:
both composites are induced by the same ordinary pure-tensor map, and exact evaluation
preserves the open unit, restriction comparison, total summands and K-flat pullback.
Source: Stacks 0GL1 and 07A4; support-open-tensor proof steps 5--6.
(blueprint: lem-coef-native-open-tensor-gamma-evaluation).
-/
theorem nativeOpenTensorGammaEvaluation {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z)
    (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors)
    (On : ∀ n : ℕ, FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors n) :
    GammaEvaluation l E j SX SZ O On := by
  intro n U L
  exact nativeOpenTensorGammaEvaluation_component l E j SX SZ O On n U L

end WeilConjectures.CoefSupportOpenTensor
