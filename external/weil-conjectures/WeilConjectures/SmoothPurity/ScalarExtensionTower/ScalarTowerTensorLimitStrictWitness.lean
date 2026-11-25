/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData

/-! # Strict representatives for the scalar/tensor limit transport

Source: Stacks 07A4 and 0941; realization step 8 of
`lem-pur-scalar-extension-tower-coherence`.

This module records the strict representative equation supplied by
`DerivedSigmaModel`.  It deliberately contains no completed tensor, total
limit, or constructible object; those are assembled in the transport module.
(blueprint: stage3-pur-scalar-tensor-limit-strict-witness)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralComparisonDerivedSequenceScalar
  integralComparisonSequenceScalarModel
open scoped ChangeOfRings

/-- A strict scalar/tensor comparison at one pair of good cochain complexes.

The equation is exactly the representative equation in `DerivedSigmaModel`.
It is a lower-level datum: it mentions only cochain complexes and the strict
tensor models, and has no localization or completed constructible objects.
Source: Stacks 07A4 and 0941 (blueprint: stage3-pur-scalar-tensor-limit-strict-witness).
-/
structure StrictTensorWitness (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    where
  P : Complex l E W
  Q : Complex l E W
  hP : Good l E W P
  hQ : Good l E W Q
  hsP : Good l L W ((scalar l E L ι W).obj P)
  hsQ : Good l L W ((scalar l E L ι W).obj Q)
  equation : DerivedSigmaModel l E L ι W SE SL α

/-- Extract the strict representative datum from `DerivedSigmaModel`.
Source: Stacks 07A4 and 0941 (blueprint: stage3-pur-scalar-tensor-limit-strict-witness).
-/
theorem strictTensorWitness_of_derivedSigmaModel (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (hα : DerivedSigmaModel l E L ι W SE SL α)
    (P Q : Complex l E W) (hP : Good l E W P) (hQ : Good l E W Q) :
    ∃ w : StrictTensorWitness l E L ι W SE SL α, w.P = P ∧ w.Q = Q := by
  obtain ⟨hsP, hsQ, _heq⟩ := hα P Q hP hQ
  refine ⟨⟨P, Q, hP, hQ, hsP, hsQ, hα⟩, rfl, rfl⟩

end WeilConjectures.ScalarExtensionTower
