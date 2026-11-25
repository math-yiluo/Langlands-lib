/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData

/-! # Identification of the prescribed finite scalar unit

Source: Stacks 06YY and 07A4.
(blueprint: lem-coef-finite-scalar-section).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionExtension
  coefficientTotalTensor
  coefficientFiniteReductionModel coefficientLocalizedCounitModel

attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  CategoryTheory.uniformProd
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

attribute [local semireducible] scalarReductionExtension
attribute [local implicit_reducible] scalarReductionExtension

-- Match the recorded adjunction unit with the explicit scalar generator.
/-- The prescribed finite scalar adjunction unit is the pure scalar section at 1.
Source: Stacks 03CZ and 06YY.
(blueprint: lem-coef-finite-scalar-section). -/
theorem coefficientFiniteScalarSection (n : ℕ)
    (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ringedFiniteFreeScalarSection.{t+1, t, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingProjectionUnrestricted l E W n)
        (scalarReductionExtension l E W n)
        (fun M ↦ by
          with_unfolding_all exact (scalarReductionExistence l E W n).choose_spec.choose M)
        M U 1 x = coefficientIntegralScalarUnitSection l E W n M U x := by
  have h := (scalarReductionExtension_adjunction l E W n).choose_spec M U x
  unfold coefficientIntegralScalarUnitSection coefficientRestrictionSection
    coefficientOrdinaryScalarAdjunction ringedFiniteFreeScalarSection
  with_unfolding_all exact h.symm

end WeilConjectures
