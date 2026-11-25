/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorRationalUnitCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageUnitCoherence

/-! # Units of the higher pullback tensor comparisons

Source: Stacks Project, Tags 07A4 and 0941, and the recorded blueprint
coefficient conventions.
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

-- Cache the existing category instances while comparing finite-stage arrows.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

attribute [local irreducible] Scheme.residueField Padic
  canonicalIntegralPullbackTensor_composition canonicalRationalPullbackTensor_composition
  canonicalCommonStagePullbackTensor_composition canonicalIntegralPullbackTensor_unit
  canonicalRationalPullbackTensor_unit canonicalCommonStagePullbackTensor_unit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The prescribed higher tensor comparisons preserve the normalized tensor units.

Source: recorded blueprint, derived-pullback-tensor-hom, completed structural diagrams
and coefficient descent; Stacks 03EL, 07A4 and 0941.
(blueprint: lem-pur-pullback-tensor-unit-coherence).

Proof: At the whole-system level inverse image sends the coefficient-ring unit
to the coefficient-ring unit. The multiplication maps on pure tensors show both
left and right unit equations, including their quotient transitions. The actual
reconstruction counit identifies the integral units and unitors with these system
units and unitors. Lift the system unit comparison along fully faithful coherent
reduction, conjugating by the tensor and unit reduction isomorphisms. Faithfulness
gives both unit equations. Uniqueness follows by evaluating the left equation at
the source unit and canceling the invertible comparison and unitor; tensoring with
the target unit is faithful because its unitor is a natural isomorphism.
Localize this integral comparison and the two equations. The normalized object
formulas and bilinear arrow formulas give the prescribed rational equations;
the same cancellation gives rational uniqueness. Finally, represent the source
and target common-stage units at one finite field. The prescribed scalar unit
comparison identifies them with rational units. Conjugate the rational pullback
unit comparison by these identifications. Scalar compatibility makes its class
independent of the finite field. Both common-stage unit equations are represented
by the rational equations at a common larger field. To show uniqueness, apply the
same left-unit cancellation in the common-stage category. -/
theorem pullbackTensorUnitCoherence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    canonicalIntegralPullbackTensor_unit l E f ∧
      canonicalRationalPullbackTensor_unit l E f ∧
        canonicalCommonStagePullbackTensor_unit l Ω f := by
  exact ⟨pullbackTensorIntegralUnitCoherence l E f,
    pullbackTensorRationalUnitCoherence l E f,
    pullbackTensorCommonStageUnitCoherence l Ω f⟩

end WeilConjectures
