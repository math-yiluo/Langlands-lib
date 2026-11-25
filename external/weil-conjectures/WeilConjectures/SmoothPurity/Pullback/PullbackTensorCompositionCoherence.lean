/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralCompositionCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorRationalCompositionCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageCompositionCoherence

/-! # Composition of the higher pullback tensor comparisons

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

/-- Pullback composition preserves the prescribed tensor comparison at all higher levels.

Source: recorded blueprint, derived-pullback-tensor-hom, integral completed quotient
realization and rational/common-stage descent; Stacks 07A4 and 0941.
(blueprint: lem-pur-pullback-tensor-composition-coherence).

Proof: On flat-term K-flat representatives the finite pullback compositor and
comparison send a pure tensor to the same pair of pulled-back sections, with the
same signed differential. These equalities respect every quotient transition.
The completed quotient realization identifies their derived limits with the actual
integral comparison and adjunction-normalized compositor. Coherent reduction and
its faithfulness identify the specified integral diagram with this system diagram.
For rational objects, apply the localization functor to this equality. The object
and morphism normalization clauses identify the images of the three comparisons
and the compositor with their prescribed rational versions; bilinearity identifies
the tensor of the two compositor maps. For common-stage inputs, choose one finite
field containing both inputs and all objects in the diagram. The representative
formulas express both composites by the rational diagram, conjugated by the same
endpoint comparisons. Intermediate comparisons cancel. The rational equality
therefore gives equality of the two classes, without any injectivity assumption
on coefficient transition maps. -/
theorem pullbackTensorCompositionCoherence {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    (∀ M N : sfIntegralConstructibleCategory l E Y,
      canonicalIntegralPullbackTensor_composition l E f h M N) ∧
    (∀ M N : sfRationalConstructibleCategory l E Y,
      canonicalRationalPullbackTensor_composition l E f h M N) ∧
    (∀ M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      canonicalCommonStagePullbackTensor_composition l Ω f h M N) := by
  refine ⟨?_, ?_, ?_⟩
  · exact pullbackTensorIntegralCompositionCoherence l E f h
  · exact pullbackTensorRationalCompositionCoherence l E f h
  · exact pullbackTensorCommonStageCompositionCoherence l Ω f h

end WeilConjectures
