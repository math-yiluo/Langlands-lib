/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientModel
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorDescent
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionPresentation

/-! # Strict tensor normalization of reduction from the ordinary quotient model

Source: Stacks 06YS, 06YY, 07A4 and 0941.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  CoefficientClosedStructure.tensor coefficientTotalTensor
  coefficientIntegralTensorModelIso coefficientSystemTensorModelIso
  coefficientScalarTensorIso coefficientEvaluationTensorIso

/-- A strict tensor comparison of the ordinary quotient-system functor whose finite
evaluations are the scalar tensor comparisons gives a reduction tensor comparison with
the simultaneous representative normalization.
Source: Stacks 07A4, proof of lemma-pullback-tensor-product, and 0941. -/
theorem reductionTensorNormalization_of_quotientTensor (M : OrdinaryModel l E W)
    (R : CoefficientDerivedSystemReduction l E W)
    (b : coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ M.quotient l E W ≅
      (M.quotient l E W).prod (M.quotient l E W) ⋙
        coefficientTotalTensor.{u, t + 1, t} (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W))
    (hb : ∀ (n : ℕ) (P Q : CochainComplex (scalarReductionSource l E W) ℤ),
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
          (b.hom.app (P, Q)) ≫
        (coefficientEvaluationTensorIso l E W n ((M.quotient l E W).obj P)
          ((M.quotient l E W).obj Q)).hom ≫
        (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
          (Prod.mkHom ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P)
            ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q)) =
      (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app
          ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≫
        (coefficientScalarTensorIso l E W n P Q).hom)
    (hpres : ∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
      P.IsKFlatIndependentCoefficients → (∀ p : ℤ, (P.X p).IsFlatOnSite) →
        CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E W) ((M.quotient l E W).obj P)) :
    ∃ μ : R.integralClosed.tensor ⋙ R.reduction ≅
      R.reduction.prod R.reduction ⋙ R.systemClosed.tensor,
      CoefficientReductionTensorNormalization l E W { R with reductionTensor := μ } := by
  classical
  obtain ⟨ε, -, hε, hhom⟩ := reductionComparison_exists l E W M R.reduction R.adjunction
  obtain ⟨μ, hμ⟩ := reductionTensor_descent l E W M R.toCoefficientDerivedSystemTensors
    R.reduction ε hε b hpres
  refine ⟨μ, ?_⟩
  intro P Q hP hQ fP fQ
  have := hε P hP fP
  have := hε Q hQ fQ
  have hPQ := flatTermKFlat_totalTensor l E W P Q ⟨hP, fP⟩ ⟨hQ, fQ⟩
  have := hε _ hPQ.1 hPQ.2
  let κ (X : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :=
    (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app X
  refine ⟨(M.quotient l E W).obj P, (M.quotient l E W).obj Q, (M.quotient l E W).obj _,
    hpres P hP fP, hpres Q hQ fQ, asIso (ε.app P), asIso (ε.app Q), asIso (ε.app _),
    κ P, κ Q, κ _, b.hom.app (P, Q), ?_, ?_, ?_, ?_, ?_⟩
  · exact strictReductionTensorPresentation l E W M R.reduction R.adjunction
      R.reductionEvaluation R.unit_projection ε hhom P hP fP
  · exact strictReductionTensorPresentation l E W M R.reduction R.adjunction
      R.reductionEvaluation R.unit_projection ε hhom Q hQ fQ
  · exact strictReductionTensorPresentation l E W M R.reduction R.adjunction
      R.reductionEvaluation R.unit_projection ε hhom _ hPQ.1 hPQ.2
  · intro n
    unfold CoefficientComparisonEquation
    exact hb n P Q
  · exact hμ P Q hP hQ fP fQ

end WeilConjectures.OrdinaryQuotient
