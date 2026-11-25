/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.SmoothPurity.Supporting.Scalar.OrdinaryScalarEvaluationUnit
import WeilConjectures.SmoothPurity.Scalar.ScalarCochainEvaluationOfUnit

/-! # Evaluation of the scalar-extension cochain counit

Source: Stacks 03D7, 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
-- Keep the common constant-sheaf and localization constructions abstract when
-- comparing the generic evaluation with its coefficient-system specialization.
attribute [local irreducible] constantSheaf CategoryTheory.Functor.leftAdjoint
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

private theorem evaluation_specialization (n : ℕ) :
    SemilinearSections.evaluation.{t + 1, t, max (t + 1) u}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n =
      coefficientSequenceEvaluation l E W n := rfl

variable (A : CoefficientExtensionSystems l E L ι W)

/-- Zero preservation of system scalar extension followed by finite evaluation.
Source: Stacks 06YY (blueprint: stage3-pur-scalar-cochain-evaluation). -/
theorem coefficientExtensionSystemEvaluationZero (n : ℕ) :
    (A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n).PreservesZeroMorphisms :=
  letI := coefficientScalarModelZero A.scalar
  letI : (coefficientSequenceEvaluation l L W n).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (coefficientSequenceEvaluation_additive l L W n)
  Functor.preservesZeroMorphisms_comp _ _

/-- Zero preservation of finite evaluation followed by scalar extension.
Source: Stacks 06YY (blueprint: stage3-pur-scalar-cochain-evaluation). -/
theorem coefficientExtensionEvaluationFiniteZero (n : ℕ) :
    (coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E).PreservesZeroMorphisms :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  letI : (coefficientSequenceEvaluation l E W n).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (coefficientSequenceEvaluation_additive l E W n)
  Functor.preservesZeroMorphisms_comp _ _

/-- The ordinary scalar evaluation comparison respects the actual adjunction units.
Source: Stacks 03D7 and 07A6
(blueprint: stage3-pur-scalar-cochain-evaluation). -/
@[irreducible] def IsCoefficientScalarEvaluationUnit
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E) : Prop :=
  ∀ (n : ℕ) (M : coefficientSequenceModules l E W),
    (coefficientSequenceEvaluation l E W n).map
        (A.scalar.ordinaryAdjunction.unit.app M) ≫
      (SemilinearSections.restrictionEvaluation_existsUnique.{t + 1, t, max (t + 1) u}
        (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W)
        (coefficientExtensionQuotient_naturality l E L ι W) n).exists.choose.hom.app
          (A.scalar.model.E.obj M) ≫
      (SemilinearSections.res (integralScalarQuotientSheafMap l E L ι W n)).map
        ((ρ n).hom.app M) =
      (A.levels n).ordinaryAdjunction.unit.app
        ((coefficientSequenceEvaluation l E W n).obj M)

/-- Ordinary evaluation and the universal scalar cochain counit commute.

Source: Stacks sites-modules.tex, lemma-adjoint-pullback-pushforward-modules
(03D7), and sites-cohomology.tex, derived base change (06YY) and
lemma-adjoint (07A6); step 2 of stage3-pur-extension-strict-derived-comparison.
(blueprint: stage3-pur-scalar-cochain-evaluation).

Proof: transpose the identity-on-sections restrictionEvaluation through the
ordinary scalar adjunctions. On local tensors the inverse comparison sends
b tensor x to b tensor x. These maps are inverse by tensor-generator
extensionality and sheafification, hence define rho and satisfy its unit equation.
Apply them degreewise. For a K-flat system complex, transpose both sides of the
claimed derived equation. A.transpose_evaluation, the scalar transpose_model at
system and finite levels, and the ordinary unit equation identify the transposes.
Evaluation preserves K-flatness, so both scalar computation formulas apply.
For an arbitrary complex choose an epimorphic flat-term K-flat resolution.
Naturality of the two universal cochain counits reduces the equation to that
resolution. Its image under evaluation is a quasi-isomorphism; localization and
the finite derived extension invert it, so cancellation gives the equation for
the original complex. No equality of derived system morphisms is inferred from
finite evaluation. Zero complexes and n=0 are included. -/
theorem coefficientScalarCochainEvaluation :
    letI := coefficientScalarModelZero A.scalar
    ∃ ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
        coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E,
      IsCoefficientScalarEvaluationUnit l E L ι W A ρ ∧
      ∀ (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ),
        letI := coefficientExtensionSystemEvaluationZero l E L ι W A n
        letI := coefficientExtensionEvaluationFiniteZero l E L ι W A n
        (coefficientSequenceDerivedEvaluation l L W n).map (A.scalar.model.ε.app C) ≫
            (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
              ((A.scalar.model.E.mapHomologicalComplex (.up ℤ)).obj C) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ρ n) (.up ℤ)).hom.app C) =
          (A.evaluation n).hom.app (DerivedCategory.Q.obj C) ≫
            (A.levels n).T.map
              ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C) ≫
            (A.levels n).model.ε.app
              (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C)
      := by
  let := coefficientScalarModelZero A.scalar
  obtain ⟨ρ, hρ⟩ := ordinaryScalarEvaluationUnit.{t + 1, t, u}
    (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (integralCoefficientCommRingSheaf l L W)
    (coefficientSequenceCommRingTransition l E W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W)
    (coefficientExtensionQuotient_naturality l E L ι W) A
  refine ⟨ρ, ?_, ?_⟩
  · unfold IsCoefficientScalarEvaluationUnit
    intro n M
    simpa only [evaluation_specialization] using hρ n M
  · intro C n
    simpa only [SemilinearSections.e, evaluation_specialization] using
      scalarCochainEvaluation_of_unit.{t + 1, t, u}
      (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (integralCoefficientCommRingSheaf l L W)
      (coefficientSequenceCommRingTransition l E W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W) A n (ρ n) (hρ n) C

end WeilConjectures
