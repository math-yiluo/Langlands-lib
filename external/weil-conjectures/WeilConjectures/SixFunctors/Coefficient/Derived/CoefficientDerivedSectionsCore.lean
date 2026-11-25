/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsCoreData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsCoreEquations

/-! A strict subpackage of the normalized coefficient-sections data.
(blueprint: lem-coef-derived-sections-normalization-core)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

def CoefficientSectionsLimitResolutionEquationCore
    (κ : coefficientSequenceLimit l E W ⋙ coefficientIntegralSections l E W ≅
      coefficientSequenceDerivedRestriction l E W ⋙
        (coefficientTowerSections l E W).rightDerivedFunctor ⋙
          coefficientMappingLimit.{max u (t + 1)}) : Prop :=
  ∀ (K : CochainComplex (coefficientSequenceModules l E W) ℤ),
    CoefficientComparisonEquation
      (coefficientGlobalLimitLeftComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      ((coefficientIntegralSections l E W).map
          ((coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))
      (κ.hom.app (DerivedCategory.Q.obj K))
      (coefficientGlobalLimitRightComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      (coefficientMappingLimit.{max u (t + 1)}.map
        ((coefficientTowerSections l E W).rightDerivedFunctor.map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))

structure CoefficientDerivedSectionsCore
    (R : CoefficientDerivedSystemReduction l E W) where
  toCoefficientDerivedSystemScalarCoherence :
    CoefficientDerivedSystemScalarCoherence l E W
  systemSectionsEvaluation : ∀ n : ℕ,
    coefficientSequenceDerivedRestriction l E W ⋙
        (coefficientTowerSections l E W).rightDerivedFunctor ⋙
          coefficientMappingEvaluation.{max u (t + 1)} n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteSections l E W n
  globalLimit : coefficientSequenceLimit l E W ⋙ coefficientIntegralSections l E W ≅
    coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
        coefficientMappingLimit.{max u (t + 1)}
  globalLimit_model : CoefficientSectionsLimitResolutionEquationCore l E W globalLimit
  sections_projection : ∀ (M : coefficientSequenceDerived l E W) (n : ℕ),
    globalLimit.hom.app M ≫
        (coefficientMappingProjection.{max u (t + 1)} n).app
          ((coefficientSequenceDerivedRestriction l E W ⋙
            (coefficientTowerSections l E W).rightDerivedFunctor).obj M) ≫
        (systemSectionsEvaluation n).hom.app M =
      (coefficientIntegralSections l E W).map
          ((coefficientSequenceProjection l E W n).app M) ≫
        (toCoefficientDerivedSystemScalarCoherence.scalarSections n).hom.app
          ((coefficientSequenceDerivedEvaluation l E W n).obj M)

/-- The construction is the first four fields of the requested package.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941.
The proof transports normalized global-sections and limit comparisons through the
coefficient tower, then records their finite projections.
(blueprint: lem-coef-derived-sections-normalization-core) -/
theorem coefficientDerivedSectionsCore
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R) :
    Nonempty (CoefficientDerivedSectionsCore l E W R) := by
  obtain ⟨D⟩ := coefficientDerivedSectionsCoreData l E W R hF
  obtain ⟨D, hmodel, hprojection⟩ := coefficientDerivedSectionsCoreEquations
    l E W R hF D
  refine ⟨{
    toCoefficientDerivedSystemScalarCoherence := D.scalar
    systemSectionsEvaluation := D.systemSectionsEvaluation
    globalLimit := D.globalLimit
    globalLimit_model := ?_
    sections_projection := ?_ }⟩
  · simpa only [CoefficientDerivedSectionsCoreResolutionEquation,
      CoefficientSectionsLimitResolutionEquationCore] using hmodel
  · exact hprojection

end WeilConjectures
