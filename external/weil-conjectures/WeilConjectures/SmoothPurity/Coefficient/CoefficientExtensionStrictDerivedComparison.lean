/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.SmoothPurity.Coefficient.CoefficientReductionNaturalCochainComparison
import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryAssociationChain
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction

/-! # Derived comparison for an already strict coefficient tensor model

Source: Stacks 03EK, 03D7, 06YY, 07A6 and 0941; the integral-operations
coefficient-extension proof, step 2 of stage3-pur-extension-strict-representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

/-- A strict tensor model computes the specified composite derived extension.

Source: Stacks 06YY and 07A6; step 2 of
stage3-pur-extension-strict-representatives
(blueprint: stage3-pur-extension-strict-derived-comparison).

Proof: form the ordinary quotient tensor system over the completed E-coefficients
and its tensor/limit adjunction (the ringed sequence projection). Transpose its
ordinary unit through reduction and scalar restriction. Derive this composite
adjunction using a flat-term K-flat resolution; the scalar restriction functors
are exact. The normalized units make the finite evaluation of this comparison
SE.reductionEvaluation followed by the finite K-flat counits, then the given
ordinary association. The latter equality follows on local tensors from
hassociation and extends through sheafification and termwise totalization.
Change of rings preserves K-flat complexes with flat terms, so both finite
counits are invertible on the input good complexes. Joint conservativity of the
finite derived evaluations makes the system comparison invertible. The given
strict transitions identify its ordinary target with direct: conjugate the
component evaluation isomorphisms and use the successor equations, then compose
them to treat every horizontal arrow. This is an isomorphism of complexes on the
sequence site. Naturality is obtained before localization from the adjunction
units and tensor maps, then descends through K-flat localization; it is not
inferred from faithfulness of derived evaluations. This yields the natural
model and exactly its stated finite evaluation equation. -/
theorem coefficientExtensionStrictDerivedComparison
    (A : CoefficientExtensionSystems l E L ι W)
    (SE : CoefficientDerivedSystemCalculus l E W)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (htransition : IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation) :
    ∃ model : integralOperationsGoodLocalization l E W ⋙
        coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q,
      IsCoefficientExtensionModelEvaluation l E L ι W SE A association direct
        directEvaluation model := by
  classical
  have := coefficientScalarModelZero A.scalar
  obtain ⟨M⟩ := CompletionUnit.ordinaryModel_exists l E W
  obtain ⟨ε, hε⟩ := coefficientReductionNaturalCochainComparison l E W SE M
  obtain ⟨ρ, hρ, hscalar⟩ := coefficientScalarCochainEvaluation l E L ι W A
  obtain ⟨β, hβ⟩ := coefficientExtensionOrdinaryAssociationChain l E L ι W A M ρ hρ
    association hassociation direct directEvaluation htransition
  let γ : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ⟶ direct ⋙ DerivedCategory.Q :=
    Functor.whiskerRight
        (Functor.whiskerLeft (integralOperationsGoodComplex l E W).ι ε) A.scalar.T ≫
      Functor.whiskerLeft ((integralOperationsGoodComplex l E W).ι ⋙ M.quotient l E W)
        A.scalar.model.ε ≫
      Functor.whiskerRight β.hom DerivedCategory.Q
  have hγ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) :
      (coefficientSequenceDerivedEvaluation l L W n).map (γ.app P) ≫
          (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
            (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P) =
        (A.evaluation n).hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
          (A.levels n).T.map ((SE.reductionEvaluation n).hom.app
            (DerivedCategory.Q.obj P.obj)) ≫
          (A.levels n).T.map
            (coefficientFiniteReductionModel l E W P.obj P.property.1 n).hom ≫
          (A.levels n).model.ε.app
            (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
          DerivedCategory.Q.map
            (coefficientExtensionAssociationChain l E L ι W A n (association n) P.obj) := by
    let C := (M.quotient l E W).obj P.obj
    let κ := (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P.obj
    let e := coefficientSequenceEvaluation l L W n
    have hn := e.mapDerivedCategoryFactors.hom.naturality (β.hom.app P)
    have ha := (A.evaluation n).hom.naturality (ε.app P.obj)
    have hc := (A.levels n).model.ε.naturality κ
    have hr := congrArg (fun f ↦ (A.levels n).T.map f) (hε P n)
    dsimp only [Functor.comp_map] at hn ha hc
    simp only [Functor.map_comp] at hr
    dsimp only [γ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn]
    rw [← DerivedCategory.Q.map_comp, hβ P n]
    simp only [Functor.map_comp]
    dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, e] at hn ha hc hr ⊢
    erw [reassoc_of% hscalar C n]
    erw [← reassoc_of% hc]
    erw [reassoc_of% ha]
    erw [reassoc_of% hr]
  have hγiso (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      IsIso (γ.app P) := by
    obtain ⟨SL, _⟩ := coefficientDerivedSystemEvaluationCalculus l L W
    apply (SL.isIso_iff_evaluations (γ.app P)).2
    intro n
    have hP := (coefficientTensorModelPreservation l E W).1 P.obj P.property.1 n
    have : IsIso ((A.levels n).model.ε.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj)) :=
      (A.levels n).model.computes _ hP
    have : IsIso (coefficientExtensionAssociationChain
        l E L ι W A n (association n) P.obj) := by
      have := coefficientExtensionFiniteZero l E L ι W A n
      have := coefficientExtensionDirectZero l E L ι W n
      have := coefficientExtensionCompositeZero l E L ι W A n
      unfold coefficientExtensionAssociationChain
      exact ((NatIso.mapHomologicalComplex (association n) (.up ℤ)).app P.obj).isIso_hom
    have : IsIso ((coefficientSequenceDerivedEvaluation l L W n).map (γ.app P) ≫
        (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
          (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P)) := by
      rw [hγ P n]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
        (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P))
  have : IsIso γ := (NatTrans.isIso_iff_isIso_app γ).2 hγiso
  refine ⟨asIso γ, ?_⟩
  unfold IsCoefficientExtensionModelEvaluation
  exact hγ

end WeilConjectures
