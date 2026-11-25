/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.CoefficientStrictReductionTensorNormalization
import WeilConjectures.SixFunctors.Coefficient.CoefficientReductionTensorEvaluationPasting
import WeilConjectures.SixFunctors.Coefficient.CoefficientPrescribedPairTensorModels
import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationTensorChain
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement

/-! # Representative normalizations for coefficient reduction

Source: Stacks 06YS, 06YY, 07A4, 07A6 and 0941
(blueprint: lem-coef-normalized-reduction-models-normalizations).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local implicit_reducible] CategoryTheory.uniformProd
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  coefficientSequenceEvaluation coefficientSequenceHasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  coefficientTotalTensor CoefficientClosedStructure.tensor
  coefficientIntegralTensorModelIso coefficientFiniteTensorModelIso
  coefficientSystemTensorModelIso coefficientScalarTensorIso coefficientEvaluationTensorIso
  CoefficientTensorModels.iso

-- Avoid re-elaborating the already typed coefficient-site instance arguments.
-- The declaration's proof is still checked by Lean's kernel.
local elab "kernel_exact " t:term : tactic => Lean.Elab.Tactic.withMainContext do
  let e ← Lean.Elab.Term.elabTerm t none
  (← Lean.Elab.Tactic.getMainGoal).assign e
  Lean.Elab.Tactic.replaceMainGoal []

private theorem actualScalarModel (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    SheafOfModules.scalarPairComplexComparison
      (coefficientActualScalarDerivedPair l E W n).extension
      (coefficientActualScalarDerivedPair l E W n).extension_additive
      (coefficientActualScalarDerivedPair l E W n).derived
      (coefficientActualScalarDerivedPair l E W n).counit P =
      (coefficientFiniteReductionModel l E W P hP n).hom := by
  unfold coefficientFiniteReductionModel coefficientLocalizedCounitModel
    SheafOfModules.scalarPairComplexComparison
  rfl

/-- Construct the finite tensor comparisons using the prescribed scalar pairs.
Source: Stacks 06YY and 07A4. -/
private theorem normalizedFiniteTensor (R : CoefficientDerivedSystemReduction l E W) :
    ∃ μ : ∀ n : ℕ,
      R.integralClosed.tensor ⋙ coefficientFiniteDerivedExtension l E W n ≅
        (coefficientFiniteDerivedExtension l E W n).prod
          (coefficientFiniteDerivedExtension l E W n) ⋙ (R.finiteClosed n).tensor,
      CoefficientFiniteTensorNormalization l E W { R with finiteTensor := μ } := by
  classical
  let J := Scheme.ProEt.topology W
  let (A : Sheaf J CommRingCat.{max u (t+1)}) :
      HasDerivedCategory.{max (t+2) (u+1)} (SheafOfModules.scalarModules J A) :=
    HasDerivedCategory.standard _
  let tc (n : ℕ) := (coefficientPrescribedPairTensorComparison.{t+1, t, u, max (t+2) (u+1)}
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (coefficientActualScalarDerivedPair l E W n) R.integralClosed (R.finiteClosed n)
    R.integralTensorModel (R.finiteTensorModel n)).some
  refine ⟨fun n ↦ (tc n).iso, ?_⟩
  intro n P Q hP hQ
  have hn := (tc n).normalization P Q hP hQ
  have hc : (tc n).complexIso P Q = coefficientScalarTensorIso l E W n P Q := by
    apply (coefficientScalarTensorIso_exists l E W n P Q).unique
    · exact (tc n).generators P Q
    · unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
      exact (coefficientScalarTensorIso_exists l E W n P Q).choose_spec.1
  rw [hc, actualScalarModel l E W n P hP, actualScalarModel l E W n Q hQ,
    actualScalarModel l E W n _
      (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ)] at hn
  unfold CoefficientTensorComparisonSquare coefficientIntegralTensorModelIso
    coefficientFiniteTensorModelIso
  simp only [SheafOfModules.scalarComplex,
    coefficientActualScalarDerivedPair_extension,
    coefficientActualScalarDerivedPair_derived] at hn
  kernel_exact hn

private theorem normalizedEvaluationTensor (R : CoefficientDerivedSystemReduction l E W) :
    ∃ μ : ∀ n : ℕ,
      R.systemClosed.tensor ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
        (coefficientSequenceDerivedEvaluation l E W n).prod
          (coefficientSequenceDerivedEvaluation l E W n) ⋙ (R.finiteClosed n).tensor,
      CoefficientEvaluationTensorNormalization l E W { R with evaluationTensor := μ } := by
  classical
  let A := coefficientSequenceModules l E W
  let J := Scheme.ProEt.topology W
  let Rs := coefficientSequenceCommRingSheaf l E W
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  have hd (n : ℕ) := coefficientNormalizedEvaluationTensorChain l E W n
  let b (n : ℕ) := (hd n).choose
  have h (n : ℕ) := by
    let F := coefficientSequenceEvaluation l E W n
    let B := normalizedDVRModules l E W n
    let PS : ObjectProperty (CochainComplex B ℤ) :=
      CochainComplex.IsKFlatIndependentCoefficients
    have hff := resolvingRepresentativesFullyFaithfulWhiskering
      (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
      (D := DerivedCategory A) (DerivedCategory B)
      (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
      (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
    let ff := hff.some.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
      (NatIso.prod (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
        (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
    exact tensorComparisonDescent DerivedCategory.Q DerivedCategory.Q
      (F.mapHomologicalComplex (.up ℤ)) (coefficientSequenceDerivedEvaluation l E W n)
      F.mapDerivedCategoryFactors.hom PR PS
      (fun P hP ↦ (coefficientTensorModelPreservation l E W).2 P hP n) ff
      (coefficientTotalTensor.{u, t+1, t} (coefficientSequenceTopology J) Rs)
      (coefficientTotalTensor.{u, t+1, t} J (integralCoefficientCommRingSheaf l E W n))
      R.systemClosed.tensor (R.finiteClosed n).tensor
      R.systemTensorModel.comparison (R.finiteTensorModel n).comparison (b n)
      (fun _ _ ↦ by infer_instance) (fun _ _ _ _ ↦ by infer_instance)
  refine ⟨fun n ↦ (h n).choose, ?_⟩
  intro n P Q hP hQ
  have hn := (h n).choose_spec.1 P Q hP hQ
  have he := congrArg Iso.hom ((hd n).choose_spec P Q)
  change (b n).hom.app (P, Q) = (coefficientEvaluationTensorIso l E W n P Q).hom at he
  rw [he] at hn
  unfold CoefficientTensorComparisonSquare coefficientSystemTensorModelIso
    coefficientFiniteTensorModelIso CoefficientTensorModels.iso
  kernel_exact hn

/-- Choose the normalized tensor comparisons while retaining the core reduction model.
Source: Stacks 06YY, 07A4 and 0941, normalized reduction construction, step 2.

STATEMENT-DISPUTED: the former assertion for arbitrary comparisons was false (repaired here):
negating just finiteTensor preserves all fields of the reduction record but changes
its prescribed representative square. Normalization must therefore construct these
comparisons, rather than assert it for the original arbitrary comparisons.

Proof: construct finite scalar tensor comparisons from the prescribed scalar-derived
pairs, identifying their chain comparisons by the unique scalar-unit generator law.
Descend exact evaluation's natural total-tensor comparison along K-flat representatives;
its unique generator law identifies it with coefficientEvaluationTensorIso. Choose
the strict reduction tensor comparison independently. Replace the three comparison
fields together and paste their representative squares for the evaluation equation.
All reduction-model data, its adjunction, and both projection identities are retained.
(blueprint: lem-coef-normalized-reduction-models-normalizations). -/
theorem coefficientNormalizedReductionNormalizations
    (R : CoefficientDerivedSystemReduction l E W) :
    ∃ S : CoefficientDerivedSystemReduction l E W,
      S.toCoefficientDerivedSystemReductionModel = R.toCoefficientDerivedSystemReductionModel ∧
      CoefficientReductionTensorNormalization l E W S ∧
      CoefficientFiniteTensorNormalization l E W S ∧
      CoefficientEvaluationTensorNormalization l E W S ∧
      CoefficientReductionTensorEvaluation l E W S := by
  obtain ⟨μR, hR⟩ := coefficientStrictReductionTensorNormalization l E W R
  obtain ⟨μF, hF⟩ := normalizedFiniteTensor l E W R
  obtain ⟨μE, hE⟩ := normalizedEvaluationTensor l E W R
  let S : CoefficientDerivedSystemReduction l E W :=
    { R with reductionTensor := μR, finiteTensor := μF, evaluationTensor := μE }
  have hsR : CoefficientReductionTensorNormalization l E W S := hR
  have hsF : CoefficientFiniteTensorNormalization l E W S := hF
  have hsE : CoefficientEvaluationTensorNormalization l E W S := hE
  exact ⟨S, rfl, hsR, hsF, hsE,
    coefficientReductionTensorEvaluation_of_normalizations l E W S hsR hsF hsE⟩

end WeilConjectures
