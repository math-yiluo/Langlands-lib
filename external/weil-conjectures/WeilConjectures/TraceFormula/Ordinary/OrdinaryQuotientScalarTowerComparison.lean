/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import all WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarPackageExists
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRestrictedTower
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionAssociationSuccessor
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationScalarUnits
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationQuotientUnits
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationTensorCoordinates
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.OrdinaryScalarTowerProof
import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation

/-! # Ordinary quotient scalar tower comparison

Source: Stacks 03EK, 03D7, 06YY and 0941, balanced tensor association.
(blueprint: lem-trf-ordinary-quotient-scalar-tower-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

/-- Ordinary scalar extension of the strict quotient system is the direct scalar tower.
Source: Stacks 03EK, 03D7 and 0941, balanced association for quotient tensors.
(blueprint: lem-trf-ordinary-quotient-scalar-tower-comparison).

Proof: evaluate at each quotient. The ordinary extension/restriction adjunction
identifies evaluation of sequence scalar extension with scalar extension of the
evaluated module. Construct the scalar systems package with the prescribed
actual sequence cochain model, transporting along the componentwise equality
of the sequence ring maps. The ordinary unit formula then identifies actual
tensor sections with scalar multiples of that unit. Compose with M.evaluation and the
balanced associator
b tensor (a tensor x) to (b times iota(a)) tensor x. Its inverse inserts 1.
Both maps commute with quotient reduction because reduction preserves products,
so they assemble to an isomorphism of whole strict towers. Apply the construction
degreewise; naturality gives compatibility with differentials and chain maps.
For a presentation a, precompose this comparison with scalar extension of a inverse.
The evaluation equation cancels a against kappa. On the sections 1 tensor x this
gives exactly s tensor x in the target. Linearity gives all s, and sheafification
extends the formula to arbitrary local sections. This is an ordinary tensor and
strict tower statement; it asserts no faithfulness of derived evaluations. -/
theorem ordinaryQuotientScalarTowerComparison
    (M : CompletionUnit.OrdinaryModel l E W) :
    let F := (integralComparisonSequenceScalarModel l E L ι W).E
    let T := F.mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    ∃ θ : M.quotient l E W ⋙ T ≅ integralScalarTowerFunctor l E L ι W,
      ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ)
        (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (a : (M.quotient l E W).obj P ≅ C)
        (κ : ∀ n : ℕ,
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
            (unrestrictedIntegralFiniteComplex l E W n).obj P),
        (∀ n : ℕ,
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
            κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) →
        ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
          (s : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
          (x : (P.X i).val.obj U),
          (((T.mapIso a.symm ≪≫ θ.app P).hom.app (op n)).f i).val.app U
            (integralComparisonRestrictedSection l L W (F.obj (C.X i)) n U
              (integralComparisonSequenceTensorSection l E L ι W (C.X i)
                (op (n, U.unop)) s
                (integralComparisonSequenceSection l E W (C.X i) n U
                  (((κ n).inv.f i).val.app U
                    (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))))) =
            integralScalarTensorSection l E L ι W n (P.X i) U s x := by
  dsimp only
  obtain ⟨A, hA, hTensor⟩ := OrdinaryScalarTowerProof.fixedSystems_exists l E L ι W
  obtain ⟨ρ, hρ, _⟩ := coefficientScalarCochainEvaluation l E L ι W A
  obtain ⟨d⟩ := coefficientExtensionFiniteAssociation_exists l E L ι W A
  obtain ⟨θ, hθ⟩ := OrdinaryScalarTowerProof.normalizedComparison l E L ι W A M ρ hρ
    d.association d.association_section (integralComparisonSequenceScalarModel l E L ι W).E hA
  refine ⟨θ, ?_⟩
  intro P C a κ hκ n i U s x
  exact hθ P C a κ hκ n i U s x _
    (hTensor (C.X i) (op (n, U.unop)) s
      (integralComparisonSequenceSection l E W (C.X i) n U
        (((κ n).inv.f i).val.app U
          (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))))

end WeilConjectures
