/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarOrdinaryPresentationCoordinates
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import all WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarPackageExists
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.OrdinaryScalarTowerProof

/-! # Ordinary scalar interchange for coherent quotient systems

Source: Stacks 03D7, 03EK and 0941. This is the ordinary tensor association
needed before transporting the derived reduction presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Balanced scalar change commutes with strict ordinary quotient presentations.
Source: Stacks 03D7, 03EK, 06YY and 0941; the ordinary association in step 1 of
lem-pur-scalar-completion-quotient-presentation.
(blueprint: lem-pur-scalar-quotient-ordinary-interchange).

Proof: use the two ordinary tensor/limit adjunctions to identify C and D with
ordinary quotient complexes of P and PS. At level n compose scalar evaluation,
the finite comparison of C, and balanced tensor association. For the latter,
both iterated extensions are left adjoint to restriction along the same
completed-coefficient-to-finite-quotient map; the coefficient square commutes.
The adjoint comparison sends b tensor (a tensor x) to b*iota(a) tensor x,
and its inverse inserts a unit. The corresponding comparison through ordinary
scalar extension sends b tensor (s tensor x) to b*projection(s) tensor x.
Their composite gives the displayed map to the nth quotient of PS.
All these are ordinary module maps, natural in P, so they commute with
cochain differentials. Their formulas on tensor generators commute with each
quotient transition, hence glue to an isomorphism on the entire sequence site.
Conjugate by the two ordinary presentation isomorphisms. On nested tensor
units the inserted units cancel and yield the stated formula. No derived
comparison, K-flatness, completeness, or invertibility of l is required.
The constructions also cover zero complexes, empty sites, n=0, identity maps
and ramified coefficient extensions. -/
theorem scalarQuotientOrdinaryInterchange (Y : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (bC : ((Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)).obj C)
    (hbC : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U),
      (((bC.f i).app (op n)).val.app U) x =
        integralComparisonRestrictedSection l E Y (C.X i) n U
          (integralComparisonSequenceSection l E Y (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x))))
    (D : CochainComplex (coefficientSequenceModules l L Y) ℤ)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex l L Y n).obj
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P))
    (bD : ((Functor.const ℕᵒᵖ : scalarReductionSource l L Y ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l L Y).mapHomologicalComplex (.up ℤ)).obj
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((coefficientSequenceRestriction l L Y).mapHomologicalComplex (.up ℤ)).obj D)
    (hbD : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (x : ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj
          P).X i).val.obj U),
      (((bD.f i).app (op n)).val.app U) x =
        integralComparisonRestrictedSection l L Y (D.X i) n U
          (integralComparisonSequenceSection l L Y (D.X i) n U
            (((κD n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l L Y n
                ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
                  (.up ℤ)).obj P).X i) U 1 x)))) :
    let PS := ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P
    let CS := ((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
      (.up ℤ)).obj C
    ∃ a : CS ≅ D,
      ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (P.X i).val.obj (op U)),
        ((κD n).hom.f i).val.app (op U)
          ((((coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ)).map
            a.hom).f i |>.val.app (op U) <|
            coefficientEvaluationSection l L Y (CS.X i) n (op U)
              (integralComparisonSequenceTensorSection l E L ι Y (C.X i) (op (n, U)) 1
                (integralComparisonSequenceSection l E Y (C.X i) n (op U)
                  (((κ n).inv.f i).val.app (op U)
                    (unrestrictedIntegralTensorSection l E Y n (P.X i) (op U) 1 x))))) =
          unrestrictedIntegralTensorSection l L Y n (PS.X i) (op U) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op U) 1 x) := by
  classical
  dsimp only
  obtain ⟨ME⟩ := CompletionUnit.ordinaryModel_exists l E Y
  obtain ⟨ML⟩ := CompletionUnit.ordinaryModel_exists l L Y
  obtain ⟨aC, _, haC⟩ := coherentQuotientOrdinaryLift l E Y ME P C κ bC hbC
  obtain ⟨aD, _, haD⟩ := coherentQuotientOrdinaryLift l L Y ML
    (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)
    D κD bD hbD
  obtain ⟨A, hA, hTensor⟩ := OrdinaryScalarTowerProof.fixedSystems_exists l E L ι Y
  obtain ⟨ρ, hρ, _⟩ := coefficientScalarCochainEvaluation l E L ι Y A
  obtain ⟨d⟩ := coefficientExtensionFiniteAssociation_exists l E L ι Y A
  obtain ⟨v, hv⟩ := scalarOrdinaryPresentationCoordinates l E L ι Y A ME ML ρ hρ
    d.association d.association_section (integralComparisonSequenceScalarModel l E L ι Y).E
    hA P C aC κ haC
  refine ⟨v ≪≫ aD, ?_⟩
  intro n i U x
  let y := integralComparisonSequenceTensorSection l E L ι Y (C.X i) (op (n, U)) 1
    (integralComparisonSequenceSection l E Y (C.X i) n (op U)
      (((κ n).inv.f i).val.app (op U)
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op U) 1 x)))
  have hy := hTensor (C.X i) (op (n, U)) 1
    (integralComparisonSequenceSection l E Y (C.X i) n (op U)
      (((κ n).inv.f i).val.app (op U)
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op U) 1 x)))
  have hn := hv n i (op U) x y (by simpa only [one_smul] using hy)
  have hd := congrArg (fun e ↦ (e.hom.f i).val.app (op U)) (haD n)
  change ((κD n).hom.f i).val.app (op U)
    (((coefficientSequenceEvaluation l L Y n).map (aD.hom.f i)).val.app (op U)
      (((coefficientSequenceEvaluation l L Y n).map (v.hom.f i)).val.app (op U)
        (coefficientEvaluationSection l L Y _ n (op U) y))) = _
  have hd' := congrArg (fun f ↦ f
    (((coefficientSequenceEvaluation l L Y n).map (v.hom.f i)).val.app (op U)
      (coefficientEvaluationSection l L Y _ n (op U) y))) hd
  exact hd'.trans hn

end WeilConjectures.ScalarExtensionTower
