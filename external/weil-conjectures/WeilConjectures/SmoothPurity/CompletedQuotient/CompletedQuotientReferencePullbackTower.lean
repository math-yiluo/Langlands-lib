/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.SmoothPurity.Supporting.CoherentReferenceQuotientComparison
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackSuccessor
import all WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackTowerTransport

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients
  pullbackTensorRestrictedTower pullbackTensorReferencePullback
  referenceOrdinaryModel integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived
  integralComparisonDerivedSequencePullback
  scalarReductionExtension unrestrictedIntegralReductionFunctor integralOperationsGoodLocalization
  HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  pullbackTensorOrdinaryReduction integralOperationsRoosFunctor
  integralOperationsPullbackOnGood integralComparisonRoosBridge
  integralOperationsPullbackComplexFunctor coefficientSequenceLimit

attribute [local irreducible] HasDerivedCategory.standard coefficientConstantTowerLimit
attribute [local irreducible] pullbackTensorCalculus integralDerivedPullback
  integralCompletedTensor coefficientTotalTensor SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory

private theorem ordinary_formula {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : StrictQuotient.Complex l E Y)
    (a : quotient l E P ≅ C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (hκ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        κ n = (NatIso.mapHomologicalComplex
          ((referenceOrdinaryModel l E Y).evaluation n) (.up ℤ)).app P) :
    let T := OrdinaryTowerProof.pullTower l E f
    let q := T.mapIso a.symm ≪≫
      (OrdinaryTowerProof.comparison l E f (referenceOrdinaryModel l E Y)).app P
    ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (C.X i).val.obj (op (n, U))),
      ((q.hom.app (op n)).f i).val.app (op ((Scheme.proEtaleBaseChange f).obj U))
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj (C.X i)) n
          (op ((Scheme.proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
      integralOperationsPullbackGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
        (((κ n).hom.f i).val.app (op U)
          (coefficientEvaluationSection l E Y (C.X i) n (op U) x)) := by
  dsimp only
  intro n i U x
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapIso_hom, OrdinaryTowerProof.pullTower_map_app_f,
    OrdinaryTowerProof.comparison_hom_app_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, Iso.symm_hom]
  erw [OrdinaryTowerProof.restriction_map_section l E
    ((integralComparisonSequencePullback l E f).map (a.inv.f i)) n
    (op ((Scheme.proEtaleBaseChange f).obj U))
    (integralComparisonSequenceGenerator l E f (C.X i) n U x)]
  erw [OrdinaryTowerProof.sequenceGenerator_naturality, OrdinaryTowerProof.level_unit]
  congr 1
  have hh :
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).map a.inv ≫
        ((NatIso.mapHomologicalComplex
          ((referenceOrdinaryModel l E Y).evaluation n) (.up ℤ)).app P).hom =
      (κ n).hom := by
    rw [← hκ n]
    exact (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex
      (.up ℤ)).mapIso a).inv_hom_id_assoc (κ n).hom
  erw [← OrdinaryTowerProof.evaluation_map_section l E (a.inv.f i) n (op U) x]
  exact congrArg (fun b ↦ (b.f i).val.app (op U)
    (coefficientEvaluationSection l E Y (C.X i) n (op U) x)) hh

/-- The reference quotient pullback tower, transported to the comparison interface.
Source: Stacks 03D2, 0941; quotient normalization reference step.
(blueprint: def-pur-completed-quotient-reference-pullback-tower).
Construction: apply sequence restriction to the inverse of the strict pullback
bridge, and compose with the fixed integral pullback tower. -/
@[irreducible] def completedQuotientReferencePullbackTower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex).obj (quotient l E P) ≅
        (integralOperationsPullbackTowerFunctor l E f).obj P :=
  (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex).mapIso
        ((pullBridge l E f).app (quotient l E P))).symm ≪≫
    pullbackTensorPullbackTower l E f P

/-- Generator formula for the transported reference tower.
Source: Stacks 06YY, 0941; coherent quotient generator calculation.
(blueprint: def-pur-completed-quotient-reference-pullback-tower).
Proof: identify the explicit transported tower with the ordinary tower using
adjunction mates. The ordinary generator formula and naturality of evaluation
then give the formula for a coherent representative. -/
theorem completedQuotientReferencePullbackTower_generator {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : StrictQuotient.Complex l E Y)
    (a : quotient l E P ≅ C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (hκ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        κ n = ((pullbackTensorReductionEvaluationComplex l E Y n).app P).symm) :
    let T := (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    let q := T.mapIso a.symm ≪≫
      completedQuotientReferencePullbackTower l E f P
    ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (C.X i).val.obj (op (n, U))),
      ((q.hom.app (op n)).f i).val.app (op ((Scheme.proEtaleBaseChange f).obj U))
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj (C.X i)) n
          (op ((Scheme.proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
      integralOperationsPullbackGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
        (((κ n).hom.f i).val.app (op U)
          (coefficientEvaluationSection l E Y (C.X i) n (op U) x)) := by
  dsimp only
  intro n i U x
  let T := OrdinaryTowerProof.pullTower l E f
  have ht : completedQuotientReferencePullbackTower l E f P =
      (OrdinaryTowerProof.comparison l E f (referenceOrdinaryModel l E Y)).app P := by
    unfold completedQuotientReferencePullbackTower
    exact tower_transport l E f P
  have hh := congrArg (fun z ↦
    ((((T.mapIso a.symm ≪≫ z).hom.app (op n)).f i).val.app
      (op ((Scheme.proEtaleBaseChange f).obj U)))
      (integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E f).obj (C.X i)) n
        (op ((Scheme.proEtaleBaseChange f).obj U))
        (integralComparisonSequenceGenerator l E f (C.X i) n U x))) ht
  exact hh.trans (ordinary_formula l E f P C a κ hκ n i U x)

end WeilConjectures.CompletedQuotient
