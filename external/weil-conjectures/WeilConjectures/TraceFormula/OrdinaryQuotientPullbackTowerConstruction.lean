/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels

import all WeilConjectures.TraceFormula.OrdinaryQuotientPullbackTowerLevels

/-! # Private strict pullback tower construction

Source: Stacks 06YY, 0941 and 099N(5), the strict quotient-system construction.
(blueprint: lem-trf-ordinary-quotient-pullback-tower-comparison)
-/

@[expose] public noncomputable section
-- This proof-only module intentionally exports no declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingProjectionUnrestricted
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
namespace OrdinaryTowerProof
attribute [local irreducible] Functor.leftAdjoint
  coefficientSequenceCommRingSheaf integralCoefficientCommRingSheaf
  directEvaluation inverseEvaluation moduleLevel level
attribute [local implicit_reducible]
  HomologicalComplex.complexOfFunctorsToFunctorToComplex HomologicalComplex.asFunctor

private theorem level_unit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (n : ℕ) (i : ℤ) (U : Y.ProEt)
    (x : (M.tensor.obj (P.X i)).val.obj (op (n, U))) :
    (((level l E f M P n).hom.f i).val.app
        (op ((proEtaleBaseChange f).obj U)))
      (integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E f).obj (M.tensor.obj (P.X i))) n
        (op ((proEtaleBaseChange f).obj U))
        (integralComparisonSequenceGenerator l E f (M.tensor.obj (P.X i)) n U x)) =
      integralOperationsPullbackGenerator l E f n
        ((scalarReductionExtension l E Y n).obj (P.X i)) U
        (((M.evaluation n).hom.app (P.X i)).val.app (op U)
          (coefficientEvaluationSection l E Y (M.tensor.obj (P.X i)) n (op U) x)) := by
  simp only [level, HomologicalComplex.Hom.isoOfComponents_hom_f]
  simp only [moduleLevel]
  change (((integralOperationsLevelPullback l E f n).map
      ((M.evaluation n).hom.app (P.X i))).val.app _)
    ((((inverseEvaluation l E f n).inv.app (M.tensor.obj (P.X i))).val.app _)
      ((((eqToIso (coefficientSequenceRestriction_evaluation l E X n)).app
        ((integralComparisonSequencePullback l E f).obj (M.tensor.obj (P.X i)))).hom.val.app _)
          _)) = _
  rw [restrictionEvaluation_section, inverseEvaluation_inv_unit]
  exact finiteGenerator_naturality l E f n ((M.evaluation n).hom.app (P.X i)) U _

private def towerIso {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    (pullTower l E f).obj ((M.quotient l E Y).obj P) ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P := by
  have h := ordinaryQuotientPullback_successor l E f M P (level l E f M P)
    (level_unit l E f M P)
  let a : (pullTower l E f).obj ((M.quotient l E Y).obj P) ⟶
      (integralOperationsPullbackTowerFunctor l E f).obj P :=
    NatTrans.ofOpSequence (fun n ↦ (level l E f M P n).hom) h
  letI : ∀ n, IsIso (a.app n) := fun n ↦ Iso.isIso_hom (level l E f M P n.unop)
  letI := NatIso.isIso_of_isIso_app a
  exact asIso a

/-- The canonical strict tower comparison, natural in the completed complex.
Source: Stacks 06YY, 0941 and 099N(5).
(blueprint: def-trf-ordinary-quotient-pullback-tower-construction).
Construction: the level maps are the adjunction mates of direct-image evaluation,
followed by the fixed quotient evaluation. Their tensor-unit formula makes them
commute with successor transitions. NatTrans.ofOpSequence and pointwise inversion
assemble the tower isomorphism; naturality is the module comparison naturality. -/
private def comparison {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y) :
    M.quotient l E Y ⋙ pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f :=
  NatIso.ofComponents (towerIso l E f M) (by
    intro P Q a
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.hom_ext
    intro i
    simp only [NatTrans.comp_app, HomologicalComplex.comp_f, towerIso, asIso_hom,
      NatTrans.ofOpSequence_app, level, HomologicalComplex.Hom.isoOfComponents_hom_f]
    exact (moduleLevel l E f M n.unop).hom.naturality (a.f i))

attribute [local irreducible] comparison

end OrdinaryTowerProof

end WeilConjectures
