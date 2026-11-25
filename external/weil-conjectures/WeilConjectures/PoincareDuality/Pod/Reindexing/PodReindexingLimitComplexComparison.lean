/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingStrictData.PodReindexingStrictComparisons

/-! # The specified limit comparison on complexes

(blueprint: def-pod-reindexing-limit-complex-comparison) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

/-- The supplied normalized Roos model after coefficient restriction.
Source: blueprint theorem-poincare-duality-frobenius--2, Step 5.
(blueprint: def-pod-reindexing-limit-complex-comparison) -/
def podReindexingLimitRoosIso (W : Scheme.{t}) (ρ : IntegralComparisonRoosModel l E W) :
    DerivedCategory.Q ⋙ coefficientSequenceLimit l E W ≅
      ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙
        integralOperationsRoosFunctor ⋙
        DerivedCategory.Q :=
  isoWhiskerRight (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
    (coefficientConstantTowerLimit l E W) ≪≫
      isoWhiskerLeft ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ))
        ρ.comparison

/-- The strict Roos maps assembled using their specified naturality.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5.
(blueprint: def-pod-reindexing-limit-complex-comparison) -/
def podReindexingStrictRoosIso (S : PodReindexingStrictData l E g)
    (hS : S.RoosNaturality l E g) :
    integralOperationsRoosFunctor (A := scalarReductionSource l E Y) ⋙
        isoReductionIntegralComplex l E g ≅
      podReindexTower l E g ⋙
        integralOperationsRoosFunctor (A := scalarReductionSource l E X) :=
  NatIso.ofComponents S.roos (by
    intro C C' f
    exact hS C C' f)

/-- Paste the normalized source and target Roos models with strict reindexing.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5.
Each factor is specified: no witness of an existence theorem is chosen.
(blueprint: def-pod-reindexing-limit-complex-comparison) -/
def podReindexingLimitComparisonOnComplexes (S : PodReindexingStrictData l E g)
    (hS : S.RoosNaturality l E g)
    (ρY : IntegralComparisonRoosModel l E Y) (ρX : IntegralComparisonRoosModel l E X)
    (r : ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙ podReindexTower l E g ≅
      ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)) ⋙
        ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex)) :
    DerivedCategory.Q ⋙ coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ≅
      DerivedCategory.Q ⋙ integralComparisonDerivedSequencePullback l E g ⋙
        coefficientSequenceLimit l E X :=
  isoWhiskerRight (podReindexingLimitRoosIso l E Y ρY) (podOrdinaryReindex l E g) ≪≫
    isoWhiskerLeft (((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙ integralOperationsRoosFunctor)
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors ≪≫
    isoWhiskerRight
      (isoWhiskerLeft ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex)
        (podReindexingStrictRoosIso l E g S hS)) DerivedCategory.Q ≪≫
    isoWhiskerRight (isoWhiskerRight r integralOperationsRoosFunctor) DerivedCategory.Q ≪≫
    (isoWhiskerLeft ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ))
        (podReindexingLimitRoosIso l E X ρX)).symm ≪≫
    (isoWhiskerRight (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors
      (coefficientSequenceLimit l E X)).symm

end WeilConjectures
