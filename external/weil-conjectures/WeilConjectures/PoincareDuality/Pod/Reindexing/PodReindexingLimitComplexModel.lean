/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingLimitComplexComparison

/-! # Component equation of the specified comparison

(blueprint: lem-pod-reindexing-limit-complex-model) -/

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

/-- Cancel the target model and localization factors in the specified comparison.

Source: blueprint theorem-poincare-duality-frobenius--2, Step 5. Expand the six
factors of the comparison. Compose with the target localization factor and the
target Roos model. Their inverse pairs cancel, leaving the source Roos model,
the integral reindexing localization map, and the two strict Roos and restricted
tower maps. This is an equality of the full maps, not only of finite projections.
(blueprint: lem-pod-reindexing-limit-complex-model) -/
theorem podReindexingLimitComparisonOnComplexes_model (S : PodReindexingStrictData l E g)
    (hS : S.RoosNaturality l E g)
    (ρY : IntegralComparisonRoosModel l E Y) (ρX : IntegralComparisonRoosModel l E X)
    (r : ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙ podReindexTower l E g ≅
      ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)) ⋙
        ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex))
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (podReindexingLimitComparisonOnComplexes l E g S hS ρY ρX r).hom.app C ≫
        (coefficientSequenceLimit l E X).map
          ((integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app C) ≫
        (podLimitRoos l E ρX
          (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj C)).hom =
      (podOrdinaryReindex l E g).map (podLimitRoos l E ρY C).hom ≫
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map (S.roos (podRestrictedTower l E C)).hom ≫
        DerivedCategory.Q.map
          (integralOperationsRoosFunctor.map (r.app C).hom) := by
  change _ ≫
    (isoWhiskerRight (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors
      (coefficientSequenceLimit l E X)).hom.app C ≫
    (isoWhiskerLeft ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ))
        (podReindexingLimitRoosIso l E X ρX)).hom.app C = _
  simp only [podReindexingLimitComparisonOnComplexes, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rfl

end WeilConjectures
