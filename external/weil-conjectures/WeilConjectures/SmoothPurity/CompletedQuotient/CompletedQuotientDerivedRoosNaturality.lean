/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTensorModelNormalization

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
  integralCoefficientSheaf integralCoefficientCommRingSheaf
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

-- Cochain-level form of the same Roos transport, with the fixed source bridge.
private theorem cochainRoos_naturality {X : Scheme.{u}}
    (ρ : IntegralComparisonRoosModel l E X)
    {C D : StrictQuotient.Complex l E X} (a : C ⟶ D) :
    let LL := coefficientSequenceLimit l E X
    let U := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    let H := integralOperationsRoosFunctor (A := scalarReductionSource l E X) ⋙ DerivedCategory.Q
    LL.map (DerivedCategory.Q.map a) ≫ (integralComparisonRoosBridge l E X ρ D).hom =
      (pullbackTensorLimitRoos l E X C).hom ≫ H.map (U.map a) := by
  dsimp only
  let ηr := Functor.isoWhiskerRight
      (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l E X) ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ))
      ρ.comparison
  rw [ScalarExtensionTower.roosBridge_eq l E X ρ]
  exact ηr.hom.naturality a

/-- Naturality of the derived pullback factorization followed by the Roos bridge.
Source: the quotient normalization transport step.
(blueprint: lem-pur-completed-quotient-derived-roos-naturality).
Proof: compose the natural derived factorization isomorphisms with the Roos
comparison, and evaluate naturality of that composite on the cochain map. -/
theorem completedQuotientDerivedRoosNaturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : IntegralComparisonRoosModel l E X)
    {C D : StrictQuotient.Complex l E Y} (a : C ⟶ D) :
    let F := integralComparisonSequencePullback l E f
    let FD := integralComparisonDerivedSequencePullback l E f
    let LL := coefficientSequenceLimit l E X
    let U := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    let H := integralOperationsRoosFunctor (A := scalarReductionSource l E X) ⋙ DerivedCategory.Q
    LL.map (FD.map (DerivedCategory.Q.map a)) ≫
        LL.map (F.mapDerivedCategoryFactors.hom.app D) ≫
        (integralComparisonRoosBridge l E X ρ _).hom =
      LL.map (F.mapDerivedCategoryFactors.hom.app C) ≫
        (integralComparisonRoosBridge l E X ρ _).hom ≫
        H.map ((F.mapHomologicalComplex (.up ℤ) ⋙ U).map a) := by
  dsimp only
  let F := integralComparisonSequencePullback l E f
  let η := Functor.isoWhiskerRight F.mapDerivedCategoryFactors
      (coefficientSequenceLimit l E X) ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (Functor.isoWhiskerRight
          (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors
          (coefficientConstantTowerLimit l E X) ≪≫
        Functor.isoWhiskerLeft
          ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ))
          ρ.comparison)
  with_unfolding_all
    simpa only [η, F, integralComparisonRoosBridge,
      integralComparisonDerivedSequencePullback, Iso.trans_hom, NatTrans.comp_app,
      Functor.mapIso_hom, Iso.app_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.comp_map, Functor.comp_obj, Category.assoc] using η.hom.naturality a

end WeilConjectures.CompletedQuotient
