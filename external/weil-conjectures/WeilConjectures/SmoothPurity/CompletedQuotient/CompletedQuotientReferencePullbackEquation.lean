/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealization
public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientReferencePullbackTower
import all WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientDerivedRoosNaturality
import all WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealization

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

/-- Completed pullback equation on the fixed reference quotient.
Source: Stacks 03D2, 0941; quotient normalization reference equation.
(blueprint: lem-pur-completed-quotient-reference-pullback-equation).
Proof: naturality of the derived strict-interface transport moves the reference
reduction through it. Derived factorization and the Roos bridge give the strict
tower transport. Cancel the bridge with its inverse and apply the normalization
of the fixed integral pullback realization. -/
theorem completedQuotientReferencePullbackEquation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : IntegralComparisonRoosModel l E X)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    let R := (pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)
    let F := integralComparisonSequencePullback l E f
    let H := integralOperationsRoosFunctor (A := scalarReductionSource l E X) ⋙ DerivedCategory.Q
    (completedQuotientPullbackRealization l E f).hom.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientSequenceLimit l E X).map
            ((integralComparisonDerivedSequencePullback l E f).map
              ((pullbackTensorReductionModel l E Y).hom.app P)) ≫
          (coefficientSequenceLimit l E X).map
            (F.mapDerivedCategoryFactors.hom.app (R.obj P.obj)) ≫
          (integralComparisonRoosBridge l E X ρ _).hom ≫
          H.map ((completedQuotientReferencePullbackTower l E f P.obj).hom) =
        (integralDerivedPullbackComparison l E f).hom.app P := by
      dsimp only
      let R := (pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)
      let F := integralComparisonSequencePullback l E f
      let U := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex
      let H := integralOperationsRoosFunctor (A := scalarReductionSource l E X) ⋙ DerivedCategory.Q
      let LL := coefficientSequenceLimit l E X
      let A := R.obj P.obj
      let b := derivedPullBridge l E f
      let B := (pullBridge l E f).hom.app A
      have hm : b.hom.app ((pullbackTensorCalculus l E Y).reduction.obj
            (DerivedCategory.Q.obj P.obj)) ≫
          (integralComparisonDerivedSequencePullback l E f).map
            ((pullbackTensorReductionModel l E Y).hom.app P) ≫
          F.mapDerivedCategoryFactors.hom.app A =
        (pullbackTensorSequenceDerived l E f).map
            ((pullbackTensorReductionModel l E Y).hom.app P) ≫
          (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A ≫
          DerivedCategory.Q.map B := by
        rw [← reassoc_of% b.hom.naturality]
        exact congrArg (fun z ↦ (pullbackTensorSequenceDerived l E f).map
          ((pullbackTensorReductionModel l E Y).hom.app P) ≫ z)
          (derivedPullBridge_factors l E f A).symm
      have hr : LL.map (DerivedCategory.Q.map B) ≫
          (integralComparisonRoosBridge l E X ρ _).hom =
        (pullbackTensorLimitRoos l E X _).hom ≫ H.map (U.map B) := by
        exact cochainRoos_naturality l E ρ B
      have ht : U.map B ≫ (completedQuotientReferencePullbackTower l E f P.obj).hom =
          (pullbackTensorPullbackTower l E f P.obj).hom := by
        unfold completedQuotientReferencePullbackTower
        change U.map B ≫ (U.map ((pullBridge l E f).inv.app A) ≫
          (pullbackTensorPullbackTower l E f P.obj).hom) = _
        rw [← Category.assoc, ← U.map_comp,
          (pullBridge l E f).hom_inv_id_app A, U.map_id, Category.id_comp]
      have hc := (pullbackTensorIntegralPullbackModel_existsUnique l E f).exists.choose_spec P
      change (pullbackTensorIntegralPullbackModel l E f).app
        (DerivedCategory.Q.obj P.obj) = _ at hc
      have hc' : (pullbackTensorIntegralPullbackModel l E f).app
            (DerivedCategory.Q.obj P.obj) ≪≫
          pullbackTensorReferencePullbackModel l E f P =
        (integralDerivedPullbackComparison l E f).app P := by
        rw [hc]
        simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
      have hf := congrArg Iso.hom hc'
      change (pullbackTensorIntegralPullbackModel l E f).hom.app _ ≫
        LL.map ((pullbackTensorSequenceDerived l E f).map
          ((pullbackTensorReductionModel l E Y).hom.app P)) ≫
        LL.map ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A) ≫
        (pullbackTensorLimitRoos l E X _).hom ≫
        H.map (pullbackTensorPullbackTower l E f P.obj).hom = _ at hf
      unfold completedQuotientPullbackRealization
      change (_ ≫ LL.map (b.hom.app _)) ≫ LL.map _ ≫ LL.map _ ≫ _ ≫ _ = _
      simp only [Category.assoc, ← LL.map_comp_assoc]
      rw [hm, LL.map_comp, LL.map_comp]
      simp only [Category.assoc]
      rw [reassoc_of% hr, ← H.map_comp, ht]
      exact hf
end WeilConjectures.CompletedQuotient
