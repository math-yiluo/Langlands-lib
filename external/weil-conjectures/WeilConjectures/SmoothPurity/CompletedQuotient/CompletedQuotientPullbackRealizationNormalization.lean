/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealization
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientReferencePullbackTower
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientReferencePullbackEquation
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientDerivedRoosNaturality
import WeilConjectures.SmoothPurity.Supporting.CoherentReferenceQuotientComparison

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

/-- The transported fixed pullback realization is normalized on coherent representatives.
Source: Stacks 03D2 and 0941; quotient scalar-coordinate normalization.
(blueprint: lem-pur-completed-quotient-pullback-realization-normalized).

Proof: identify inverse evaluation by adjunction mates and the two pullback towers
componentwise. Use the coherent reference quotient comparison to transport the
ordinary tower and its generator formula to the given representative. The fixed
integral pullback model supplies the completed equation on the reference quotient;
naturality of derived quotient factorization and the Roos bridge transports it
to the given coherent presentation. -/
theorem completedQuotientPullbackRealization_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : IntegralComparisonRoosModel l E X) :
    IsIntegralComparisonPullbackNormalized l E f (pullbackTensorCalculus l E Y) ρ
      (completedQuotientPullbackRealization l E f) := by
  intro P C e κ hp hc
  obtain ⟨a, ha, hκ⟩ := coherentReferenceQuotientComparison l E Y
    (pullbackTensorCalculus l E Y) P C e κ hc
  simp only [Adjunction.leftAdjointUniq_refl, NatTrans.id_app,
    Category.id_comp] at ha
  let R := (pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)
  let F := integralComparisonSequencePullback l E f
  let U := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let T := F.mapHomologicalComplex (.up ℤ) ⋙ U
  let H := integralOperationsRoosFunctor (A := scalarReductionSource l E X) ⋙ DerivedCategory.Q
  let θ := completedQuotientReferencePullbackTower l E f P.obj
  let q := T.mapIso a.symm ≪≫ θ
  refine ⟨q, ?_, ?_⟩
  · apply completedQuotientReferencePullbackTower_generator l E f P.obj C a κ
    intro n
    have h := hκ n
    exact h
  · have hreference :
        (completedQuotientPullbackRealization l E f).hom.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientSequenceLimit l E X).map
            ((integralComparisonDerivedSequencePullback l E f).map
              ((pullbackTensorReductionModel l E Y).hom.app P)) ≫
          (coefficientSequenceLimit l E X).map
            (F.mapDerivedCategoryFactors.hom.app (R.obj P.obj)) ≫
          (integralComparisonRoosBridge l E X ρ _).hom ≫
          H.map (θ.hom) =
        (integralDerivedPullbackComparison l E f).hom.app P := by
      exact completedQuotientReferencePullbackEquation l E f ρ P
    have hq : T.map a.hom ≫ q.hom = θ.hom := by
      dsimp only [q]
      change T.map a.hom ≫ (T.map a.inv ≫ θ.hom) = _
      rw [← Category.assoc, ← T.map_comp, a.hom_inv_id, T.map_id, Category.id_comp]
    let LL := coefficientSequenceLimit l E X
    have hn := completedQuotientDerivedRoosNaturality l E f ρ a.hom
    change LL.map ((integralComparisonDerivedSequencePullback l E f).map
        (DerivedCategory.Q.map a.hom)) ≫
      LL.map (F.mapDerivedCategoryFactors.hom.app C) ≫
      (integralComparisonRoosBridge l E X ρ _).hom =
        LL.map (F.mapDerivedCategoryFactors.hom.app (R.obj P.obj)) ≫
        (integralComparisonRoosBridge l E X ρ _).hom ≫ H.map (T.map a.hom) at hn
    change (completedQuotientPullbackRealization l E f).hom.app _ ≫
      LL.map ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
      LL.map (F.mapDerivedCategoryFactors.hom.app C) ≫
      (integralComparisonRoosBridge l E X ρ _).hom ≫ H.map q.hom = _
    rw [← ha, (integralComparisonDerivedSequencePullback l E f).map_comp, LL.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hn]
    have hhq := congrArg H.map hq
    simp only [Functor.map_comp] at hhq
    rw [hhq]
    exact hreference

end WeilConjectures.CompletedQuotient
