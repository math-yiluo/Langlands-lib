/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonStrictComparisonAux
public import WeilConjectures.SmoothPurity.IntegralCoherence.SequencePullbackMonoidal

/-! # Composition law of the strict quotient comparisons

Source: Stacks 07A4 and 0D6D
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

The recorded generator-normalized comparisons of strict quotient complexes satisfy the
composition law with the adjunction-normalized compositor, written with the total tensor
bifunctor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]


attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  SheafOfModules.monoidalCategory
  pullbackTensorCalculus integralDerivedPullback integralCompletedTensor
  coefficientSequenceLimit Functor.mapDerivedCategory Functor.leftAdjoint

attribute [local implicit_reducible] coefficientSequenceInternalHom
  pullbackTensorReferenceTensor pullbackTensorReferencePullback
  constructibleIntegralTensor constructibleIntegralPullback scalarReductionSourceDerived
  StrictQuotient.SystemGood coefficientTotalTensor pullbackTensorSequenceDerived
  SheafOfModules.cochainModulesMonoidal HomologicalComplex.monoidalCategory
  value expression IntegralCoherence.value substituteInputs
  pullbackTensorSystemComparison
  pullbackTensorSequenceBase integralComparisonSequenceBaseChange
  pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
  pullbackTensorSequenceInverse pullbackTensorSequenceAdjunction
  integralComparisonSequencePullback IntegralCoherence.generator
  integralComparisonSequenceGenerator sheafCompose Functor.sheafPushforwardContinuous

private local instance (priority := 10000) sequenceMonoidal (V : Scheme.{u}) :
    MonoidalCategory (coefficientSequenceModules l E V) :=
  SheafOfModules.monoidalCategory (coefficientSequenceCommRingSheaf l E V)
private local instance sequencePreadditive (V : Scheme.{u}) :
    MonoidalPreadditive (coefficientSequenceModules l E V) :=
  SheafOfModules.cochainModulesPreadditive (coefficientSequenceCommRingSheaf l E V)
private local instance sequenceColimits (V : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (coefficientSequenceModules l E V) := by
  with_unfolding_all infer_instance
private local instance sequenceLeftColim (V : Scheme.{u}) (M : coefficientSequenceModules l E V) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits (coefficientSequenceCommRingSheaf l E V) M
private local instance sequenceRightColim (V : Scheme.{u}) (M : coefficientSequenceModules l E V) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  SheafOfModules.cochainTensorRightPreservesColimits (coefficientSequenceCommRingSheaf l E V) M
private local instance sequenceTensor (V : Scheme.{u})
    (X Y : GradedObject ℤ (coefficientSequenceModules l E V)) : X.HasTensor Y := inferInstance
private local instance sequenceFour (V : Scheme.{u})
    (X Y Z U : GradedObject ℤ (coefficientSequenceModules l E V)) :
    GradedObject.HasTensor₄ObjExt X Y Z U := inferInstance
private local instance sequenceLeft (V : Scheme.{u})
    (X Y Z : GradedObject ℤ (coefficientSequenceModules l E V)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
private local instance sequenceRight (V : Scheme.{u})
    (X Y Z : GradedObject ℤ (coefficientSequenceModules l E V)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
private local instance (priority := 10000) complexMonoidal (V : Scheme.{u}) :
    MonoidalCategory (StrictQuotient.Complex l E V) := inferInstance

/-- The strict comparisons satisfy the cochain composition law, in the form of the total
tensor bifunctor.
Source: Stacks 07A4, 0D6D
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).
Proof: the generator-normalized strict comparisons are the components of
`sequenceComparison`, whose composition law is `sequenceComparison_compositionLaw`;
the total tensor of two maps is the monoidal tensor of the maps. -/
theorem comparison_composition {X Y Z : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (comparison l E (h ≫ f) P Q).hom ≫
        (coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology Z))
          (coefficientSequenceCommRingSheaf l E Z)).map
          (Prod.mkHom ((IntegralCoherence.compositor l E h f).hom.app P)
            ((IntegralCoherence.compositor l E h f).hom.app Q)) =
      (IntegralCoherence.compositor l E h f).hom.app
          ((coefficientTotalTensor.{u, u + 1, u}
            (coefficientSequenceTopology (Scheme.ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y)).obj (P, Q)) ≫
        ((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).map
          (comparison l E f P Q).hom ≫
        (comparison l E h
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj
            Q)).hom := by
  have hlaw := IntegralCoherence.sequenceComparison_compositionLaw l E h f P Q
  rw [completedComparisonStrictComparisonAux l E (h ≫ f),
    completedComparisonStrictComparisonAux l E f,
    completedComparisonStrictComparisonAux l E h,
    MonoidalCategory.tensorHom_def] at hlaw
  exact hlaw

end WeilConjectures.CompletedQuotient
