/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs

/-! # Naturality of normalized strict tensor comparisons

Source: Stacks 07A4 and 0941; the canonical integral comparison realization.
(blueprint: lem-pur-completed-comparison-tensorator-naturality).
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

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

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

private def coreTensorIso {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) (c : F.CoreMonoidal) :
    MonoidalCategory.tensor C ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor D := by
  let : F.Monoidal := c.toMonoidal
  exact (Functor.Monoidal.μNatIso F).symm

private theorem coreTensorIso_hom {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) (c : F.CoreMonoidal)
    (A : C × C) : (coreTensorIso F c).hom.app A = (c.μIso A.1 A.2).inv := rfl

attribute [local irreducible] coreTensorIso

private def tensorInterface (V : Scheme.{u}) :
    coefficientTotalTensor.{u, u+1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology V))
      (coefficientSequenceCommRingSheaf l E V) ≅
      MonoidalCategory.tensor (StrictQuotient.Complex l E V) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro A B w
    simp only [Iso.refl_hom]
    change (w.1 ▷ A.2 ≫ B.1 ◁ w.2) = w.1 ⊗ₘ w.2
    exact (tensorHom_def w.1 w.2).symm)

private theorem tensorInterface_hom (V : Scheme.{u})
    (A : StrictQuotient.Complex l E V × StrictQuotient.Complex l E V) :
    (tensorInterface l E V).hom.app A = 𝟙 _ := rfl

private theorem tensorInterface_inv (V : Scheme.{u})
    (A : StrictQuotient.Complex l E V × StrictQuotient.Complex l E V) :
    (tensorInterface l E V).inv.app A = 𝟙 _ := rfl

private def normalizedTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : IntegralCoherence.PullbackComparison l E f) :
    coefficientTotalTensor.{u, u+1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) ⋙ IntegralCoherence.pull l E f ≅
    (IntegralCoherence.pull l E f).prod (IntegralCoherence.pull l E f) ⋙
      coefficientTotalTensor.{u, u+1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X) :=
  Functor.isoWhiskerRight (tensorInterface l E Y) (IntegralCoherence.pull l E f) ≪≫
    coreTensorIso (IntegralCoherence.pull l E f) c.toCoreMonoidal ≪≫
    Functor.isoWhiskerLeft
      ((IntegralCoherence.pull l E f).prod (IntegralCoherence.pull l E f))
      (tensorInterface l E X).symm

private theorem normalizedTensor_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : IntegralCoherence.PullbackComparison l E f)
    (A : StrictQuotient.Complex l E Y × StrictQuotient.Complex l E Y) :
    (normalizedTensor l E f c).hom.app A = (c.tensor l E A.1 A.2).hom := by
  simp only [normalizedTensor, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    tensorInterface_hom, tensorInterface_inv, coreTensorIso_hom]
  erw [(IntegralCoherence.pull l E f).map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The normalized strong monoidal comparison is natural for the actual total
coefficient tensor bifunctor.
Source: Stacks 07A4; the strong monoidal naturality step of canonical comparison
identification (blueprint: lem-pur-completed-comparison-tensorator-naturality).
Proof: the project total tensor bifunctor and the monoidal tensor bifunctor have
an identity-component natural isomorphism, whose naturality is tensorHom_def.
Conjugate Mathlib's monoidal tensorator natural isomorphism by these two identity
comparisons. Its component is exactly the normalized tensor comparison. -/
theorem completedComparisonTensoratorNaturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : IntegralCoherence.PullbackComparison l E f) :
    ∃ e : coefficientTotalTensor.{u, u+1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) ⋙ IntegralCoherence.pull l E f ≅
      (IntegralCoherence.pull l E f).prod (IntegralCoherence.pull l E f) ⋙
        coefficientTotalTensor.{u, u+1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X),
      ∀ P Q : StrictQuotient.Complex l E Y, e.app (P,Q) = c.tensor l E P Q := by
  refine ⟨normalizedTensor l E f c, ?_⟩
  intro P Q
  apply Iso.ext
  exact normalizedTensor_hom l E f c (P,Q)

end WeilConjectures.CompletedQuotient
