/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonGeneratorTransport
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonTensoratorNaturality

/-! # Identification of normalized strict tensor comparisons

Source: Stacks 07A4 and 0941; the canonical integral comparison realization.
(blueprint: lem-pur-completed-comparison-strict-identification).
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

private theorem cancel_tensor_bridge {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) {F G : C ⥤ D}
    (b : F ≅ G) (e : T ⋙ G ≅ G.prod G ⋙ U) (A : C × C) :
    (b.app (T.obj A)).symm ≪≫
        ((Functor.isoWhiskerLeft T b ≪≫ e ≪≫
          Functor.isoWhiskerRight (NatIso.prod b.symm b.symm) U).app A) ≪≫
        U.mapIso (Iso.prod (b.app A.1) (b.app A.2)) = e.app A := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod_hom, NatTrans.prod,
    Functor.mapIso_hom, Iso.prod_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← U.map_comp, prod_comp, Iso.inv_hom_id_app, ← prod_id]
  exact (congrArg (e.hom.app A ≫ ·) (U.map_id _)).trans (Category.comp_id _)

/-- Source: Stacks 07A4 and 0941, generator normalization of the cochain comparison.
(blueprint: lem-pur-completed-comparison-strict-identification).
Proof: transport the normalized strong monoidal comparison across the equality of
sequence inverse-image functors. The adjunction units transport with that equality,
so the generator equations agree. Uniqueness fixes the resulting natural isomorphism.
Cancel the bridge and its tensor product to recover the displayed components. -/
theorem completedComparisonStrictComparisonAux {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : IntegralCoherence.PullbackComparison l E f)
    (P Q : StrictQuotient.Complex l E Y) :
    c.tensor l E P Q = comparison l E f P Q := by
  obtain ⟨e, he⟩ := completedComparisonTensoratorNaturality l E f c
  let T := coefficientTotalTensor.{u, u+1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y)
  let U := coefficientTotalTensor.{u, u+1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)
  let e' := Functor.isoWhiskerLeft T (pullBridge l E f) ≪≫ e ≪≫
    Functor.isoWhiskerRight (NatIso.prod (pullBridge l E f).symm
      (pullBridge l E f).symm) U
  have eh (A : StrictQuotient.Complex l E Y × StrictQuotient.Complex l E Y) :
      e.hom.app A = (c.tensor l E A.1 A.2).hom := congrArg Iso.hom (he A.1 A.2)
  have hbridge : e' = pullbackTensorSequenceCochain l E f := by
    apply (pullbackTensorSequenceCochain_existsUnique l E f).unique
    · intro A B p q k hpq V x y
      simp only [e', Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        NatIso.prod_hom, NatTrans.prod, Iso.symm_hom, eh]
      exact completedComparisonGeneratorTransport l E f c A B p q k hpq V x y
    · exact (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose_spec
  have hh := cancel_tensor_bridge T U (pullBridge l E f) e (P,Q)
  change ((pullBridge l E f).app (T.obj (P,Q))).symm ≪≫ e'.app (P,Q) ≪≫
    U.mapIso (Iso.prod ((pullBridge l E f).app P) ((pullBridge l E f).app Q)) =
      e.app (P,Q) at hh
  rw [hbridge] at hh
  unfold comparison
  exact (he P Q).symm.trans hh.symm

end WeilConjectures.CompletedQuotient
