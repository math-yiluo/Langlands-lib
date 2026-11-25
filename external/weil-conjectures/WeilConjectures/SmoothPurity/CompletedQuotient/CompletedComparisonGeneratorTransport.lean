/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs

/-! # Transport of strict comparison generators

Source: Stacks 07A4 and 0941; the canonical integral comparison realization.
(blueprint: lem-pur-completed-comparison-generator-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
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

private def sequenceDirect {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : coefficientSequenceCommRingSheaf l E Y ⟶
      ((pullbackTensorSequenceBase f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X)) :=
  SheafOfModules.pushforward.{u + 1} (F := pullbackTensorSequenceBase f)
    (J := coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (K := coefficientSequenceTopology (Scheme.ProEt.topology X))
    (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E Y))
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E X))
    ⟨Functor.whiskerRight r.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private def generatorNorm {X Y : Scheme.{u}} (f : X ⟶ Y) (r)
    (hG : (sequenceDirect l E f r).IsRightAdjoint)
    (a : letI := hG
      ∀ P Q : StrictQuotient.Complex l E Y,
        ((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).obj
            ((coefficientTotalTensor.{u, u + 1, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q)) ≅
          (coefficientTotalTensor.{u, u + 1, u}
            (coefficientSequenceTopology (Scheme.ProEt.topology X))
            (coefficientSequenceCommRingSheaf l E X)).obj
            (((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).obj P,
              ((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).obj
                Q)) : Prop := by
  letI := hG
  exact ∀ (P Q : StrictQuotient.Complex l E Y) (p q k : ℤ) (h : p + q = k)
    (V : ℕ × Y.ProEt) (x : (P.X p).val.obj (op V))
    (y : (Q.X q).val.obj (op V)),
    (((a P Q).hom.f k).val.app
        (op ((pullbackTensorSequenceBase f).obj V)))
      ((((Adjunction.ofIsRightAdjoint (sequenceDirect l E f r)).unit.app
        (((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q)).X k)).val.app
            (op V))
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) P Q p q k h (op V) x y)) =
    coefficientTensorGenerator.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X)
      (((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).obj P)
      (((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).obj Q)
      p q k h (op ((pullbackTensorSequenceBase f).obj V))
      ((((Adjunction.ofIsRightAdjoint (sequenceDirect l E f r)).unit.app (P.X p)).val.app
        (op V)) x)
      ((((Adjunction.ofIsRightAdjoint (sequenceDirect l E f r)).unit.app (Q.X q)).val.app
        (op V)) y)

private theorem generatorNorm_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r r') (hr : (sequenceDirect l E f r).IsRightAdjoint)
    (hr' : (sequenceDirect l E f r').IsRightAdjoint) (e : r = r')
    (eF : @Functor.leftAdjoint _ _ _ _ (sequenceDirect l E f r) hr =
      @Functor.leftAdjoint _ _ _ _ (sequenceDirect l E f r') hr')
    (a : letI := hr
      ∀ P Q : StrictQuotient.Complex l E Y,
        ((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).obj
            ((coefficientTotalTensor.{u, u + 1, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q)) ≅
          (coefficientTotalTensor.{u, u + 1, u}
            (coefficientSequenceTopology (Scheme.ProEt.topology X))
            (coefficientSequenceCommRingSheaf l E X)).obj
            (((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).obj P,
              ((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ)).obj Q)) :
    generatorNorm l E f r hr a →
      generatorNorm l E f r' hr'
        (fun P Q ↦
          ((NatIso.mapHomologicalComplex (eqToIso eF) (.up ℤ)).app
            ((coefficientTotalTensor.{u, u + 1, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q))).symm ≪≫
            a P Q ≪≫
          (coefficientTotalTensor.{u, u + 1, u}
            (coefficientSequenceTopology (Scheme.ProEt.topology X))
            (coefficientSequenceCommRingSheaf l E X)).mapIso
              (Iso.prod
                ((NatIso.mapHomologicalComplex (eqToIso eF) (.up ℤ)).app P)
                ((NatIso.mapHomologicalComplex (eqToIso eF) (.up ℤ)).app Q))) := by
  intro ha
  subst r'
  have hi : NatIso.mapHomologicalComplex (eqToIso eF) (.up ℤ) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext A
    apply HomologicalComplex.hom_ext
    intro i
    simp
  rw [hi]
  have he (P Q : StrictQuotient.Complex l E Y) :
      ((Iso.refl ((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex (.up ℤ))).app
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj (P, Q))).symm ≪≫
        a P Q ≪≫
        (coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)).mapIso
            (Iso.prod
              ((Iso.refl ((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex
                (.up ℤ))).app P)
              ((Iso.refl ((sequenceDirect l E f r).leftAdjoint.mapHomologicalComplex
                (.up ℤ))).app Q)) = a P Q := by
    apply Iso.ext
    simp
  simp only [he]
  exact ha

private theorem mapComplex_eqToIso_symm
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F = G) :
    NatIso.mapHomologicalComplex (eqToIso e.symm) (.up ℤ) =
      (NatIso.mapHomologicalComplex (eqToIso e) (.up ℤ)).symm := by
  subst G
  rfl

/-- Generator normalization after transport across the sequence pullback bridge.
Source: Stacks 07A4 and 0941; the generator-normalization step of canonical
comparison identification (blueprint: lem-pur-completed-comparison-generator-transport).
Proof: equality of the constant-section ring maps identifies the direct images.
Eliminate that equality with the right-adjoint and additivity proofs retained as
parameters. Proof irrelevance identifies these proofs with their recorded values.
The chosen inverse image, its adjunction unit and the cochain bridge then reduce
to the same expressions. The assertion is the generator field of the normalized
strict monoidal comparison. -/
theorem completedComparisonGeneratorTransport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : IntegralCoherence.PullbackComparison l E f)
    (P Q : StrictQuotient.Complex l E Y) (p q k : ℤ) (hpq : p + q = k)
    (V : ℕ × Y.ProEt) (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)) :
    let b := pullBridge l E f
    let T := coefficientTotalTensor.{u, u+1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)
    let U := coefficientTotalTensor.{u, u+1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X)
    (((b.hom.app (T.obj (P,Q)) ≫ (c.tensor l E P Q).hom ≫
        U.map (Prod.mkHom (b.inv.app P) (b.inv.app Q))).f k).val.app
        (op ((pullbackTensorSequenceBase f).obj V)))
      ((((pullbackTensorSequenceAdjunction l E f).unit.app
        ((T.obj (P,Q)).X k)).val.app (op V))
        (coefficientTensorGenerator.{u, u+1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) P Q p q k hpq (op V) x y)) =
    coefficientTensorGenerator.{u, u+1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X)
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P)
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj Q)
      p q k hpq (op ((pullbackTensorSequenceBase f).obj V))
      ((((pullbackTensorSequenceAdjunction l E f).unit.app (P.X p)).val.app (op V)) x)
      ((((pullbackTensorSequenceAdjunction l E f).unit.app (Q.X q)).val.app (op V)) y) := by
  rcases V with ⟨n, V⟩
  have hr : pullbackTensorSequenceRing l E f =
      integralComparisonSequenceRingMap l E f := by
    unfold pullbackTensorSequenceRing pullbackTensorSequenceRingMap
    rfl
  let rI := integralComparisonSequenceRingMap l E f
  let rP := pullbackTensorSequenceRing l E f
  have hI : (sequenceDirect l E f rI).IsRightAdjoint := by
    change (integralComparisonSequenceDirectImage l E f).IsRightAdjoint
    exact integralComparisonSequenceDirectImage_isRightAdjoint l E f
  have hP : (sequenceDirect l E f rP).IsRightAdjoint := by
    change (pullbackTensorSequenceDirect l E f).IsRightAdjoint
    exact pullbackTensorSequenceDirect_rightAdjoint l E f
  have eF :
      @Functor.leftAdjoint _ _ _ _ (sequenceDirect l E f rI) hI =
        @Functor.leftAdjoint _ _ _ _ (sequenceDirect l E f rP) hP := by
    change integralComparisonSequencePullback l E f =
      pullbackTensorSequenceInverse l E f
    exact (sequencePullback_eq l E f).symm
  have ht := generatorNorm_transport l E f
    rI rP hI hP hr.symm eF
    (fun A B ↦ (c.μIso A B).symm)
  have hs := ht (by
    unfold generatorNorm
    intro P Q p q k hpq V x y
    exact c.generators P Q p q k hpq V.1 V.2 x y)
  have hbridge :
      NatIso.mapHomologicalComplex
          (eqToIso eF) (.up ℤ) =
        (pullBridge l E f).symm := by
    unfold pullBridge
    exact mapComplex_eqToIso_symm (sequencePullback_eq l E f)
  unfold generatorNorm at hs
  specialize hs P Q p q k hpq (n, V) x y
  rw [hbridge] at hs
  dsimp only [rI, rP] at hs ⊢
  simp only [Iso.trans_hom, Iso.symm_hom] at hs
  dsimp only [sequenceDirect, pullbackTensorSequenceDirect,
    pullbackTensorSequenceAdjunction, pullbackTensorSequenceInverse,
    IntegralCoherence.PullbackComparison.tensor] at hs ⊢
  exact hs

end WeilConjectures.CompletedQuotient
