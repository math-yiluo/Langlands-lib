/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonCanonicalSquare
import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralStrictPullbackComparisons
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonStrictComparisonAux

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
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
  coefficientSequenceLimit Functor.mapDerivedCategory

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

private theorem strictCoherence {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y) :
    StrictCoherence l E h f := by
  obtain ⟨c, hc, hcomp⟩ :=
    IntegralCoherence.strictPullbackComparisons l E (fun V : Scheme.{u} ↦ V)
  unfold StrictCoherence
  refine ⟨c f, c h, c (h ≫ f), hc f, hc h, hc (h ≫ f), hcomp h f, ?_, ?_, ?_⟩
  · exact completedComparisonStrictComparisonAux l E f (c f)
  · exact completedComparisonStrictComparisonAux l E h (c h)
  · exact completedComparisonStrictComparisonAux l E (h ≫ f) (c (h ≫ f))

private def integralComparisonIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralTensor l E Y ⋙ constructibleIntegralPullback l E f ≅
      (constructibleIntegralPullback l E f).prod (constructibleIntegralPullback l E f) ⋙
        constructibleIntegralTensor l E X := by
  let I := (sfIntegralConstructible l E Y).ι
  let R := I ⋙ (pullbackTensorCalculus l E Y).reduction
  let F := pullbackTensorSequenceDerived l E f
  let LY := coefficientSequenceLimit l E Y
  let LX := coefficientSequenceLimit l E X
  let TY := (pullbackTensorCalculus l E Y).systemClosed.tensor
  let TX := (pullbackTensorCalculus l E X).systemClosed.tensor
  let RX := (pullbackTensorCalculus l E X).reduction
  let P := I ⋙ integralDerivedPullback l E f
  let a : P ≅ R ⋙ F ⋙ LX :=
    Functor.isoWhiskerLeft I (pullbackTensorIntegralPullbackModel l E f)
  let b : (I.prod I) ⋙ integralCompletedTensor l E Y ≅ (R.prod R) ⋙ TY ⋙ LY :=
    Functor.isoWhiskerLeft (I.prod I) (pullbackTensorIntegralTensorModel l E Y)
  let cy : (R.prod R) ⋙ TY ⋙ LY ⋙ (pullbackTensorCalculus l E Y).reduction ≅
      (R.prod R) ⋙ TY :=
    NatIso.ofComponents (fun MN ↦ by
      letI : IsIso ((pullbackTensorCalculus l E Y).adjunction.counit.app
          (TY.obj (R.obj MN.1, R.obj MN.2))) :=
        (pullbackTensorComparisonCounits l E f MN.1 MN.2).1
      exact asIso ((pullbackTensorCalculus l E Y).adjunction.counit.app
        (TY.obj (R.obj MN.1, R.obj MN.2))))
      (by
        intro MN MN' g
        simpa only [LY, Functor.comp_map, Functor.prod_map, Functor.id_map, asIso_hom] using
          (pullbackTensorCalculus l E Y).adjunction.counit.naturality
            (TY.map (Prod.mkHom (R.map g.1) (R.map g.2))))
  let cx : R ⋙ F ⋙ LX ⋙ RX ≅ R ⋙ F :=
    NatIso.ofComponents (fun M ↦ by
      letI : IsIso ((pullbackTensorCalculus l E X).adjunction.counit.app
          (F.obj (R.obj M))) := (pullbackTensorComparisonCounits l E f M M).2.1
      exact asIso ((pullbackTensorCalculus l E X).adjunction.counit.app (F.obj (R.obj M))))
      (by
        intro M M' g
        simpa only [LX, RX, Functor.comp_map, Functor.id_map, asIso_hom] using
          (pullbackTensorCalculus l E X).adjunction.counit.naturality (F.map (R.map g)))
  let e : ((I.prod I) ⋙ integralCompletedTensor l E Y) ⋙ integralDerivedPullback l E f ≅
      (P.prod P) ⋙ integralCompletedTensor l E X :=
    Functor.isoWhiskerLeft ((I.prod I) ⋙ integralCompletedTensor l E Y)
        (pullbackTensorIntegralPullbackModel l E f) ≪≫
      Functor.isoWhiskerRight b
        ((pullbackTensorCalculus l E Y).reduction ⋙ F ⋙ LX) ≪≫
      Functor.isoWhiskerRight cy (F ⋙ LX) ≪≫
      Functor.isoWhiskerLeft (R.prod R)
        (Functor.isoWhiskerRight (pullbackTensorSystemComparison l E f) LX) ≪≫
      Functor.isoWhiskerRight (NatIso.prod cx.symm cx.symm) (TX ⋙ LX) ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (Functor.isoWhiskerRight a.symm RX)
          (Functor.isoWhiskerRight a.symm RX)) (TX ⋙ LX) ≪≫
      Functor.isoWhiskerLeft (P.prod P) (pullbackTensorIntegralTensorModel l E X).symm
  exact NatIso.ofComponents
    (fun MN ↦ ObjectProperty.isoMk _ (e.app MN))
    (fun g ↦ ObjectProperty.hom_ext _ (e.hom.naturality g))

private theorem integralComparisonIso_app
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonIso l E f).app (M,N) =
      canonicalIntegralPullbackTensor l E f M N := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  simp only [integralComparisonIso, canonicalIntegralPullbackTensor,
    pullbackTensorReferenceComparison, ObjectProperty.isoMk, Iso.app_hom, Iso.app_inv,
    ObjectProperty.ι_obj,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    NatTrans.comp_app, NatIso.prod_hom, NatTrans.prod,
    asIso_hom, asIso_inv, Iso.prod_hom, ObjectProperty.homMk,
    pullbackTensorReferencePullback, pullbackTensorReferenceTensor,
    Functor.comp_obj, Functor.prod_obj, Functor.comp_map, Functor.prod_map,
    Category.assoc]

private theorem naturalComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] : NaturalComparison l E f := by
  intro M N M' N' a b
  have e := (integralComparisonIso l E f).hom.naturality
    (Prod.mkHom (ObjectProperty.homMk a) (ObjectProperty.homMk b))
  have e' := congrArg (fun k ↦ k.hom) e
  change (integralDerivedPullback l E f).map
      ((integralCompletedTensor l E Y).map (Prod.mkHom a b)) ≫
      ((integralComparisonIso l E f).app (M', N')).hom.hom =
    ((integralComparisonIso l E f).app (M, N)).hom.hom ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom ((integralDerivedPullback l E f).map a)
          ((integralDerivedPullback l E f).map b)) at e'
  rw [integralComparisonIso_app, integralComparisonIso_app] at e'
  exact e'

/-- Identification of the strict comparison and its coherent completed image.
Source: realization proof steps 2, 3 and 5; Stacks 07A4 and 0D6D
(blueprint: lem-pur-completed-comparison-canonical-identification).

Proof: the equality of the two sequence inverse-image interfaces transports the
generator-normalized cochain pullback tensor comparison. Its tensor generators
uniquely fix it, so it agrees with the recorded sequence cochain comparison.
The descended system comparison satisfies its K-flat normalization equation.
Insert the tensor and pullback primitive realization formulas into the recursive
substitutions at the source and target. Naturality moves each reduction-model
map through the tensor and inverse-image functors. Effective counits cancel
against their inverses; the remaining composite is precisely the defining
canonicalIntegralPullbackTensor composite. Generator normalization also supplies
the strong monoidal, signed symmetry and composition equations for the three
pullbacks. Transport along the same interface equality gives StrictCoherence.
Apply this at both coefficients. Naturality of the descended system comparison,
primitive natural isomorphisms and counits gives NaturalComparison for arbitrary
derived input maps, without choosing representatives for those maps. -/
theorem completedComparisonCanonicalIdentification
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A)) :
    (transport l E P (fun i ↦ (M i).obj) φ good invertible
      (sourceExpression h f) (targetExpression h f)
      (comparison l E f (quotient l E (P 0).obj) (quotient l E (P 1).obj)).hom =
        (canonicalIntegralPullbackTensor l E f (M 0) (M 1)).hom.hom) ∧
    StrictCoherence l E h f ∧ StrictCoherence l L h f ∧
    NaturalComparison l E f ∧ NaturalComparison l L f := by
  refine ⟨?_, ?_, ?_, naturalComparison l E f, naturalComparison l L f⟩
  · let β := fun i : Fin 3 ↦ substitution l E P (fun j ↦ (M j).obj) φ good
        (.input i)
    have hs := completedComparisonCanonicalSquare l E f (M 0) (M 1)
      (quotient l E (P 0).obj) (quotient l E (P 1).obj)
      (good (.input 0)) (good (.input 1))
      (good (.pullF (.input 0))) (good (.pullF (.input 1))) (β 0) (β 1)
    let := invertible (targetExpression h f)
    have hi := IsIso.inv_hom_id
      (substitution l E P (fun i ↦ (M i).obj) φ good (targetExpression h f))
    unfold transport
    apply (cancel_mono (substitution l E P (fun i ↦ (M i).obj) φ good
      (targetExpression h f))).1
    simp only [asIso_inv, Category.assoc, hi, Category.comp_id]
    simp only [substitution, substituteInputs, sourceExpression,
      targetExpression, β, strictValue] at hs ⊢
    exact hs
  · exact strictCoherence l E h f
  · exact strictCoherence l L h f

end WeilConjectures.CompletedQuotient
