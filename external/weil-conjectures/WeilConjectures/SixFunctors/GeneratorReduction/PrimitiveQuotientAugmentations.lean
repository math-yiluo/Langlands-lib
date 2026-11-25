/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.GeneratorReduction.TensorQuotientAugmentationOnGood
import WeilConjectures.SixFunctors.GeneratorReduction.PullQuotientAugmentationOnGood
import WeilConjectures.SixFunctors.GeneratorReduction.FiniteReductionCompletionUnit
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
/-! # Quotient augmentations of primitive operations

Source: current blueprint fix-prop-coherence, primitive comparisons
(blueprint: lem-sf-primitive-quotient-augmentations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem goodRepresentative (X : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E X)) :
    ∃ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let q := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  let : q.IsLocalization W := goodComplexes_isLocalization
    (completedIntegralCommRingSheafUnrestricted l E X)
    (integralOperationsGoodComplex l E X) (fun _ ↦ Iff.rfl)
  let : q.EssSurj := Localization.essSurj q W
  exact ⟨q.objPreimage K, ⟨q.objObjPreimageIso K⟩⟩

private theorem app_eq_of_iso {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (α β : F ⟶ G) {P K : A} (e : P ≅ K)
    (h : α.app P = β.app P) : α.app K = β.app K := by
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality, β.naturality, h]

private theorem reduction_completionUnit_isIso (X : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E X)) :
    IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
      ((IntegralOnSlice.completionUnit l E X none).app K)) := by
  let S := IntegralSystemRealization.calculus l E X
  apply (S.isIso_iff_evaluations _).2
  intro n
  have := finiteReduction_completionUnit l E X K n
  let e := S.reductionEvaluation n
  have h := e.hom.naturality ((IntegralOnSlice.completionUnit l E X none).app K)
  dsimp only [Functor.comp_map] at h
  have hi : IsIso ((coefficientSequenceDerivedEvaluation l E X n).map
      (S.reduction.map ((IntegralOnSlice.completionUnit l E X none).app K)) ≫
        e.hom.app ((IntegralOnSlice.completion l E X none).obj K)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)

private theorem tensor_augmentation_onGood
    (ringed : IntegralSystemRealization.RingedModels l E) (X : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    ((ringed.tensor X).chi l E).app (DerivedCategory.Q.obj P.obj,
        DerivedCategory.Q.obj Q.obj) ≫
      (pullbackTensorIntegralTensorModel l E X).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      (IntegralSystemRealization.calculus l E X).adjunction.unit.app
        ((ringed.tensor X).ordinary.tensor.obj
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
      (coefficientSequenceLimit l E X).map
        ((IntegralSystemRealization.calculus l E X).reduction.map
          (eqToIso (congrArg (fun T ↦ T.obj
            (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
              (ringed.tensorClosed X))).hom ≫
          (IntegralSystemRealization.calculus l E X).reductionTensor.hom.app
            (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) := by
  let t := ringed.tensor X
  let e := pullbackTensorReferenceTensorModel l E X P Q
  have hm : (pullbackTensorIntegralTensorModel l E X).hom.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫ e.hom =
      (integralCompletedTensorComparison l E X).hom.app (P, Q) := by
    have h := congrArg Iso.hom
      ((pullbackTensorIntegralTensorModel_existsUnique l E X).exists.choose_spec P Q)
    simpa only [pullbackTensorIntegralTensorModel, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, e] using
      congrArg (fun z ↦ z ≫ e.hom) h
  apply (cancel_epi (t.ordinary.representative.hom.app
    (⟨P.obj, P.property⟩, ⟨Q.obj, Q.property⟩))).1
  apply (cancel_mono e.hom).1
  simp only [Category.assoc]
  rw [hm]
  have hc := t.canonical.2 P.obj Q.obj P.property Q.property
  have ht := tensorQuotientTranspose_onGood l E ringed X P Q
  simpa only [OpenFactorCoherence.Tensor.chi, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc, t, e] using hc.trans ht.symm

private theorem pull_augmentation_onGood
    (ringed : IntegralSystemRealization.RingedModels l E)
    (system : IntegralSystemRealization.Operations l E)
    (realization : IntegralSystemRealization.RealizationModel l E system)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    ((ringed.pull f).unit l E).app (DerivedCategory.Q.obj P.obj) ≫
      (pullbackTensorIntegralPullbackModel l E f).hom.app (DerivedCategory.Q.obj P.obj) =
      (IntegralSystemRealization.calculus l E X).adjunction.unit.app
        ((IntegralSystemRealization.ringedPull l E f).obj (DerivedCategory.Q.obj P.obj)) ≫
      (coefficientSequenceLimit l E X).map
        ((realization.reductionPull f).hom.app (DerivedCategory.Q.obj P.obj)) := by
  let p := ringed.pull f
  let e := pullbackTensorReferencePullbackModel l E f P
  have hm : (pullbackTensorIntegralPullbackModel l E f).hom.app
      (DerivedCategory.Q.obj P.obj) ≫ e.hom =
      (integralDerivedPullbackComparison l E f).hom.app P := by
    have h := congrArg Iso.hom
      ((pullbackTensorIntegralPullbackModel_existsUnique l E f).exists.choose_spec P)
    simpa only [pullbackTensorIntegralPullbackModel, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, e] using
      congrArg (fun z ↦ z ≫ e.hom) h
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, OpenFactorCoherence.Pull.unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [hm, p.model P.obj P.property]
  rw [← Category.assoc, ← Category.assoc]
  rw [← (IntegralOnSlice.completionUnit l E X none).naturality]
  simp only [Functor.id_map, Category.assoc]
  have hu := (IntegralOnSlice.completionUnit_existsUnique l E X none).exists.choose_spec
    (⟨(OpenFactorCoherence.pullCx l E f).obj P.obj, p.good P.obj P.property⟩)
  change (IntegralOnSlice.completionUnit l E X none).app _ ≫ _ = _ at hu
  have hu' := congrArg (fun z ↦
    (IntegralSystemRealization.integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app
        P.obj ≫ z ≫
      DerivedCategory.Q.map (integralOperationsRoosMap (p.tower.hom.app P.obj))) hu
  simpa only [Category.assoc, p, e, OpenFactorCoherence.star,
    OpenFactorCoherence.pullCx, IntegralSystemRealization.integralOrdinaryPull,
    IntegralOnSlice.qGood, Functor.comp_obj, ObjectProperty.ι_obj] using
    hu'.trans (pullQuotientTranspose_onGood l E system realization f p P).symm

/-- The normalized ordinary tensor augmentation realizes the reduction-tensor map.
Source: current blueprint, fix-prop-coherence.proof.md, maps-used sentence;
Stacks Tags 07A4, 07A6 and 0941
(blueprint: lem-sf-primitive-quotient-augmentations).

Proof: first work on good flat-term K-flat complexes. The strict tensor
transpose calculation identifies the reconstruction composite in the full reference
Roos coordinates. Tensor.canonical.2 computes the quotient augmentation in those
same coordinates. The defining global tensor realization and cancellation of the
ordinary tensor representative identify these maps. For pullback, the strict
transpose calculation is combined with Pull.model, naturality of completionUnit,
and its defining good-representative equation. Cancel the full reference pullback
Roos isomorphism. Both equations are natural transformations, so representative
isomorphisms from the resolving-class localization extend them to arbitrary objects.
Finite scalar extension inverts completionUnit. Naturality of reductionEvaluation
and joint conservativity imply invertibility of its whole reduction. Both primitive
comparisons are completionUnit followed by the specified comparison isomorphism,
so their reductions are invertible too. No completeness or boundedness of the
inputs, or invertibility of l on the schemes, is assumed. -/
theorem primitiveQuotientAugmentations (ringed : IntegralSystemRealization.RingedModels l E)
    (system : IntegralSystemRealization.Operations l E)
    (realization : IntegralSystemRealization.RealizationModel l E system) :
    (∀ (X : Scheme.{u}) (K L : DerivedCategory (scalarReductionSource l E X)),
    IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
      (((ringed.tensor X).chi l E).app (K, L))) ∧
    ((ringed.tensor X).chi l E).app (K, L) ≫
      (pullbackTensorIntegralTensorModel l E X).hom.app (K, L) =
      (IntegralSystemRealization.calculus l E X).adjunction.unit.app
        ((ringed.tensor X).ordinary.tensor.obj (K, L)) ≫
      (coefficientSequenceLimit l E X).map
        ((IntegralSystemRealization.calculus l E X).reduction.map
          (eqToIso (congrArg (fun T ↦ T.obj (K, L)) (ringed.tensorClosed X))).hom ≫
          (IntegralSystemRealization.calculus l E X).reductionTensor.hom.app (K, L))) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : DerivedCategory (scalarReductionSource l E Y)),
    IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
      (((ringed.pull f).unit l E).app K)) ∧
    ((ringed.pull f).unit l E).app K ≫ (pullbackTensorIntegralPullbackModel l E f).hom.app K =
      (IntegralSystemRealization.calculus l E X).adjunction.unit.app
        ((IntegralSystemRealization.ringedPull l E f).obj K) ≫
      (coefficientSequenceLimit l E X).map ((realization.reductionPull f).hom.app K)) := by
  constructor
  · intro X K L
    constructor
    · have := reduction_completionUnit_isIso l E X
        ((ringed.tensor X).ordinary.tensor.obj (K, L))
      change IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
        ((IntegralOnSlice.completionUnit l E X none).app
          ((ringed.tensor X).ordinary.tensor.obj (K, L)) ≫
          (ringed.tensor X).comparison.hom.app (K, L)))
      rw [Functor.map_comp]
      infer_instance
    · let S := IntegralSystemRealization.calculus l E X
      let T := (ringed.tensor X).ordinary.tensor
      let r : T ⋙ S.reduction ⟶
          S.reduction.prod S.reduction ⋙ S.systemClosed.tensor :=
        Functor.whiskerRight (eqToHom (ringed.tensorClosed X)) S.reduction ≫
          S.reductionTensor.hom
      let α := (ringed.tensor X).chi l E ≫
        (pullbackTensorIntegralTensorModel l E X).hom
      let β := Functor.whiskerLeft T S.adjunction.unit ≫
        Functor.whiskerRight r (coefficientSequenceLimit l E X)
      obtain ⟨P, ⟨eP⟩⟩ := goodRepresentative l E X K
      obtain ⟨Q, ⟨eQ⟩⟩ := goodRepresentative l E X L
      suffices h : α.app (K, L) = β.app (K, L) by
        simpa only [α, β, r, S, T, eqToIso.hom, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.whiskerRight_app, eqToHom_app, ← Functor.map_comp] using h
      apply app_eq_of_iso α β (Iso.prod eP eQ)
      simpa only [α, β, r, S, T, eqToIso.hom, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, eqToHom_app, ← Functor.map_comp] using
        tensor_augmentation_onGood l E ringed X P Q
  · intro X Y f K
    constructor
    · have := reduction_completionUnit_isIso l E X
        ((IntegralSystemRealization.ringedPull l E f).obj K)
      change IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
        ((IntegralOnSlice.completionUnit l E X none).app
          ((IntegralSystemRealization.ringedPull l E f).obj K) ≫
          (ringed.pull f).comparison.hom.app K))
      rw [Functor.map_comp]
      infer_instance
    · let S := IntegralSystemRealization.calculus l E X
      let α := (ringed.pull f).unit l E ≫
        (pullbackTensorIntegralPullbackModel l E f).hom
      let β := Functor.whiskerLeft (IntegralSystemRealization.ringedPull l E f)
          S.adjunction.unit ≫
        Functor.whiskerRight (realization.reductionPull f).hom (coefficientSequenceLimit l E X)
      obtain ⟨P, ⟨eP⟩⟩ := goodRepresentative l E Y K
      change α.app K = β.app K
      apply app_eq_of_iso α β eP
      exact pull_augmentation_onGood l E ringed system realization f P

end WeilConjectures.GeneratorReduction
