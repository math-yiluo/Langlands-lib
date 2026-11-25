/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorUnitRepresentatives
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! The coherent unit comparison follows from the associativity comparison.

This module isolates the unit construction so that consumers of the completed
pullback comparison do not re-elaborate its large representative model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

section CoherentUnit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
universe a b c d
open MonoidalCategory

private theorem coherentAssociativity_from_tensorHom
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (h : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          (𝟙 (F.obj A) ⊗ₘ (μ.app (B, M)).hom) =
        (μ.app (A ⊗ B, M)).hom ≫ ((μ.app (A, B)).hom ⊗ₘ 𝟙 (F.obj M)) ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom) (A B M : C) :
    F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
        F.obj A ◁ (μ.app (B, M)).hom =
      (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
        (α_ (F.obj A) (F.obj B) (F.obj M)).hom := by
  have h' := h A B M
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h' ⊢
  simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using h'

private def coherentUnit_single (W : Scheme.{u}) :
    (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
      (DerivedCategory.singleFunctor (coefficientSequenceModules l E W) 0).obj
        (SheafOfModules.unit ((sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E W))) := by
  let S := (pullbackTensorCalculus l E W).systemClosed
  let h := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
  let S₀ := h.choose
  let h₀ := h.choose_spec.choose_spec.choose_spec.some
  let U := S₀.monoidal.tensorUnit
  let e := (S.adjunction U).leftAdjointUniq (S₀.adjunction U)
  exact (S₀.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    (e.app S.monoidal.tensorUnit).symm ≪≫ S.monoidal.leftUnitor U ≪≫ h₀.unitIso

private def coherentPullback_unit_object {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceDerived l E f).obj
        (pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l E X).systemClosed.monoidal.tensorUnit := by
  let φ := (show ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E Y)) ⟶
      ((pullbackTensorSequenceBase f).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E X)) from
      ⟨Functor.whiskerRight (pullbackTensorSequenceRing l E f).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
  letI : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    pullbackTensorSequenceDirect_rightAdjoint l E f
  letI : (pullbackTensorSequenceBase f).Final := by
    unfold pullbackTensorSequenceBase
    infer_instance
  let j : (pullbackTensorSequenceInverse l E f).obj
      (SheafOfModules.unit ((sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficientSequenceCommRingSheaf l E Y))) ≅
      SheafOfModules.unit ((sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficientSequenceCommRingSheaf l E X)) :=
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit φ)
      (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
        (F := pullbackTensorSequenceBase f) φ)
  exact (pullbackTensorSequenceDerived l E f).mapIso (coherentUnit_single l E Y) ≪≫
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (coefficientSequenceModules l E X) 0).mapIso j ≪≫
    (coherentUnit_single l E X).symm

attribute [local irreducible] pullbackTensorCalculus pullbackTensorSequenceDerived
  pullbackTensorSystemComparison coherentUnit_single coherentPullback_unit_object

/--
Both unit equations for the coherent μ used to define the integral comparison,
assuming the associativity equation for μ. The representative construction of
the unit is the one transported by the ordinary pullback of the coefficient
ring unit. Source: Stacks 03EL, 07A4, 0941 (blueprint:
lem-pur-completed-pullback-tensor-unit-from-associativity).
-/
theorem completedPullbackTensor_unit_of_associativity
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hA : ∀ M N P : coefficientSequenceDerived l E Y,
    (pullbackTensorSequenceDerived l E f).map
      ((pullbackTensorCalculus l E Y).systemClosed.monoidal.associator M N P).hom ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (M,(pullbackTensorCalculus l E Y).systemClosed.tensor.obj (N,P)) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) ((pullbackTensorSystemComparison l E f).hom.app (N,P))) =
    (pullbackTensorSystemComparison l E f).hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N),P) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((pullbackTensorSystemComparison l E f).hom.app (M,N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l E X).systemClosed.monoidal.associator
        ((pullbackTensorSequenceDerived l E f).obj M)
        ((pullbackTensorSequenceDerived l E f).obj N)
        ((pullbackTensorSequenceDerived l E f).obj P)).hom) :
    ∃ ε : (pullbackTensorSequenceDerived l E f).obj
        (pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l E X).systemClosed.monoidal.tensorUnit,
      ∀ M : coefficientSequenceDerived l E Y,
        ((pullbackTensorSystemComparison l E f).hom.app
          ((pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit,M) ≫
          (pullbackTensorCalculus l E X).systemClosed.tensor.map
            (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor
            ((pullbackTensorSequenceDerived l E f).obj M)).hom =
        (pullbackTensorSequenceDerived l E f).map
          ((pullbackTensorCalculus l E Y).systemClosed.monoidal.leftUnitor M).hom) ∧
        ((pullbackTensorSystemComparison l E f).hom.app
          (M,(pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit) ≫
          (pullbackTensorCalculus l E X).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor
            ((pullbackTensorSequenceDerived l E f).obj M)).hom =
        (pullbackTensorSequenceDerived l E f).map
          ((pullbackTensorCalculus l E Y).systemClosed.monoidal.rightUnitor M).hom) := by
  letI : MonoidalCategory (coefficientSequenceDerived l E Y) :=
    (pullbackTensorCalculus l E Y).systemClosed.monoidal
  letI : MonoidalCategory (coefficientSequenceDerived l E X) :=
    (pullbackTensorCalculus l E X).systemClosed.monoidal
  let F := pullbackTensorSequenceDerived l E f
  let μ := pullbackTensorSystemComparison l E f
  have hAssoc := coherentAssociativity_from_tensorHom F μ hA
  obtain ⟨ε, hL, hR⟩ := unit_from_tensor F μ
    (coherentPullback_unit_object l E f) hAssoc
  exact ⟨ε, fun M ↦ ⟨hL M, hR M⟩⟩

end CoherentUnit

end WeilConjectures
