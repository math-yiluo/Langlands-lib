/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality

/-! # Unit sections of the completed pullback evaluation mate

Source: Stacks Tags 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  pullbackTensorSequenceInverse pullbackTensorSystemComparison
  pullbackTensorInverseEvaluationComplex finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorCalculus pullbackTensorSequenceDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModulePullback

attribute [local instance] sfIntrinsicPullback_additive

attribute [local implicit_reducible] integralOperationsLevelPullback
  pullbackTensorSequenceDirect coefficientSequenceEvaluation

private theorem transport_heq {A B : AddCommGrpCat.{u}}
    (h : A = B) (x : A) : HEq ((eqToHom h) x) x := by
  cases h
  rfl

private theorem evaluation_section_heq (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    HEq (coefficientEvaluationSection l E W M n U x) x := by
  have h := transport_heq (coefficientSequenceEvaluationAb_eq l E W M n U).symm x
  exact h

private theorem coefficient_homEquiv_section_heq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    {A : normalizedDVRModules l E Y n} {B : normalizedDVRModules l E X n}
    (g : (integralOperationsLevelPullback l E f n).obj A ⟶ B)
    (U : Y.ProEt) (x : A.val.obj (op U)) :
    HEq (((coefficientProEtaleModuleAdjunction.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).homEquiv
        A B g).val.app (op U) x)
      (g.val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).unit.app A
            ).val.app (op U) x)) := by
  rfl

-- The section transports involve two presentations of the module underlying groups.
private theorem evaluation_mate_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E Y) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((pullbackTensorSequenceInverseEvaluation l E f n).hom.app M).val.app
      (op ((proEtaleBaseChange f).obj U))
      (((coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1}
          (finiteCoefficientRing l E (n + 1))))).unit.app
        ((coefficientSequenceEvaluation l E Y n).obj M)).val.app (op U)
        (coefficientEvaluationSection l E Y M n (op U) x)) =
    coefficientEvaluationSection l E X ((pullbackTensorSequenceInverse l E f).obj M)
      n (op ((proEtaleBaseChange f).obj U))
      (((pullbackTensorSequenceAdjunction l E f).unit.app M).val.app (op (n, U)) x) := by
  have h := (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose_spec M
  change (coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).homEquiv _ _
      ((pullbackTensorSequenceInverseEvaluation l E f n).hom.app M) = _ at h
  dsimp only [Functor.comp_obj] at h
  have hh := congrArg (fun a ↦ a.val.app (op U)
    (coefficientEvaluationSection l E Y M n (op U) x)) h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hh
  have hd := (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec
    ((pullbackTensorSequenceInverse l E f).obj M) U
      ((((coefficientSequenceEvaluation l E Y n).map
        ((pullbackTensorSequenceAdjunction l E f).unit.app M)).val.app (op U))
        (coefficientEvaluationSection l E Y M n (op U) x))
  have hm := evaluationSection_map l E Y
    ((pullbackTensorSequenceAdjunction l E f).unit.app M) n (op U) x
  have hms := evaluation_section_heq l E Y
    ((pullbackTensorSequenceDirect l E f).obj
      ((pullbackTensorSequenceInverse l E f).obj M)) n (op U)
    (((pullbackTensorSequenceAdjunction l E f).unit.app M).val.app (op (n, U)) x)
  have hmap : HEq
      ((((coefficientSequenceEvaluation l E Y n).map
        ((pullbackTensorSequenceAdjunction l E f).unit.app M)).val.app (op U))
        (coefficientEvaluationSection l E Y M n (op U) x))
      (((pullbackTensorSequenceAdjunction l E f).unit.app M).val.app (op (n, U)) x) :=
    (heq_of_eq hm).trans hms
  have hsection := evaluation_section_heq l E X
    ((pullbackTensorSequenceInverse l E f).obj M) n
    (op ((proEtaleBaseChange f).obj U))
    (((pullbackTensorSequenceAdjunction l E f).unit.app M).val.app (op (n, U)) x)
  have hh' : HEq _ _ := heq_of_eq hh
  have hdh : HEq _ _ := hd.trans hmap
  have hdh' : HEq _ _ := hdh.trans hsection.symm
  have hu := coefficient_homEquiv_section_heq l E f n
    ((pullbackTensorSequenceInverseEvaluation l E f n).hom.app M) U
    (coefficientEvaluationSection l E Y M n (op U) x)
  exact eq_of_heq (hu.symm.trans (hh'.trans hdh'))

private theorem evaluation_complex_f {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (A : CochainComplex (coefficientSequenceModules l E Y) ℤ) (p : ℤ) :
    (((pullbackTensorInverseEvaluationComplex l E f n).inv.app A) ≫
      (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)).f p =
    (pullbackTensorSequenceInverseEvaluation l E f n).inv.app (A.X p) ≫
      c.hom.app ((coefficientSequenceEvaluation l E Y n).obj (A.X p)) := by
  simp only [pullbackTensorInverseEvaluationComplex, Functor.comp_obj,
    Functor.mapHomologicalComplex_obj_X, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    NatIso.mapHomologicalComplex_inv_app_f, NatIso.mapHomologicalComplex_hom_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id]

private theorem moduleIso_inv_section
    {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (e : M ≅ N) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U)
    (h : e.hom.val.app U x = y) : e.inv.val.app U y = x :=
  (congrArg (fun z ↦ e.inv.val.app U z) h).symm.trans
    (congrArg (fun z : M ⟶ M ↦ z.val.app U x) e.hom_inv_id)

private theorem intrinsic_unit_map {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    {M N : normalizedDVRModules l E Y n} (a : M ⟶ N) (U : Y.ProEt)
    (x : M.val.obj (op U)) :
    (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).map a).val.app
      (op ((proEtaleBaseChange f).obj U)))
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op U) x) =
    ((sfIntrinsicConstantModuleAdjunction f
      (finiteCoefficientRing l E (n + 1))).unit.app N).val.app (op U)
      (a.val.app (op U) x) := by
  exact (congrArg (fun z ↦ z.val.app (op U) x)
    ((sfIntrinsicConstantModuleAdjunction f
      (finiteCoefficientRing l E (n + 1))).unit.naturality a)).symm

/-- The ordinary evaluation mate followed by c preserves adjunction-unit sections.
Source: Stacks Tags 0941 and 03D2
(blueprint: lem-pur-completed-pullback-tensor-evaluation-unit).
Proof: transpose the defining mate equality by the finite inverse-image adjunction.
The direct evaluation map is the identity on the underlying transported sections.
Naturality of evaluation identifies the image of the sequence unit. Apply the
inverse mate to that equality and then the supplied unit normalization hc.
-/
theorem completedPullbackTensor_evaluation_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (A : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : A.val.obj (op U)),
      (c.hom.app A).val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (n + 1))))).unit.app A).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app A).val.app (op U) x)
    (M : coefficientSequenceModules l E Y) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :
    (((pullbackTensorSequenceInverseEvaluation l E f n).inv.app M ≫
      c.hom.app ((coefficientSequenceEvaluation l E Y n).obj M)).val.app
        (op ((proEtaleBaseChange f).obj U)))
      (coefficientEvaluationSection l E X ((pullbackTensorSequenceInverse l E f).obj M)
        n (op ((proEtaleBaseChange f).obj U))
        (((pullbackTensorSequenceAdjunction l E f).unit.app M).val.app (op (n, U)) x)) =
    ((sfIntrinsicConstantModuleAdjunction f
      (finiteCoefficientRing l E (n + 1))).unit.app
        ((coefficientSequenceEvaluation l E Y n).obj M)).val.app (op U)
      (coefficientEvaluationSection l E Y M n (op U) x) := by
  change (c.hom.app _).val.app _
    (((pullbackTensorSequenceInverseEvaluation l E f n).inv.app M).val.app _ _) = _
  erw [moduleIso_inv_section ((pullbackTensorSequenceInverseEvaluation l E f n).app M)
    _ _ _ (evaluation_mate_unit l E f n M U x)]
  exact hc _ U _

private theorem evaluation_complex_unit {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (A : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : A.val.obj (op U)),
      (c.hom.app A).val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (n + 1))))).unit.app A).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app A).val.app (op U) x)
    (A : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (i : ℤ) (U : Y.ProEt) (x : (A.X i).val.obj (op (n, U))) :
    ((((pullbackTensorInverseEvaluationComplex l E f n).inv.app A ≫
      (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)).f
          i).val.app (op ((proEtaleBaseChange f).obj U)))
      (coefficientEvaluationSection l E X
        ((pullbackTensorSequenceInverse l E f).obj (A.X i)) n
        (op ((proEtaleBaseChange f).obj U))
        (((pullbackTensorSequenceAdjunction l E f).unit.app (A.X i)).val.app (op (n, U)) x)) =
    ((sfIntrinsicConstantModuleAdjunction f
      (finiteCoefficientRing l E (n + 1))).unit.app
        ((coefficientSequenceEvaluation l E Y n).obj (A.X i))).val.app (op U)
      (coefficientEvaluationSection l E Y (A.X i) n (op U) x) := by
  erw [evaluation_complex_f]
  exact completedPullbackTensor_evaluation_unit l E f n c hc _ U x

end WeilConjectures
