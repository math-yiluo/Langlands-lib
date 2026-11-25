/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicScalarLocalizationComparison
import Mathlib.CategoryTheory.Shift.Localization

/-! # The rational section-valued tensor cocone

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option linter.all false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

private theorem commShift_of_localization
    {A B D : Type*} [Category A] [Category B] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift D ℤ]
    (Q : A ⥤ B) (W : MorphismProperty A) [Q.IsLocalization W]
    [Q.CommShift ℤ] {F G : B ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift (Functor.whiskerLeft Q τ) ℤ] :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  apply Localization.natTrans_ext Q W
  intro K
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft Q τ) n K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  rw [← τ.naturality_assoc] at h
  exact (cancel_epi (F.map ((Q.commShiftIso n).hom.app K))).mp h

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]
variable (C : CoefficientSystem l X)
attribute [local irreducible] integralTensor rationalTensor

/-- The integral factorization of a rational transition followed by realization.
Source: Stacks Tag 05R6 (blueprint: lem-sf-native-rational-tensor-cocone). -/
def rationalTensorTransitionLift {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    stageLocalization l X E ⋙
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙
        rationalTensor l X C L ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h ⋙
        integralTensor l X C L :=
  (Functor.associator (stageLocalization l X E)
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h)
      (rationalTensor l X C L)).symm ≪≫
    Functor.isoWhiskerRight (rationalIntegralTransition l X h) (rationalTensor l X C L) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rationalTensorIntegral l X C L)

instance rationalTensorTransitionLift_shift {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    NatTrans.CommShift (rationalTensorTransitionLift l X C h).hom ℤ := by
  dsimp only [rationalTensorTransitionLift, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

instance rationalTensorTransition_lifting {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    Localization.Lifting
      (stageLocalization l X E)
      (integralTensorW l X E)
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h ⋙
        integralTensor l X C L)
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙
        rationalTensor l X C L) :=
  ⟨rationalTensorTransitionLift l X C h⟩

/-- The localized comparison is uniquely fixed by the explicit integral tensor map.
Source: BS 6.8.14(2) (blueprint: lem-sf-native-rational-tensor-cocone). -/
def rationalTensorTransition {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    rationalTensor l X C E ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙
        rationalTensor l X C L :=
  Localization.liftNatIso
    (stageLocalization l X E)
    (integralTensorW l X E) _ _ _ _ (asIso (integralTensorComparison l X C h))

/-- The integral components of the localized comparison are the prescribed ones.
Source: Stacks Tag 05R6 (blueprint: lem-sf-native-rational-tensor-cocone). -/
theorem rationalTensorTransition_hom_app {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (rationalTensorTransition l X C h).hom.app
        ((stageLocalization l X E).obj K) =
      (rationalTensorIntegral l X C E).hom.app K ≫
        (integralTensorComparison l X C h).app K ≫
        (rationalTensorIntegral l X C L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition
            l (PadicAlgCl l) X E L h).obj K) ≫
        (rationalTensor l X C L).map ((rationalIntegralTransition l X h).inv.app K) := by
  simp only [rationalTensorTransition, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, rationalTensorTransition_lifting,
    rationalTensor_lifting, Localization.Lifting.iso,
    rationalTensorTransitionLift, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, asIso_hom, Iso.symm_inv,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]

instance rationalTensorTransition_shift {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    NatTrans.CommShift (rationalTensorTransition l X C h).hom ℤ := by
  haveI := (integralTensorComparison_coherent l X C).1 h
  let Q := stageLocalization l X E
  have he : Functor.whiskerLeft Q (rationalTensorTransition l X C h).hom =
      (rationalTensorIntegral l X C E).hom ≫ integralTensorComparison l X C h ≫
        (rationalTensorTransitionLift l X C h).inv := by
    ext K
    dsimp only [Q]
    simp only [Functor.whiskerLeft_app, rationalTensorTransition_hom_app,
      NatTrans.comp_app, rationalTensorTransitionLift, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_inv,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
  haveI : NatTrans.CommShift (Functor.whiskerLeft Q
      (rationalTensorTransition l X C h).hom) ℤ := by
    rw [he]
    infer_instance
  exact commShift_of_localization Q (integralTensorW l X E) _

/-- The localized comparisons obey the field-tower equation.
Source: BS 6.8.14(2), Remark 6.8.15
(blueprint: lem-sf-native-rational-tensor-cocone). -/
theorem rationalTensorTransition_tower {E L M : Index l (PadicAlgCl l)}
    (h : E ≤ L) (k : L ≤ M)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E) :
    (rationalTensorTransition l X C h).hom.app K ≫
      (rationalTensorTransition l X C k).hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj K) ≫
      (rationalTensor l X C M).map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem
          l (PadicAlgCl l) X).assoc h k).hom.app K) =
    (rationalTensorTransition l X C (h.trans k)).hom.app K := by
  cases K with
  | mk K =>
    let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X
    let q := rationalIntegralTransition l X h
    let q' := rationalIntegralTransition l X k
    let q'' := rationalIntegralTransition l X (h.trans k)
    let T := GeneralAlgebraicallyClosedCoefficients.integralTransition
      l (PadicAlgCl l) X E L h
    let Q := stageLocalization l X E
    let Q' := stageLocalization l X M
    have hq : q'.inv.app (T.obj K) ≫ (S.T k).map (q.inv.app K) ≫
        (S.assoc h k).hom.app (Q.obj K) =
      Q'.map ((integralTensorAssociator l X (PadicAlgCl l) h k).hom.app K) ≫ q''.inv.app K := by
      apply (cancel_epi ((S.T k).map (q.hom.app K) ≫ q'.hom.app (T.obj K))).mp
      apply (cancel_mono (q''.hom.app K)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
        ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
        Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
      dsimp only [S, q, q', q'', T, Q, Q']
      simpa only [Functor.comp_obj, Category.assoc, Category.comp_id] using
        (rationalIntegralTransition_tower l X h k K).symm
    change (rationalTensorTransition l X C h).hom.app (Q.obj K) ≫
      (rationalTensorTransition l X C k).hom.app ((S.T h).obj (Q.obj K)) ≫
      (rationalTensor l X C M).map ((S.assoc h k).hom.app (Q.obj K)) =
        (rationalTensorTransition l X C (h.trans k)).hom.app (Q.obj K)
    dsimp only [Q, S]
    simp only [rationalTensorTransition_hom_app l X C h K,
      rationalTensorTransition_hom_app l X C (h.trans k) K]
    simp only [Category.assoc]
    have hn := (rationalTensorTransition l X C k).hom.naturality
      ((rationalIntegralTransition l X h).inv.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at hn
    simp only [reassoc_of% hn]
    simp only [rationalTensorTransition_hom_app l X C k]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.comp_map, Functor.comp_obj]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
    dsimp only [S, q, q', q'', T, Q, Q'] at hq
    simp only [hq, Functor.map_comp]
    have hf := (rationalTensorIntegral l X C M).inv.naturality
      ((integralTensorAssociator l X (PadicAlgCl l) h k).hom.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at hf
    simp only [← (reassoc_of% hf)]
    simp only [reassoc_of% ((integralTensorComparison_coherent l X C).2 h k K)]

/-- The inverse comparisons have the contravariant cocone orientation.
Source: BS 6.8.14(2) (blueprint: lem-sf-native-rational-tensor-cocone). -/
theorem rationalTensorTransition_inv_tower {E L M : Index l (PadicAlgCl l)}
    (h : E ≤ L) (k : L ≤ M)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E) :
    (rationalTensor l X C M).map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem
          l (PadicAlgCl l) X).assoc h k).hom.app K) ≫
      (rationalTensorTransition l X C (h.trans k)).inv.app K =
    (rationalTensorTransition l X C k).inv.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj K) ≫
      (rationalTensorTransition l X C h).inv.app K := by
  apply (cancel_epi ((rationalTensorTransition l X C h).hom.app K ≫
    (rationalTensorTransition l X C k).hom.app
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj K))).mp
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, Category.comp_id] using
    congrArg (fun f ↦ f ≫ (rationalTensorTransition l X C (h.trans k)).inv.app K)
      (rationalTensorTransition_tower l X C h k K)

private theorem equivalence_counit_conjugate
    {A B : Type*} [Category A] [Category B] (e : A ≌ B)
    {P Q : B} (f : P ⟶ Q) :
    e.functor.map (e.inverse.map f) =
      e.counitIso.hom.app P ≫ f ≫ e.counitIso.inv.app Q := by
  apply (cancel_mono (e.counitIso.hom.app Q)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj,
    Category.comp_id] using e.counitIso.hom.naturality f

private theorem equivalence_counit_transport
    {A B : Type*} [Category A] [Category B] (e : A ≌ B)
    {P Q R : B} (f : P ⟶ Q) (h : Q = R) :
    HEq (e.functor.map (e.inverse.map (f ≫ eqToHom h)))
      (e.counitIso.hom.app P ≫ f ≫ e.counitIso.inv.app Q) := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]
  exact heq_of_eq (equivalence_counit_conjugate e f)

/-- The lifted component equation after an arbitrary equivalence, with the literal
scalar object transport removed heterogeneously.
Source: BS 6.8.14(2) (blueprint: lem-sf-native-rational-tensor-cocone).
Proof: expand the localization component, express its final scalar transport as
an equality morphism, and use the equivalence counit naturality. Equality induction
removes that last transport, retaining the integral endpoint on the right. -/
theorem rationalTensorTransition_native_normalization
    {N : Type*} [Category N]
    (e : N ≌ DerivedCategory (pbcModules X (ringSheaf l X)))
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    HEq (e.functor.map (e.inverse.map ((rationalTensorTransition l X C h).hom.app
      ((stageLocalization l X E).obj K))))
      (e.counitIso.hom.app ((rationalTensor l X C E).obj
          ((stageLocalization l X E).obj K)) ≫
        (rationalTensorIntegral l X C E).hom.app K ≫
        (integralTensorComparison l X C h).app K ≫
        (rationalTensorIntegral l X C L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition
            l (PadicAlgCl l) X E L h).obj K) ≫
        e.counitIso.inv.app ((rationalTensor l X C L).obj
          ((stageLocalization l X L).obj
            ((GeneralAlgebraicallyClosedCoefficients.integralTransition
              l (PadicAlgCl l) X E L h).obj K)))) := by
  rw [rationalTensorTransition_hom_app l X C h K,
    rationalIntegralTransition_inv, eqToHom_map]
  simpa only [Functor.comp_obj, Category.assoc] using equivalence_counit_transport e
    ((rationalTensorIntegral l X C E).hom.app K ≫
      (integralTensorComparison l X C h).app K ≫
      (rationalTensorIntegral l X C L).inv.app
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition
          l (PadicAlgCl l) X E L h).obj K)) _

end WeilConjectures.LocallyFiniteAdicRealization
