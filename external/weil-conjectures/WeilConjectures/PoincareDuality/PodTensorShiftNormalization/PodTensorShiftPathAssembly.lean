/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts

import WeilConjectures.PoincareDuality.PodTensorShiftNormalization.PodTensorShiftPresentedModel
import WeilConjectures.PoincareDuality.PodTensorShiftNormalization.PodTensorShiftRoosTransport

/-! # Proved calculations for tensor-shift path normalization

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-path-assembly-t5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodTensorShiftNormalization

attribute [local irreducible] integralOperationsTensorTowerFunctor
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsTensorComplexFunctor integralOperationsGoodLocalization podOrdinaryReindex
  podGoodReindex integralOperationsRoosFunctor podShiftTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem shifted_model
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {A B K : C} {Z : D}
    (c : A ≅ B) (v : A ⟶ K) (t : F.obj K ⟶ Z) (z : F.obj B ⟶ Z)
    (r : ℤ) (h : F.map v ≫ t = F.map c.hom ≫ z) :
    F.map (c.inv⟦r⟧') ≫ F.map (v⟦r⟧') ≫
        (F.commShiftIso r).hom.app K ≫ t⟦r⟧' =
      (F.commShiftIso r).hom.app B ≫ z⟦r⟧' := by
  have hb := (F.mapIso c).inv_comp_eq.mpr h
  rw [F.commShiftIso_hom_naturality_assoc, F.commShiftIso_hom_naturality_assoc]
  simpa only [Functor.map_comp, Functor.mapIso_inv, Category.assoc] using
    congrArg (fun f ↦ (F.commShiftIso r).hom.app B ≫ f⟦r⟧') hb

section Presentations
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

attribute [local irreducible] integralOperationsRoos

variable [(isoReductionIntegralInverse l E g).Additive]
  [PreservesFiniteLimits (isoReductionIntegralInverse l E g)]
  [PreservesFiniteColimits (isoReductionIntegralInverse l E g)]

-- Share the normalized categorical expressions without unfolding coefficient constructions.
/-- Normalize the source-shift path from its model formula.
Move the presentation past the ordinary shift comparison, substitute the presented tensor
model, and apply the Roos transport calculation.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-path-assembly-t5). -/
theorem source_path
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (M N : sfIntegralConstructibleCategory l E Y)
    (eP : DerivedCategory.Q.obj P.obj ≅ M.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj)
    (r : ℤ) (C' : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ)
    (s : C' ⟶ podShiftTower
      ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj)) r)
    (A B : DerivedCategory (scalarReductionSource l E Y))
    (c : A ≅ DerivedCategory.Q.obj (integralOperationsRoos C'))
    (v : A ⟶ B)
    (sy : B ⟶ ((integralCompletedTensor l E Y).obj (M.obj, N.obj))⟦r⟧)
    (hsy : v ≫ sy = c.hom ≫ DerivedCategory.Q.map (integralOperationsRoosMap s) ≫
      DerivedCategory.Q.map (D.shiftSource.comparison
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj)) r).hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app _ ≫
      (integralCompletedTensorComparison l E Y).inv.app (P, Q)⟦r⟧' ≫
      ((integralCompletedTensor l E Y).map (Prod.mkHom eP.hom eQ.hom))⟦r⟧') :
    let F := podOrdinaryReindex l E g
    let φ := (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors
    let PX := (podGoodReindex l E g D).obj P
    let QX := (podGoodReindex l E g D).obj Q
    F.map v ≫ F.map sy ≫ (F.commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
      (F.map c.hom ≫ φ.hom.app _ ≫ DerivedCategory.Q.map (D.roos C').hom) ≫
      DerivedCategory.Q.map (integralOperationsRoosMap
        ((podReindexTower l E g).map s ≫
          (podTowerShift l E g
            ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj)) r).hom ≫
          whiskerRight (T.tower P Q).hom (shiftFunctor _ r))) ≫
      (DerivedCategory.Q.map (D.shiftTarget.comparison
        ((integralOperationsTensorTowerFunctor l E X).obj (PX.obj, QX.obj)) r).hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app _ ≫
      (integralCompletedTensorComparison l E X).inv.app (PX, QX)⟦r⟧' ≫
      ((integralCompletedTensor l E X).map
        (Prod.mkHom (φ.inv.app P.obj ≫ F.map eP.hom)
          (φ.inv.app Q.obj ≫ F.map eQ.hom)))⟦r⟧') := by
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at *
  let F := (isoReductionIntegralInverse l E g).mapDerivedCategory
  let φ := (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors
  have hm := tensor_model_presented l E g D T hT P Q M N eP eQ
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at hm
  have htail := shifted_model F ((integralCompletedTensorComparison l E Y).app (P, Q))
    ((integralCompletedTensor l E Y).map (Prod.mkHom eP.hom eQ.hom))
    (T.tensor M N).hom _ r hm
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj, F, φ] at htail
  simp only [Iso.app_inv, Functor.map_comp] at htail
  have h₁ := congrArg (fun z ↦ F.map z ≫
    (F.commShiftIso r).hom.app ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
      (T.tensor M N).hom⟦r⟧') hsy
  have h₂ := congrArg (fun z ↦ F.map c.hom ≫
    F.map (DerivedCategory.Q.map (integralOperationsRoosMap s)) ≫
    F.map (DerivedCategory.Q.map (D.shiftSource.comparison
      ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj)) r).hom) ≫
    F.map ((DerivedCategory.Q.commShiftIso r).hom.app
      (integralOperationsRoos
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj)))) ≫ z) htail
  have hp := roos_path_shift l E g D hD r s (T.tower P Q).hom
  have h₃ := congrArg (fun f ↦ F.map c.hom ≫ f ≫
    ((integralCompletedTensorComparison l E X).inv.app
      ((podGoodReindex l E g D).obj P, (podGoodReindex l E g D).obj Q))⟦r⟧' ≫
    ((integralCompletedTensor l E X).map (Prod.mkHom
      (φ.inv.app P.obj ≫ F.map eP.hom) (φ.inv.app Q.obj ≫ F.map eQ.hom)))⟦r⟧') hp
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj, F, φ] at h₁ h₂ h₃
  simp only [Functor.map_comp, Category.assoc] at h₁ h₂ h₃
  simpa only [Category.assoc] using h₁.trans (h₂.trans h₃)

end Presentations
end WeilConjectures.PodTensorShiftNormalization
