/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts

import WeilConjectures.PoincareDuality.PodTensorShiftNormalization.PodTensorShiftNaturality
import WeilConjectures.PoincareDuality.PodTensorShiftNormalization.PodTensorShiftTargetPathAssembly

/-! # The right target tensor-shift path formula -/

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
namespace WeilConjectures

attribute [local irreducible] integralOperationsTensorTowerFunctor
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsTensorComplexFunctor integralOperationsGoodLocalization podOrdinaryReindex
  podGoodReindex integralOperationsRoosFunctor podShiftTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open PodTensorShiftNormalization

attribute [local irreducible] integralOperationsRoos

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [(isoReductionIntegralInverse l E g).Additive]
  [PreservesFiniteLimits (isoReductionIntegralInverse l E g)]
  [PreservesFiniteColimits (isoReductionIntegralInverse l E g)]

-- Keep sharing in the dependent coefficient-category expressions.
/-- The right-slot target path formula, proved from its model law.
Use the arbitrary-presentation path calculation and shift-presentation naturality.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: lem-pod-tensor-shift-right-target-path-t5). -/
theorem podTensorShift_rightTargetPath
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D) (hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X)
    (_mSY : SY.Model l E D.shiftSource) (mSX : SX.Model l E D.shiftTarget)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
    (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧)
    (eP : DerivedCategory.Q.obj P.obj ≅ M.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj)
    (eP' : DerivedCategory.Q.obj (P.obj⟦r⟧) ≅ M'.obj)
    (eQ' : DerivedCategory.Q.obj (Q.obj⟦r⟧) ≅ N'.obj)
    (_ha : eP'.hom ≫ a.hom = (DerivedCategory.Q.commShiftIso r).hom.app P.obj ≫ eP.hom⟦r⟧')
    (hb : eQ'.hom ≫ b.hom = (DerivedCategory.Q.commShiftIso r).hom.app Q.obj ≫ eQ.hom⟦r⟧') :
    let PX := (podGoodReindex l E g D).obj P
    let QX := (podGoodReindex l E g D).obj Q
    let TY := integralOperationsTensorTowerFunctor l E Y
    let TX := integralOperationsTensorTowerFunctor l E X
    let QYr := (⟨Q.obj⟦r⟧, SY.good Q r⟩ :
      (integralOperationsGoodComplex l E Y).FullSubcategory)
    let R₂ := (T.tower P QYr).hom ≫
      TX.map (Prod.mkHom (𝟙 PX.obj)
        (((isoReductionIntegralComplex l E g).commShiftIso r).hom.app Q.obj)) ≫
      (SX.rightTower PX QX r).hom
    let F := podOrdinaryReindex l E g
    let V := integralCompletedTensor l E Y
    let W := integralCompletedTensor l E X
    let cY := integralCompletedTensorComparison l E Y
    let cX := integralCompletedTensorComparison l E X
    let φ := (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors
    let startR := F.map (cY.hom.app (P, QYr)) ≫ φ.hom.app _ ≫
      DerivedCategory.Q.map (D.roos (TY.obj (P.obj, Q.obj⟦r⟧))).hom
    let finish :=
      DerivedCategory.Q.map (D.shiftTarget.comparison (TX.obj (PX.obj, QX.obj)) r).hom ≫
      ((DerivedCategory.Q (C := scalarReductionSource l E X)).commShiftIso r).hom.app
        (integralOperationsRoos (TX.obj (PX.obj, QX.obj))) ≫ cX.inv.app (PX, QX)⟦r⟧' ≫
      (W.map (Prod.mkHom (φ.inv.app P.obj ≫ F.map eP.hom)
        (φ.inv.app Q.obj ≫ F.map eQ.hom)))⟦r⟧'
    (F.map (V.map (Prod.mkHom eP.hom eQ'.hom)) ≫ (T.tensor M N').hom ≫
        (SX.right ⟨_, T.constructible M⟩ ⟨_, T.constructible N⟩
          ⟨_, T.constructible N'⟩ r
          (F.mapIso b ≪≫ (F.commShiftIso r).app N.obj)).hom =
      startR ≫ DerivedCategory.Q.map (integralOperationsRoosMap R₂) ≫ finish)  := by
  intro PX QX TY TX QYr R₂ F V W cY cX φ startR finish
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at *
  let ePX := φ.symm.app P.obj ≪≫ F.mapIso eP
  let eQX := φ.symm.app Q.obj ≪≫ F.mapIso eQ
  let aX := F.mapIso a ≪≫ (F.commShiftIso r).app M.obj
  let bX := F.mapIso b ≪≫ (F.commShiftIso r).app N.obj
  let ePX' := (DerivedCategory.Q.commShiftIso r).app PX.obj ≪≫
    (shiftFunctor _ r).mapIso ePX ≪≫ aX.symm
  let eQX' := (DerivedCategory.Q.commShiftIso r).app QX.obj ≪≫
    (shiftFunctor _ r).mapIso eQX ≪≫ bX.symm
  have haX : ePX'.hom ≫ aX.hom =
      (DerivedCategory.Q.commShiftIso r).hom.app PX.obj ≫ ePX.hom⟦r⟧' := by
    simp only [ePX', Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.app_hom, Functor.mapIso_hom]
  have hbX : eQX'.hom ≫ bX.hom =
      (DerivedCategory.Q.commShiftIso r).hom.app QX.obj ≫ eQX.hom⟦r⟧' := by
    simp only [eQX', Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.app_hom, Functor.mapIso_hom]
  have hsX := mSX PX QX r ⟨_, T.constructible M⟩ ⟨_, T.constructible N⟩
    ⟨_, T.constructible M'⟩ ⟨_, T.constructible N'⟩ ePX eQX ePX' eQX' aX bX haX hbX
  have hq := reindexed_shift_presentation DerivedCategory.Q DerivedCategory.Q
    (isoReductionIntegralComplex l E g)
    (isoReductionIntegralInverse l E g).mapDerivedCategory
    (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors Q.obj r eQ eQ' b hb
  have h := target_path l E g D T hT P QYr M N' eP eQ'
    PX ⟨QX.obj⟦r⟧, SX.good QX r⟩ (𝟙 PX)
    ⟨((isoReductionIntegralComplex l E g).commShiftIso r).hom.app Q.obj⟩
    ePX.hom eQX'.hom
    (by
      change φ.inv.app P.obj ≫ F.map eP.hom =
        DerivedCategory.Q.map (𝟙 PX.obj) ≫ ePX.hom
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      rfl) hq
    _ (SX.right ⟨_, T.constructible M⟩ ⟨_, T.constructible N⟩
      ⟨_, T.constructible N'⟩ r bX).hom _ (SX.rightTower PX QX r).hom finish hsX.2
  exact h

end WeilConjectures
