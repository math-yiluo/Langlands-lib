/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts

import WeilConjectures.PoincareDuality.PodTensorShiftNormalization.PodTensorShiftPathAssembly

/-! # The left source tensor-shift path formula -/

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

-- Keep sharing in the dependent coefficient-category expressions.
/-- The left-slot source path formula, proved from its model law.
Use the arbitrary-presentation path calculation.
Source: blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: lem-pod-tensor-shift-left-paths-t5). -/
theorem podTensorShift_leftSourcePath
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D) (hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X)
    (mSY : SY.Model l E D.shiftSource) (_mSX : SX.Model l E D.shiftTarget)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
    (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧)
    (eP : DerivedCategory.Q.obj P.obj ≅ M.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj)
    (eP' : DerivedCategory.Q.obj (P.obj⟦r⟧) ≅ M'.obj)
    (eQ' : DerivedCategory.Q.obj (Q.obj⟦r⟧) ≅ N'.obj)
    (ha : eP'.hom ≫ a.hom = (DerivedCategory.Q.commShiftIso r).hom.app P.obj ≫ eP.hom⟦r⟧')
    (hb : eQ'.hom ≫ b.hom = (DerivedCategory.Q.commShiftIso r).hom.app Q.obj ≫ eQ.hom⟦r⟧') :
    letI : (isoReductionIntegralInverse l E g).Additive :=
      isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
    let PX := (podGoodReindex l E g D).obj P
    let QX := (podGoodReindex l E g D).obj Q
    let TY := integralOperationsTensorTowerFunctor l E Y
    let TX := integralOperationsTensorTowerFunctor l E X
    let PYr := (⟨P.obj⟦r⟧, SY.good P r⟩ :
      (integralOperationsGoodComplex l E Y).FullSubcategory)
    let L₁ := (podReindexTower l E g).map (SY.leftTower P Q r).hom ≫
      (podTowerShift l E g (TY.obj (P.obj, Q.obj)) r).hom ≫
      whiskerRight (T.tower P Q).hom (shiftFunctor _ r)
    let F := podOrdinaryReindex l E g
    let V := integralCompletedTensor l E Y
    let W := integralCompletedTensor l E X
    let cY := integralCompletedTensorComparison l E Y
    let cX := integralCompletedTensorComparison l E X
    let φ := (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors
    let startL := F.map (cY.hom.app (PYr, Q)) ≫ φ.hom.app _ ≫
      DerivedCategory.Q.map (D.roos (TY.obj (P.obj⟦r⟧, Q.obj))).hom
    let finish :=
      DerivedCategory.Q.map (D.shiftTarget.comparison (TX.obj (PX.obj, QX.obj)) r).hom ≫
      ((DerivedCategory.Q (C := scalarReductionSource l E X)).commShiftIso r).hom.app
        (integralOperationsRoos (TX.obj (PX.obj, QX.obj))) ≫ cX.inv.app (PX, QX)⟦r⟧' ≫
      (W.map (Prod.mkHom (φ.inv.app P.obj ≫ F.map eP.hom)
        (φ.inv.app Q.obj ≫ F.map eQ.hom)))⟦r⟧'
    (F.map (V.map (Prod.mkHom eP'.hom eQ.hom)) ≫
        F.map (SY.left M N M' r a).hom ≫
        (F.commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
      startL ≫ DerivedCategory.Q.map (integralOperationsRoosMap L₁) ≫ finish) := by
  intro PX QX TY TX PYr L₁ F V W cY cX φ startL finish
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at *
  have hsY := mSY P Q r M N M' N' eP eQ eP' eQ' a b ha hb
  have h := source_path l E g D hD T hT P Q M N eP eQ r _
    (SY.leftTower P Q r).hom _ _ (cY.app (PYr, Q)) _ _ hsY.1
  exact h

end WeilConjectures
