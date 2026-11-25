/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts

import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftLeftPaths
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftRightPaths
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftLeftTargetPath
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftRightTargetPath

/-! # Normalizing the two derived tensor-shift paths -/

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

attribute [local irreducible] integralOperationsRoos

-- Keep sharing in the four dependent path formulas; the wall-clock limit is unchanged.
/-- The two derived paths have separate formulas in terms of strict tower maps.
No equality between the two strict paths is assumed or asserted here.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4 and 0941
(blueprint: lem-pod-tensor-shift-roos-path-normalization-c3).

Proof: substitute SY.Model into the source-shift path and SX.Model into the
target-shift path. Substitute T.Model on the base and shifted good pairs, using
T.Naturality to move the three derived presentation isomorphisms. In the target
model present the reindexed inputs using the inverse of mapDerivedCategoryFactors
followed by ordinary reindexing of eP and eQ; present the shifted inputs by the
canonical shift comparison and the specified a or b. Naturality and compatibility
of mapDerivedCategoryFactors with shifts identify these presentations with the
images of eP' and eQ'. D.RoosNaturality moves the source tower shift past D.roos.
D.RoosShift then converts the source signed Roos shift to the target signed shift;
its two cone coordinates retain the prescribed sign. Naturality of Q.commShiftIso
and cancellation of adjacent comparison isomorphisms give the two displayed
normal forms, with the same prefix and suffix. The right slot uses the identical
argument and its given signed tower map. No generator calculation is needed,
and no equality between the two strict tower paths is used. -/
theorem podTensorShift_roosPathNormalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D) (hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X)
    (mSY : SY.Model l E D.shiftSource) (mSX : SX.Model l E D.shiftTarget)
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
    let QYr := (⟨Q.obj⟦r⟧, SY.good Q r⟩ :
      (integralOperationsGoodComplex l E Y).FullSubcategory)
    let L₁ := (podReindexTower l E g).map (SY.leftTower P Q r).hom ≫
      (podTowerShift l E g (TY.obj (P.obj, Q.obj)) r).hom ≫
      whiskerRight (T.tower P Q).hom (shiftFunctor _ r)
    let L₂ := (T.tower PYr Q).hom ≫
      TX.map (Prod.mkHom (((isoReductionIntegralComplex l E g).commShiftIso r).hom.app P.obj)
        (𝟙 QX.obj)) ≫ (SX.leftTower PX QX r).hom
    let R₁ := (podReindexTower l E g).map (SY.rightTower P Q r).hom ≫
      (podTowerShift l E g (TY.obj (P.obj, Q.obj)) r).hom ≫
      whiskerRight (T.tower P Q).hom (shiftFunctor _ r)
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
    let startL := F.map (cY.hom.app (PYr, Q)) ≫ φ.hom.app _ ≫
      DerivedCategory.Q.map (D.roos (TY.obj (P.obj⟦r⟧, Q.obj))).hom
    let startR := F.map (cY.hom.app (P, QYr)) ≫ φ.hom.app _ ≫
      DerivedCategory.Q.map (D.roos (TY.obj (P.obj, Q.obj⟦r⟧))).hom
    let finish :=
      DerivedCategory.Q.map (D.shiftTarget.comparison (TX.obj (PX.obj, QX.obj)) r).hom ≫
      ((DerivedCategory.Q (C := scalarReductionSource l E X)).commShiftIso r).hom.app
        (integralOperationsRoos (TX.obj (PX.obj, QX.obj))) ≫ cX.inv.app (PX, QX)⟦r⟧' ≫
      (W.map (Prod.mkHom (φ.inv.app P.obj ≫ F.map eP.hom)
        (φ.inv.app Q.obj ≫ F.map eQ.hom)))⟦r⟧'
    (F.map (V.map (Prod.mkHom eP'.hom eQ.hom)) ≫
        F.map (SY.left M N M' r a).hom ≫
        (F.commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
      startL ≫ DerivedCategory.Q.map (integralOperationsRoosMap L₁) ≫ finish) ∧
    (F.map (V.map (Prod.mkHom eP'.hom eQ.hom)) ≫ (T.tensor M' N).hom ≫
        (SX.left ⟨_, T.constructible M⟩ ⟨_, T.constructible N⟩
          ⟨_, T.constructible M'⟩ r
          (F.mapIso a ≪≫ (F.commShiftIso r).app M.obj)).hom =
      startL ≫ DerivedCategory.Q.map (integralOperationsRoosMap L₂) ≫ finish) ∧
    (F.map (V.map (Prod.mkHom eP.hom eQ'.hom)) ≫
        F.map (SY.right M N N' r b).hom ≫
        (F.commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
      startR ≫ DerivedCategory.Q.map (integralOperationsRoosMap R₁) ≫ finish) ∧
    (F.map (V.map (Prod.mkHom eP.hom eQ'.hom)) ≫ (T.tensor M N').hom ≫
        (SX.right ⟨_, T.constructible M⟩ ⟨_, T.constructible N⟩
          ⟨_, T.constructible N'⟩ r
          (F.mapIso b ≪≫ (F.commShiftIso r).app N.obj)).hom =
      startR ≫ DerivedCategory.Q.map (integralOperationsRoosMap R₂) ≫ finish)  := by
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact podTensorShift_leftSourcePath l E g D hD T hT SY SX mSY mSX
      P Q M N M' N' r a b eP eQ eP' eQ' ha hb
  · exact podTensorShift_leftTargetPath l E g D hD T hT SY SX mSY mSX
      P Q M N M' N' r a b eP eQ eP' eQ' ha hb
  · exact podTensorShift_rightSourcePath l E g D hD T hT SY SX mSY mSX
      P Q M N M' N' r a b eP eQ eP' eQ' ha hb
  · exact podTensorShift_rightTargetPath l E g D hD T hT SY SX mSY mSX
      P Q M N M' N' r a b eP eQ eP' eQ' ha hb

end WeilConjectures
