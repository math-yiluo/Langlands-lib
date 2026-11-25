/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftStrictTowerLeftSquare
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftStrictTowerRightSquare

/-! # Strict tensor towers and signed reindexing -/

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

attribute [local irreducible] integralOperationsTensorTowerFunctor integralOperationsRoos
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsTensorComplexFunctor integralOperationsGoodLocalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Reindexing commutes with the two signed tensor shifts on entire strict towers.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G and 07A4
(blueprint: lem-pod-tensor-shift-strict-tower-squares-c3).

Proof: evaluate each natural transformation at a quotient n, each cochain degree,
and each pro-etale object. Direct-sum extensionality reduces equality to a homogeneous
pure tensor of bidegree (p,q). For the first slot, both composites relabel its factors
without a sign. For the second slot, both multiply the relabelled tensor by (-1)^(pr).
The quotient comparison is fixed on generators by D.QuotientGenerators; its shifted
version has the same component in each relabelled degree. T.Generators and the two
shift generator laws therefore give equality on all pure tensors. Sheafified tensor
extensionality, followed by direct-sum, complex and natural-transformation
extensionality, gives equality of the entire tower maps, including transitions.
This works for zero and negative shifts and for zero complexes and empty sites. -/
theorem podTensorShift_strictTowerSquares
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D) (hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X)
    (hSY : SY.Generators l E) (hSX : SX.Generators l E)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (r : ℤ) :
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
    L₁ = L₂ ∧ R₁ = R₂ := by
  exact ⟨podTensorShift_strictTowerLeftSquare l E g D hD T hT SY SX hSY hSX P Q r,
    podTensorShift_strictTowerRightSquare l E g D hD T hT SY SX hSY hSX P Q r⟩

end WeilConjectures
