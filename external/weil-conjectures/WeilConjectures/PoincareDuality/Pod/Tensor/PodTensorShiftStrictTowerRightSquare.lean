/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelReduction
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftStrictTowerRightGenerator

/-! # Right strict tensor-shift square -/

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

attribute [local irreducible] integralOperationsRoos
attribute [local implicit_reducible] integralOperationsTensorTowerFunctor
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsTensorComplexFunctor integralOperationsGoodLocalization

attribute [local implicit_reducible] integralOperationsTensorLevel
  integralOperationsTensorComposite SheafOfModules.restrictScalars podGoodReindex
  podShiftTower Functor.ofOpSequence Functor.ofSequence
attribute [local implicit_reducible] Functor.map₂HomologicalComplex
attribute [local implicit_reducible] isoSectionwiseModuleInverseImage
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

-- Keep the original tower interface while reducing to the generator calculation.
/-- The right tensor-shift square commutes on the entire strict quotient tower.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G and 07A4
(blueprint: lem-pod-tensor-shift-strict-tower-right-square-t6).

Precompose with the inverse normalized tensor comparison and evaluate at a quotient
and a degree. Finite tensor extensionality tests unit reduction generators. The
quotient normalization computes their images, then the inverse tensor normalization,
the signed shift laws, and the forward tensor normalization compute the left path.
The finite tensor map law and the identity components of termwise reindexing with
shift compute the right path. Integer degree transport identifies the outputs.
For the right slot, additivity transports the common Koszul sign (-1)^(pr).
These identities apply for every integer shift, including zero and negative shifts. -/
theorem podTensorShift_strictTowerRightSquare
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
    let QYr := (⟨Q.obj⟦r⟧, SY.good Q r⟩ :
      (integralOperationsGoodComplex l E Y).FullSubcategory)
    let R₁ := (podReindexTower l E g).map (SY.rightTower P Q r).hom ≫
      (podTowerShift l E g (TY.obj (P.obj, Q.obj)) r).hom ≫
      whiskerRight (T.tower P Q).hom (shiftFunctor _ r)
    let R₂ := (T.tower P QYr).hom ≫
      TX.map (Prod.mkHom (𝟙 PX.obj)
        (((isoReductionIntegralComplex l E g).commShiftIso r).hom.app Q.obj)) ≫
      (SX.rightTower PX QX r).hom
    R₁ = R₂ := by
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  dsimp only
  apply (cancel_epi (T.tower P ⟨Q.obj⟦r⟧, SY.good Q r⟩).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro k
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f]
  apply finite_tensor_ext l E X n.unop
    ((isoReductionIntegralComplex l E g).obj P.obj)
    ((isoReductionIntegralComplex l E g).obj (Q.obj⟦r⟧)) k _ _ _
  intro p q hpq U x y
  subst k
  simp only [eqToHom_refl, SheafOfModules.id_val, PresheafOfModules.id_app]
  exact podTensorShift_strictTowerRightGenerator l E g D hD T hT SY SX hSY hSX P Q r n p q U x y

end WeilConjectures
