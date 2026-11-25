/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitStrictWitness
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitRepresentativeTransport
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import Mathlib.CategoryTheory.Localization.Prod

/-! # Representative and limit transport

The scalar/tensor comparison is transported in two separate stages.  The first
stage is the strict calculation on K-flat good representatives.  The second
stage is the localization, completion, and total-limit argument.  Keeping the
representative equality as an explicit hypothesis makes the latter a genuine
transport statement rather than a restatement of DerivedSigmaModel.
(blueprint: stage3-pur-scalar-tensor-limit-strict-equation-assembly)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible]
  integralCompletedTensor scalarReduction tensorReduction
  integralComparisonDerivedSequenceScalar

private theorem transport_natural_eq
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (q : A ⥤ B) [q.EssSurj] {F G : B ⥤ C}
    (a b : F ⟶ G) (h : ∀ P : A, a.app (q.obj P) = b.app (q.obj P))
    (X : B) : a.app X = b.app X := by
  let e := q.objObjPreimageIso X
  apply (cancel_epi (F.map e.hom)).1
  rw [a.naturality, b.naturality, h]

/--
Localization, completion, and total-limit functoriality assemble the square
from the prescribed ordinary-source equation on K-flat good representatives.
Both ordinary-source word maps are natural. Essential surjectivity extends their
equality to every input, and invertibility of source completion on the complete
tensor gives the specified completed comparison. The cochain-level predicate
DerivedSigmaModel is not used by this transport step.
Source: Stacks 07A4 and 0941 (blueprint:
stage3-pur-scalar-tensor-limit-strict-equation-assembly).
-/
theorem scalarTowerTensorLimitSquare_of_representativeTransport
    (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (_hl : IsUnit (l : Γ(W, ⊤)))
    (M N : sfIntegralConstructibleCategory l E W)
    (hT : IsSfDerivedComplete l E W
      ((integralCompletedTensor.{u, u} l E W).obj (M.obj, N.obj)))
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (hRep : ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
      (scalarTensorOrdinary l E L ι W).hom.app
          ((integralOperationsGoodLocalization l E W).obj P,
            (integralOperationsGoodLocalization l E W).obj Q) ≫
        (integralCompletedTensor l L W).map (Prod.mkHom
          ((scalarCompletion l E L ι W).app
            ((integralOperationsGoodLocalization l E W).obj P))
          ((scalarCompletion l E L ι W).app
            ((integralOperationsGoodLocalization l E W).obj Q))) ≫
        TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj P),
            (integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj P))
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj Q)))) =
      (scalarCompletion l E L ι W).app
          ((integralCompletedTensor l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ≫
        SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
            (tensorReduction l E W SE ρE TE
              ((integralOperationsGoodLocalization l E W).obj P)
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
          α.hom.app
            (SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj P),
              SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj Q)))) :
    (scalarTensorCompleted l E L ι W M.obj N.obj M.property.1 N.property.1 hT).hom ≫
        TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι W).obj M.obj,
            (integralScalarExtension.{u} l E L ι W).obj N.obj) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY M.obj)
            (scalarReduction l E L ι W SE SL ρL SY N.obj))) =
      SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E W).obj (M.obj, N.obj)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
            (tensorReduction l E W SE ρE TE M.obj N.obj) ≫
          α.hom.app (SE.reduction.obj M.obj, SE.reduction.obj N.obj)) := by
  let q := integralOperationsGoodLocalization l E W
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E W
  let : (q.prod q).EssSurj := Localization.essSurj (q.prod q) (V.prod V)
  let δ : integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ⟶
      SE.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι W :=
    Functor.whiskerRight SY.realization.hom SL.reduction ≫
      Functor.whiskerLeft (SE.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι W)
        SL.adjunction.counit
  let τ : integralCompletedTensor l E W ⋙ SE.reduction ⟶
      SE.reduction.prod SE.reduction ⋙ SE.systemClosed.tensor :=
    Functor.whiskerRight TE.realization.hom SE.reduction ≫
      Functor.whiskerLeft (SE.reduction.prod SE.reduction ⋙ SE.systemClosed.tensor)
        SE.adjunction.counit
  let a := Functor.whiskerLeft (integralCompletedTensor l E W) SY.realization.hom ≫
    Functor.whiskerRight
      (Functor.whiskerRight τ (integralComparisonDerivedSequenceScalar l E L ι W) ≫
        Functor.whiskerLeft (SE.reduction.prod SE.reduction) α.hom)
      (coefficientSequenceLimit l L W)
  let b := Functor.whiskerLeft
      ((integralScalarExtensionOfUniverses l E L ι W).prod
        (integralScalarExtensionOfUniverses l E L ι W)) TL.realization.hom ≫
    Functor.whiskerRight
      (Functor.whiskerRight (NatTrans.prod δ δ) SL.systemClosed.tensor)
      (coefficientSequenceLimit l L W)
  let χ := scalarCompletion l E L ι W
  let c := (scalarTensorOrdinary l E L ι W).hom ≫
    Functor.whiskerRight (NatTrans.prod χ χ) (integralCompletedTensor l L W)
  have h := transport_natural_eq (q.prod q) (c ≫ b)
      (Functor.whiskerLeft (integralCompletedTensor l E W) χ ≫ a) (by
    intro P
    simpa only [a, b, c, χ, δ, τ, q, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.prod, Functor.prod_obj, Functor.comp_obj,
      scalarReduction, tensorReduction, integralScalarExtension,
      integralScalarExtensionOfUniverses, Category.assoc] using hRep P.1 P.2) (M.obj, N.obj)
  let : IsIso (χ.app ((integralCompletedTensor l E W).obj (M.obj, N.obj))) :=
    (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.2 _ hT
  apply (cancel_epi (χ.app ((integralCompletedTensor l E W).obj (M.obj, N.obj)))).1
  rw [← Category.assoc, scalarTensorCompleted_unitEquation]
  simpa only [a, b, c, χ, δ, τ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.prod, Functor.prod_obj, Functor.comp_obj,
    scalarReduction, tensorReduction, integralScalarExtension,
    integralScalarExtensionOfUniverses, Category.assoc] using h

end WeilConjectures.ScalarExtensionTower
