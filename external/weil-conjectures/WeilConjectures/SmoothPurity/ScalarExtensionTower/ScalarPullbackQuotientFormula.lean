/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData

/-! # Tensor-unit formula for scalar/pullback quotient coordinates

Source: Stacks 06YY, 07A4 and 0941
(blueprint: stage3-pur-scalar-pullback-roos-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The fixed tensor-unit equation for a strict scalar/pullback quotient comparison.
Source: Stacks 06YY, 07A4 (blueprint: stage3-pur-scalar-pullback-roos-coordinates). -/
def ScalarPullbackQuotientFormula
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (P.obj.X i).val.obj (op U)),
    ((q.hom.app (op n)).f i).val.app (op ((Scheme.proEtaleBaseChange f).obj U))
      (integralComparisonRestrictedSection.{u, u} l L X
        ((integralComparisonSequencePullback.{u, u} l L f).obj
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj (C.X i))) n
        (op ((Scheme.proEtaleBaseChange f).obj U))
        (integralComparisonSequenceGenerator.{u, u} l L f
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj (C.X i)) n U
          (integralComparisonSequenceTensorSection.{u, u} l E L ι Y (C.X i)
            (op (n, U)) 1
            (integralComparisonSequenceSection.{u, u} l E Y (C.X i) n (op U)
              (((κ n).inv.f i).val.app (op U)
                (unrestrictedIntegralTensorSection.{u, u} l E Y n (P.obj.X i)
                  (op U) 1 x)))))) =
      integralOperationsPullbackGenerator.{u, u} l L f n
        (((unrestrictedIntegralFiniteComplex.{u, u} l L Y n).obj
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)).X i)
        U (unrestrictedIntegralTensorSection.{u, u} l L Y n
          ((integralOrdinaryScalar l E L ι Y).obj (P.obj.X i)) (op U) 1
          (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) (op U) 1 x))

end WeilConjectures.ScalarExtensionTower
