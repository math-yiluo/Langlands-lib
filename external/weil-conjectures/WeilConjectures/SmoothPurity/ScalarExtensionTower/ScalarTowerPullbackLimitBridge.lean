/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackLeftRoos
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRightRoos
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Scalar/pullback normalization in fixed Roos coordinates

Source: Stacks 07A4 and 0941; realization step 8 of
lem-pur-scalar-extension-tower-coherence.
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

/-- The scalar/pullback mate equation in fixed Roos coordinates.
Source: Stacks 06YY, 07A4 and 0941
(blueprint: stage3-pur-scalar-pullback-limit-bridge).

Proof: represent M by a good complex P and choose its coherent strict quotient
presentation C. The nested quotient coordinate t is invertible: the scalar
cochain counit computes on pull_E(C), as shown by levelwise K-flatness and
termwise flatness. The left and right normalization calculations identify both
maps, after t, with the same explicit ordinary scalarPullbackChain. Cancel t,
and use the system isomorphism's hom-inverse identity on the right. The original
strict tensor/pullback-square hypothesis is retained but not used.
-/
theorem scalarTowerPullbackLimitSquare_mate (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ML : CompletedOperations.Models.{u, u} l L W)
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true)
      (ME.calculus true) (ML.roos true))
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι (W false)
      (ME.calculus false) (ML.roos false))
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (M : sfIntegralConstructibleCategory l E (W false))
    (hF : IsSfDerivedComplete l E (W true)
      ((integralDerivedPullback.{u, u} l E f).obj M.obj))
    (_hstrict : leftRoute l E L ι f = rightRoute l E L ι f) :
    ((scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom ≫
        (ML.pullback f).realization.hom.app
          ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj) ≫
        (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonDerivedSequencePullback.{u, u} l L f).map
            (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
              (ML.roos false) SY M.obj)) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonSystemScalarPullback.{u, u} l E L ι f).inv.app
          ((ME.calculus false).reduction.obj M.obj))) =
    (SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj M.obj) ≫
        (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
            (pullbackReduction l E W ME f M.obj) ≫
          (integralComparisonSystemScalarPullback.{u, u} l E L ι f).hom.app
            ((ME.calculus false).reduction.obj M.obj))) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonSystemScalarPullback.{u, u} l E L ι f).inv.app
          ((ME.calculus false).reduction.obj M.obj)) := by
  let Q := integralOperationsGoodLocalization.{u, u} l E (W false)
  let V := (HomologicalComplex.quasiIso (scalarReductionSource.{u, u} l E (W false))
    (.up ℤ)).inverseImage (integralOperationsGoodComplex.{u, u} l E (W false)).ι
  have : Q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E (W false)
  have : Q.EssSurj := Localization.essSurj Q V
  let P := Q.objPreimage M.obj
  let eP : DerivedCategory.Q.obj P.obj ≅ M.obj := Q.objObjPreimageIso M.obj
  obtain ⟨C, eC, κ, hp, hc⟩ :=
    coherentPrimitiveReductionPresentation l E (ME.calculus false) P
  obtain ⟨q, hq⟩ :=
    scalarPullbackRoosCoordinates_exists l E L ι f P C (ME.calculus false) eC κ hp hc
  let t := scalarPullbackRoosCoordinate l E L ι f P C
    (ME.calculus false) (ML.roos true) M.obj eP eC q
  have : IsIso ((integralComparisonSequenceScalarModel.{u, u} l E L ι (W true)).ε.app
      (((integralComparisonSequencePullback.{u, u} l E f).mapHomologicalComplex (.up ℤ)).obj
        C)) := scalarPullbackQuotient_computes l E L ι f P C κ
  have : IsIso t := by
    dsimp only [t, scalarPullbackRoosCoordinate]
    infer_instance
  have hleft := scalarPullbackLeftRoos l E L ι W (ME.calculus false) ML SY f
    _hX _hY P M eP C eC κ hp hc q hq hF
  have hright := scalarPullbackRightRoos l E L ι W ME (ML.roos true) SX f
    _hX _hY P M eP C eC κ hp hc q hq hF
  apply (cancel_mono t).1
  simp only [Category.assoc] at hleft hright ⊢
  refine hleft.trans ?_
  symm
  have hcancel := (integralComparisonSystemScalarPullback.{u, u} l E L ι f).hom_inv_id_app
    ((ME.calculus false).reduction.obj M.obj)
  simp only [Functor.comp_obj] at hcancel
  have hm :
      (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
              (pullbackReduction l E W ME f M.obj) ≫
            (integralComparisonSystemScalarPullback.{u, u} l E L ι f).hom.app
              ((ME.calculus false).reduction.obj M.obj)) ≫
        (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonSystemScalarPullback.{u, u} l E L ι f).inv.app
            ((ME.calculus false).reduction.obj M.obj)) =
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
          (pullbackReduction l E W ME f M.obj)) := by
    rw [← Functor.map_comp, Category.assoc, hcancel]
    congr 1
    exact Category.comp_id _
  have hmt := congrArg (fun z ↦
    SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj M.obj) ≫ z ≫ t) hm
  simp only [Category.assoc] at hmt
  exact hmt.trans hright

end WeilConjectures.ScalarExtensionTower
