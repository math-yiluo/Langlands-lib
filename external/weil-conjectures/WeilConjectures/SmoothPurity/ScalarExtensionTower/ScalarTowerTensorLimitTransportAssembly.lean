/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitStrictWitness
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitStrictEquationAssembly
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitRepresentativeTransport

/-! # Assembly of strict scalar/tensor representatives

Source: Stacks 07A4 and 0941; localization and total-limit transport in
realization step 8 of `lem-pur-scalar-extension-tower-coherence`.

The remaining assembly takes strict representative witnesses as input and
passes them through the localization, completion, realization and total-limit
maps.  It is separated from the strict representative calculation so that the
two arguments can be proved independently.
(blueprint: stage3-pur-scalar-tensor-limit-transport-assembly)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible]
  integralCompletedTensor integralDerivedPullback
  integralComparisonDerivedSequenceScalar integralComparisonDerivedSequencePullback
  pullbackReduction scalarReduction tensorReduction

set_option linter.unusedVariables false in
/-- Assemble strict representative witnesses into the completed limit square.

This is the localization and total-limit part of the proof.  The hypothesis
has only strict cochain data; in particular it contains no asserted equality
between the two completed composites in the conclusion.  Its proof is the
Roos-bridge naturality and localization argument from Stacks 07A4 and 0941.
Source: Stacks 07A4 and 0941 (blueprint: stage3-pur-scalar-tensor-limit-transport-assembly).
-/
theorem scalarTowerTensorLimitSquare_of_strictWitnesses (W : Scheme.{u})
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
    (hstrict : ∀ (P Q : Complex l E W) (hP : Good l E W P) (hQ : Good l E W Q),
      ∃ w : StrictTensorWitness l E L ι W SE SL α, w.P = P ∧ w.Q = Q) :
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
  apply scalarTowerTensorLimitSquare_of_representativeTransport l E L ι W SE SL ρE ρL SY TE TL
    _hl M N hT α
  apply scalarTowerTensorLimitSquare_on_good_representatives l E L ι W SE SL ρE ρL SY TE TL α
  intro P Q hP hQ
  obtain ⟨w, hwP, hwQ⟩ := hstrict P Q hP hQ
  obtain ⟨hsP, hsQ, heq⟩ := w.equation P Q hP hQ
  subst P
  subst Q
  exact ⟨hsP, hsQ, heq⟩

end WeilConjectures.ScalarExtensionTower
