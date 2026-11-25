/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorShiftProperties
import all WeilConjectures.SixFunctors.Completed.CompletedTensorShiftRight
import WeilConjectures.SixFunctors.Completed.CompletedTensorFiniteShift
import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorRightShiftExt

/-! # Unique normalized shift in the signed completed second slot -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem roosShiftOnSite_hom_app (W : AlgebraicGeometry.Scheme.{u}) (r : ℤ)
    (β : finiteShiftIsoType l E W r) (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (roosShiftOnSite l E W r β).hom.app (P, Q) =
      (completedTensorShiftRoosIso
        ((integralOperationsTensorTowerFunctor l E W).obj (P, Q))
        ((integralOperationsTensorTowerFunctor l E W).obj (P, Q⟦r⟧))
        r (coneIso _ _ r (β.app (P, Q)))).hom := rfl

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 1024
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted
  goodOutputShiftIso goodInputShiftIso roosShiftNaturalIso quotientShiftOnSite
  goodShiftInclusionIso goodShiftLocalizationIso integralCompletedTensorDescent
  integralOperationsTensorTowerFunctor integralCompletedTensorComparison coneIso
  integralCompletedTensorFiniteShiftFormula completedTensorShiftConeFormula
  integralOperationsGoodComplex completedTensorShiftOneSub completedTensorShiftProductIso
  completedTensorShiftRoosIso integralOperationsRoos integralOperationsRoosMap DerivedCategory.Q

/-- Existence and uniqueness for the signed completed second slot.
Source: Stacks 011G, 014E, 06YU, 0941; blueprint purity transport, Step 2
(blueprint: lem-pur-integral-tensor-right-shift-unique).

Proof: use the already proved finite tower comparison, good-model shift and
normalized product/cone descent from CompletedTensorShiftRight. None of those
construction helpers requires invertibility of l on W. Its component equation
is precisely the required normalization. The separate representative
extensionality theorem identifies any other normalized comparison with it. -/
theorem integralTensorRightShift_existsUnique (W : Scheme.{u}) (r : ℤ) :
    ∃! σ : completedTensorShiftSecond (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r,
      integralCompletedTensorRightShiftProperty l E W r σ := by
  classical
  let D := DerivedCategory (integralTowerModules l E W)
  let L := integralOperationsGoodLocalization l E W
  obtain ⟨β, hβ⟩ := integralCompletedTensorFiniteShift l E W r
  let U := goodSecondShift l E W r
  let κ := goodInputShiftIso l E W r
  let ε := integralCompletedTensorComparison l E W
  let T := integralOperationsTensorOnGood l E W
  let τ' := goodOutputShiftIso l E W r β
  obtain ⟨σ, hσ⟩ := descendShift (L.prod L) U (completedTensorShiftSecond D r)
    (shiftFunctor D r) (integralCompletedTensor l E W) T ε κ τ' (by
      intro G' ε'
      exact completedTensorUniversal l E W G' ε')
  have hnorm : integralCompletedTensorRightShiftProperty l E W r σ := by
    intro Q₁ Q₂
    refine ⟨goodShift l E W Q₂ r, ?_⟩
    refine ⟨β.app (Q₁.obj, Q₂.obj), ?_,
      coneIso _ _ r (β.app (Q₁.obj, Q₂.obj)),
      coneIso_formula _ _ r (β.app (Q₁.obj, Q₂.obj)), ?_⟩
    · unfold integralCompletedTensorFiniteShiftFormula
      exact hβ Q₁.obj Q₂.obj
    · set_option backward.isDefEq.respectTransparency false in
        have h := hσ (Q₁, Q₂)
        simp only [κ, τ', goodInputShiftIso_hom_app, goodOutputShiftIso_hom_app,
          roosShiftOnSite_hom_app, quotientShiftOnSite_eq] at h
        dsimp only [U, L, ε, D, T, goodSecondShift, goodShiftFunctor,
          integralOperationsGoodLocalization, Functor.prod_obj, Functor.comp_obj,
          Functor.id_obj, ObjectProperty.lift, ObjectProperty.ι] at h
        exact h
  exact ⟨σ, hnorm, fun τ hτ ↦ integralTensorRightShift_ext l E W r τ σ hτ hnorm⟩

end WeilConjectures.IntegralSystemRealization
