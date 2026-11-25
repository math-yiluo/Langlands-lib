/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The original completion augmentation and the selected reduction calculus

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4, 0941 (blueprint: lem-pod-reindexing-completion-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The original completion augmentation agrees with the actual unit of the selected
reduction/limit adjunction.
Source: blueprint theorem-poincare-duality-frobenius--2, proof Steps 1 and 5;
Stacks 07A4, 0941 (blueprint: lem-pod-reindexing-completion-normalization).

Proof: take the normalized primitive completion model on the singleton family W.
Both its reduction functor and the selected reduction functor are left adjoint to
the same total-limit functor. The unique left-adjoint comparison identifies their
actual units. Whisker that comparison by total limit and compose it with the
primitive model's completion comparison. The primitive unit normalization and the
unit formula for the unique left-adjoint comparison give the required equality.
The construction does not use nonemptiness of W or boundedness of a complex. -/
theorem podReindexingCompletionNormalization (W : Scheme.{t})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃ e : IntegralOnSlice.completion l E W none ≅
        (podReindexCalculus l E W).reduction ⋙ coefficientSequenceLimit l E W,
      ∀ K : DerivedCategory (scalarReductionSource l E W),
        (IntegralOnSlice.completionUnit l E W none).app K ≫ e.hom.app K =
          (podReindexCalculus l E W).adjunction.unit.app K := by
  obtain ⟨M, _⟩ := CompletedOperations.normalizedCompletedOperationModels l E
    (fun _ : Unit ↦ W) (fun _ w ↦ isUnit_of_invertible (l : W.residueField w))
  let e := Adjunction.leftAdjointUniq (M.calculus ()).adjunction
    (podReindexCalculus l E W).adjunction
  refine ⟨M.completion () ≪≫ isoWhiskerRight e (coefficientSequenceLimit l E W), ?_⟩
  intro K
  change (IntegralOnSlice.completionUnit l E W none).app K ≫
    (M.completion ()).hom.app K ≫ (coefficientSequenceLimit l E W).map (e.hom.app K) = _
  rw [← Category.assoc, M.completion_unit]
  exact Adjunction.unit_leftAdjointUniq_hom_app _ _ K

end WeilConjectures
