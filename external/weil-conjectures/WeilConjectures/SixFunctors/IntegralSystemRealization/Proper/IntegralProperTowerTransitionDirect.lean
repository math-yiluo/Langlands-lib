/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SmoothPurity.Sf.SfDirectImageTransitionPresentation
import all WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all WeilConjectures.SixFunctors.Compact.CompactSupportInputTowerCompatibility
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Pull.IntegralPullEvaluationQuotientSquare
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Pull.IntegralPullEvaluationDirectTransitionSquare

set_option linter.privateModule false

/-! # Finite direct-image transition transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section Transport
universe a b c v w
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  (F : A ⥤ C) (G : B ⥤ D) [F.Additive] [G.Additive]
  (S S₀ : A ⥤ B) (T T₀ : C ⥤ D)
  [S.Additive] [S₀.Additive] [T.Additive] [T₀.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits S₀] [PreservesFiniteColimits S₀]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits T₀] [PreservesFiniteColimits T₀]

end Transport

private theorem completedComp_eq (W : Scheme.{u})
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℕ) :
    normalizedDVRResCompletedComp l E W D hl n.le_succ =
      compactSupportSystemRestrictionComp l E W n.le_succ := by
  have he := ordinaryCompletedComp_eq
    (completedIntegralCoefficientProjection l E W D hl (n + 1))
    (normalizedDVRQuotient l E W n.le_succ)
    (completedIntegralCoefficientProjection l E W D hl n)
    (limit.w (integralCoefficientSheafSystem l E W) (homOfLE n.le_succ).op)
    (coefficientRestrictionComp l E W n.le_succ)
  dsimp only [normalizedDVRResCompletedComp]
  erw [he]
  rfl

attribute [local instance] normalizedDVRModuleRes_limits normalizedDVRModuleRes_colimits

end WeilConjectures.IntegralSystemRealization
