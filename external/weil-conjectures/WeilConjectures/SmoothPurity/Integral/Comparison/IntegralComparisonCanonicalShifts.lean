/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift

/-! # Canonical shifts for whole-system coefficient realizations

The limit uses its actual right-derived shift, reduction uses its adjoint mate,
and scalar change uses its universal cochain counit. These constructions fix
one common shift before studying either realization comparison.
Source: Stacks Tags 014E, 06YY and 0941.
(blueprint: def-sf-integral-comparison-canonical-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The shift on the actual sequence limit, through exact restriction and Rlim.
Source: Stacks 0941 (blueprint: def-sf-integral-comparison-canonical-shifts). -/
@[instance_reducible] def integralComparisonLimitShift (X : Scheme.{u}) :
    (coefficientSequenceLimit l E X).CommShift ℤ := by
  unfold coefficientSequenceLimit coefficientSequenceDerivedRestriction
    coefficientConstantTowerLimit
  infer_instance

/-- Exact sequence pullback carries the termwise derived shift.
Source: Stacks 014E (blueprint: def-sf-integral-comparison-canonical-shifts). -/
@[instance_reducible] def integralComparisonSequencePullbackShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralComparisonDerivedSequencePullback l E f).CommShift ℤ := by
  unfold integralComparisonDerivedSequencePullback
  infer_instance

/-- Reduction carries the adjoint mate of the fixed total-limit shift.
Source: Stacks 0941 (blueprint: def-sf-integral-comparison-canonical-shifts). -/
@[instance_reducible] def integralComparisonReductionShift (X : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E X) : S.reduction.CommShift ℤ := by
  letI := integralComparisonLimitShift l E X
  exact S.adjunction.leftAdjointCommShift ℤ

/-- The universal scalar cochain counit determines the coherent scalar shift.
Source: Stacks 06YY and 014E
(blueprint: def-sf-integral-comparison-canonical-shifts). -/
theorem integralComparisonSequenceScalarShift_exists
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u}) :
    ∃ s : (integralComparisonDerivedSequenceScalar l E L ι X).CommShift ℤ,
      letI : (integralComparisonSequenceScalarModel l E L ι X).T.CommShift ℤ := s
      NatTrans.CommShift (integralComparisonSequenceScalarModel l E L ι X).ε ℤ := by
  let M := integralComparisonSequenceScalarModel l E L ι X
  let := M.additive
  let := M.universal
  exact Functor.rightKanExtension_coherentShift _ DerivedCategory.Q M.T M.ε
    (Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso _ (.up ℤ)))

/-- The uniquely counit-normalized scalar shift, independently of pullback.
Source: Stacks 06YY (blueprint: def-sf-integral-comparison-canonical-shifts). -/
@[instance_reducible] def integralComparisonSequenceScalarShift
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u}) :
    (integralComparisonDerivedSequenceScalar l E L ι X).CommShift ℤ :=
  (integralComparisonSequenceScalarShift_exists l E L ι X).choose

end WeilConjectures
