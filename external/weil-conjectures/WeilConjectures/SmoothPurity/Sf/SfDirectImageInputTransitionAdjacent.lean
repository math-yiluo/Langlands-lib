/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
import WeilConjectures.SixFunctors.Compact.CompactSupportInputTowerCompatibility

/-! # The adjacent completed input transition

Source: Stacks Tags 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The adjacent completed input reduction is the canonical derived transition.
This is the specialization of the compact-support input tower compatibility to
successive indices; it is the input-transition part of the direct-image formula.
Source: Stacks Tags 06YY and 07A6.
(blueprint: lem-sf-direct-image-input-transition-adjacent). -/
theorem sfDirectImageInputTransition_adjacent
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (scalarReductionDerivedRestriction l E X (n + 1)).map
          (compactSupportReductionMap l E X (n + 1) n (Nat.le_succ n) K) ≫
        (compactSupportRestrictionComp l E X (n + 1) n (Nat.le_succ n)).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K) =
      (sfDerivedReductionTransition l E X n).app K := by
  have h := compactSupportInput_completed_tower l E X K (n + 1) n (Nat.le_succ n)
  simpa only [sfIntegralReductionTower,
    Functor.ofOpSequence_map_homOfLE_succ] using h

end WeilConjectures
