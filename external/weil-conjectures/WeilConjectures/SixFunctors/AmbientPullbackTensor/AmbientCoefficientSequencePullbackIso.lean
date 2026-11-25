/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientCoefficientSequencePullbackIsoApp

/-! Sequence-site component of ambient coefficient pullback.
Source: Stacks 03CB and 0941.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-sequence).

The product-site inverse image is computed levelwise.  The finite-stage
comparisons assemble to a morphism of compatible families, and the assembled
inverse is checked componentwise under the evaluation functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Sequence coefficient pullback is invertible.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-sequence) -/
theorem coefficientPullback_none_isIso {X Y : Scheme.{t}}
    (f : X ⟶ Y) :
    IsIso (ringMap ell E f none) := by
  let F := sheafToPresheaf (topology X none) CommRingCat.{max u (t + 1)}
  have hF : IsIso (F.map (ringMap ell E f none)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    exact coefficientPullback_none_isIso_app ell E f U.unop
  exact isIso_of_reflects_iso (ringMap ell E f none) F

end WeilConjectures.AmbientPullbackTensor
