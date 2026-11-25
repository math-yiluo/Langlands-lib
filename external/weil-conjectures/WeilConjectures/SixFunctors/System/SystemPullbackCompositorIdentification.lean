/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorCoherence
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # Identifying the two canonical presentations of system pullback

Source: Stacks 03D3, 03EL and 07A7. Both direct images use the same map on
constant sections; their inverse images and composition maps are fixed by adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable {X Y Z : Scheme.{u}}

private theorem chosen_left_eq {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) [F.IsRightAdjoint] [G.IsRightAdjoint] (h : F = G) :
    F.leftAdjoint = G.leftAdjoint := by
  subst G
  rfl

private theorem sequence_ring_eq (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f = AmbientPullbackTensor.ringUnit l E f none := by
  apply (pullbackTensorSequenceRing_existsUnique l E f).unique
  · intro n U
    unfold pullbackTensorSequenceRing pullbackTensorSequenceRingMap
    rfl
  · intro n U
    rfl

/-- Both presentations of direct image use precisely the same ringed sequence-site map.
Source: Stacks 03D3 (blueprint: lem-sf-system-pullback-compositor-identification).
Proof: the unique coefficient map is the map on constant sections at every (n,U).
The displayed direct images are the same pushforward after replacing that map. -/
theorem sequence_direct_eq (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f = AmbientPullbackTensor.push l E f none := by
  unfold pullbackTensorSequenceDirect
  rw [sequence_ring_eq]
  rfl

/-- The inverse-image presentations agree because leftAdjoint is applied to equal functors.
Source: Stacks 03D3 (blueprint: lem-sf-system-pullback-compositor-identification).
Proof: apply congruence to the established equality of the right adjoints. -/
theorem sequence_inverse_eq (f : X ⟶ Y) :
    pullbackTensorSequenceInverse l E f = AmbientPullbackTensor.pull l E f none := by
  unfold pullbackTensorSequenceInverse AmbientPullbackTensor.pull
  let : (AmbientPullbackTensor.push l E f none).IsRightAdjoint :=
    AmbientPullbackTensor.pushRightAdjoint l E f none
  exact chosen_left_eq _ _ (sequence_direct_eq l E f)

/-- Exact localization preserves the equality of these inverse-image presentations.
Source: Stacks 015F (blueprint: lem-sf-system-pullback-compositor-identification).
Proof: apply congruence to mapDerivedCategory. -/
theorem sequence_derived_eq (f : X ⟶ Y) :
    pullbackTensorSequenceDerived l E f = AmbientPullbackTensor.derivedPull l E f none := by
  unfold pullbackTensorSequenceDerived AmbientPullbackTensor.derivedPull
  congr 1
  exact sequence_inverse_eq l E f

end WeilConjectures
