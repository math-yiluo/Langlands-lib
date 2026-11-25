/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientCoefficientPullbackFiniteIso
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientCoefficientSequencePullbackIso

/-! # Components of ambient pullback coherence

Source: Stacks 03CB, 03D3, 03EL, 07A4 and 04VG.
(blueprint: lem-sf-ambient-coefficient-pullback-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

/-- Inverse image preserves the actual coefficient ring, on the finite or sequence site.
Source: Stacks 0H7J, 03CB and 0941
(blueprint: lem-sf-ambient-coefficient-pullback-iso).
Proof: at a finite level identify each coefficient sheaf with the sheafification
of the constant ring presheaf. The two composites of inverse image and the
constant-sheaf functor are left adjoint to evaluation of direct image at the
terminal object; the fibre-product terminal comparison identifies those right
adjoints. The unique left-adjoint comparison is invertible, and its unit on
constant sections identifies it with ringMap. On the sequence site, inverse image
along the product with the identity of the index category is the levelwise
inverse image. This follows by restricting the levelwise adjunction bijections
to compatible families; their naturality gives compatibility with all quotient
maps. Evaluation on ordinary ring sheaves reflects isomorphisms, so the finite
comparisons prove invertibility on the sequence site as well. No derived
evaluation, flat transition, nonzero-ring or finiteness hypothesis is used. -/
theorem coefficientPullback_isIso {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    IsIso (ringMap ell E f s) := by
  cases s with
  | some n => exact coefficientPullback_some_isIso ell E f n
  | none => exact coefficientPullback_none_isIso ell E f

end WeilConjectures.AmbientPullbackTensor
