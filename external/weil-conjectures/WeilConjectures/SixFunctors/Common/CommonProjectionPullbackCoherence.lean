/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackStages
/-! # The prescribed normalized pullback stage data -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.pairFunctorCoherent
attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Coherence of the prescribed normalized pullback transitions.
Source: common-stage pullback normalization in the blueprint.
(blueprint: lem-sf-common-projection-pullback-stage-coherence).
Proof: take the coherence proof from normalized pullback descent. This chooses only
proof data, and leaves the prescribed pullback functors and transition maps fixed. -/
theorem commonProjectionPullbackCoherence :
    StageSystem.pairFunctorCoherent (stageSystem l Ω Y) (stageSystem l Ω X)
      (fun L ↦ rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L) f)
      (commonStagePullbackTransition l Ω f) :=
  (commonStagePullbackNormalizedDescent l Ω f).choose

end WeilConjectures
