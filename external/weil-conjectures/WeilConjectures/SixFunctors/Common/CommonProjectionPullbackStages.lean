/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent

/-! # The prescribed coherent pullback stage morphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.pairFunctorCoherent
attribute [local irreducible] rationalDerivedPullback
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

/-- Assemble the prescribed pullbacks and transition comparisons with their coherence proof.
Source: current blueprint common-stage pullback paragraph.
(blueprint: def-sf-common-projection-pullback-stages). -/
def commonProjectionPullbackStages
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hc : StageSystem.pairFunctorCoherent (stageSystem l Ω Y) (stageSystem l Ω X)
      (fun L ↦ rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L) f)
      (commonStagePullbackTransition l Ω f)) :
    (stageSystem l Ω Y).Morphism (stageSystem l Ω X) :=
  ⟨_, commonStagePullbackTransition l Ω f, hc⟩

end WeilConjectures
