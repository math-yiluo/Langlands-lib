/-
Copyright (c) 2026 The Weil Conjectures Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil Conjectures Contributors
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.LineSmooth
public import WeilConjectures.WeilSheaf.SmoothPurity
public import WeilConjectures.WeilSheaf.TateTwistPullback

/-!
# The affine-line adjunction from smooth purity

An affine-line bundle is smooth of relative dimension one. Smooth purity therefore
gives its compact-support adjunction, and compatibility of pullback with Tate twists
and shifts moves the twist to the base.

Together with homotopy invariance, this proves the rank-one Thom isomorphism without
using `WeilComplex.exists_weilTrace_of_isPullback`. That separate trace statement and
its lifting construction in `AffineLineBundle` are unused by this route. The input is smooth
purity for a separated base,
`WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth_of_isSeparated`; the base `X` of the
line bundle is therefore assumed separated over `k₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (π : Y ⟶ X) (s : Y ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))]
  (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

include hπ in
/-- The compact-support adjunction of an affine-line bundle over a separated base follows from
smooth purity and compatibility of pullback with twists and shifts. -/
theorem nonempty_affineLineAdjunction_of_smoothPurity :
    Nonempty (derivedLowerShriek k₀ l π ⊣
      (tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙
        upperStar π) := by
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π]
    infer_instance
  have : SmoothOfRelativeDimension 1 π :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hπ.flip
      (inferInstance : SmoothOfRelativeDimension 1
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  obtain ⟨adj⟩ :=
    nonempty_derivedLowerShriek_adjunction_of_smooth_of_isSeparated (k₀ := k₀) (l := l) π 1
  exact ⟨adj.ofNatIsoRight (tateTwistShiftCompUpperStarIso (k₀ := k₀) (l := l) π 1 2).symm⟩

end AlgebraicGeometry.WeilComplex
