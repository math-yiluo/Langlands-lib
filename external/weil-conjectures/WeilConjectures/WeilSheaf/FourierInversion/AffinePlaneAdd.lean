/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs

/-!
# The addition of the affine line

The addition `(x, y) ↦ x + y` of `𝔸¹ ×_{k₀} 𝔸¹` to the affine line
(`AlgebraicGeometry.affinePlane.add`); it is the group law `AlgebraicGeometry.AffineSpace.add`
of the additive group (`AlgebraicGeometry.affinePlane.add_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀]

variable (k₀) in
/-- The addition `(x, y) ↦ x + y` of the affine plane `𝔸¹ ×_{k₀} 𝔸¹` to the affine line. -/
noncomputable def affinePlane.add : affinePlane k₀ ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) fun _ ↦
    (affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) +
      (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit)

instance : (affinePlane.add k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.homOfVector_over _ _⟩

lemma affinePlane.add_appTop_coord :
    (affinePlane.add k₀).appTop (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit) =
      (affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) +
        (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- The addition of the affine plane is the group law of the additive group. -/
lemma affinePlane.add_eq :
    affinePlane.add k₀ = AffineSpace.add PUnit.{u + 1} (Spec (CommRingCat.of k₀)) := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · exact (AffineSpace.homOfVector_over _ _).trans (AffineSpace.add_over _ _).symm
  · exact (AffineSpace.homOfVector_appTop_coord _ _ _).trans
      (AffineSpace.add_appTop_coord _ _ _).symm

end AlgebraicGeometry
