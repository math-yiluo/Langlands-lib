/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The derived pushforward of Weil complexes is triangulated

The derived pushforward `Rφ_*` of Weil complexes is the restriction of the total right derived
functor of the pushforward of pro-étale Weil sheaves, a triangulated functor between the derived
categories; hence it commutes with the shift and is triangulated.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

noncomputable instance : (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).CommShift ℤ :=
  ObjectProperty.commShiftLiftFullSubcategory _ _ _ _

/-- The derived pushforward of Weil complexes is a triangulated functor. -/
instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).IsTriangulated :=
  ObjectProperty.isTriangulated_liftFullSubcategory _ _ _ _

end AlgebraicGeometry
