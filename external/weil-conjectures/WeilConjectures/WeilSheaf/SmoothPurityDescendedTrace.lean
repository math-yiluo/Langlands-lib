/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible

/-!
# Descending a smooth trace from the finite base field

The smooth trace over the finite field can be pulled back to the geometric fibre with
its canonical Weil structure. Compact-support base change then gives a morphism in the
derived category of condensed Weil sheaves. This construction does not require a choice
of an equivariant orientation on the geometric fibre.

The source here is the pullback of the actual condensed Tate line. Identifying it with
the scalar-defined Tate twist of native Weil sheaves is a separate comparison.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (l : ℕ) [Fact l.Prime] {k₀ : Type u} [Field k₀] [Finite k₀]
  [Fact (ringChar k₀).Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Over (Spec (.of k₀))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ)

/-- The finite-field smooth trace, pulled to the geometric fibre with Weil structures. -/
noncomputable def geometricFiberWeilSmoothTrace :
    (weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj l)
        (compactificationOverField f) (Over.w f)).obj
      ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) X.hom).mapDerivedCategory.obj
        (boundedConstructibleTateTwist l X d (2 * d)).obj) ⟶
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) Y.hom).mapDerivedCategory.obj
        (𝟙_ _) :=
  (boundedConstructibleLowerShriekGeometricFiberWeilIso l f).inv.app
      (boundedConstructibleTateTwist l X d (2 * d)) ≫
    (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) Y.hom).mapDerivedCategory.map
      (smoothTrace l f d).hom

/-- Compact-support base change identifies the descended trace with the pulled-back trace. -/
theorem geometricFiberWeilSmoothTrace_baseChange :
    (boundedConstructibleLowerShriekGeometricFiberWeilIso l f).hom.app
        (boundedConstructibleTateTwist l X d (2 * d)) ≫ geometricFiberWeilSmoothTrace l f d =
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) Y.hom).mapDerivedCategory.map
        (smoothTrace l f d).hom := by
  unfold geometricFiberWeilSmoothTrace
  rw [Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
