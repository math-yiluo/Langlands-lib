/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift

/-!
# The compact-support direct image of every compactification is triangulated

For every compactification `c = (X ⟶[j] X̄ ⟶[f̄] Y)` of a morphism `f`, the compact-support
candidate `Rf^c_! = Rf̄_* j_! : D(X_proét) ⥤ D(Y_proét)`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`) is a triangulated
functor: the functor `D(j_!)` induced by the exact extension by zero is triangulated, and so is
the total right derived functor `Rf̄_*` (blueprint
`proposition-construction-independence-rf-shriek--1`). For the chosen compactification this is the
commutation with shifts `AlgebraicGeometry.ProEtale.commShiftRightDerivedLowerShriek`.

## Main statements

- `AlgebraicGeometry.ProEtale.commShiftRightDerivedLowerShriekOfCompactification`
- `AlgebraicGeometry.ProEtale.isTriangulated_rightDerivedLowerShriekOfCompactification`
- `AlgebraicGeometry.ProEtale.isTriangulated_rightDerivedLowerShriek`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The compact-support candidate `Rf^c_! = D(j_!) ⋙ Rf̄_*` of a compactification `c` commutes
with shifts: it is a composite of two functors commuting with shifts. -/
noncomputable instance commShiftRightDerivedLowerShriekOfCompactification
    (c : Compactification f) :
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).CommShift ℤ :=
  inferInstanceAs ((D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).CommShift ℤ)

/-- Blueprint `proposition-construction-independence-rf-shriek--1`: Triangulatedness of the
finite-level compact-support direct image. For every compactification `c = (j, f̄)` of `f`, the
functor `Rf^c_! = Rf̄_* j_! : D(X_proét) ⥤ D(Y_proét)` preserves shifts
(`commShiftRightDerivedLowerShriekOfCompactification`) and distinguished triangles: the
extension by zero `j_!` is exact, so `D(j_!)` is triangulated, and the derived direct image
`Rf̄_*`, computed by K-injective resolutions, is triangulated. -/
instance isTriangulated_rightDerivedLowerShriekOfCompactification (c : Compactification f) :
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).IsTriangulated :=
  inferInstanceAs ((D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).IsTriangulated)

/-- The compact-support direct image `Rf_!` for the chosen compactification is triangulated. -/
instance isTriangulated_rightDerivedLowerShriek [HasCompactification f] :
    (ProEtale.rightDerivedLowerShriek A f).IsTriangulated :=
  inferInstanceAs ((D(((HasCompactification.compactification f).i)_!open[A]) ⋙
    R(((HasCompactification.compactification f).g)_*[A])).IsTriangulated)

end AlgebraicGeometry.ProEtale
