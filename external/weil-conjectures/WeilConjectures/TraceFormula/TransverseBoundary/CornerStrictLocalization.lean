/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.TraceFormula.TransverseBoundary.Basic

/-!
# The complement of the divisors in the strict localization at the corner

Let `S` be the strict localization of the surface `Z` of a transverse corner
(`AlgebraicGeometry.Scheme.TransverseCorner`) at a geometric point `z̄`, with the divisors
`X_S, Y_S`. This file introduces `S - (X_S ∪ Y_S) = S ×_Z (Z - (X ∪ Y))`, with its open immersion
into `S - Y_S = S ×_Z (Z - Y)` (the scheme `pullback C.j (strictLocalizationToBase zbar)`, also
called `puncturedStrictLocalization` downstream) and its projection to `Z - (X ∪ Y)`
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`).

## Main definitions

- `AlgebraicGeometry.Scheme.TransverseCorner.strictLocalizationComplement`: `S - (X_S ∪ Y_S)`.
- `AlgebraicGeometry.Scheme.TransverseCorner.strictLocalizationComplementι`: the open immersion
  `S - (X_S ∪ Y_S) ⟶ S - Y_S`.
- `AlgebraicGeometry.Scheme.TransverseCorner.strictLocalizationComplementToV`: the projection
  `S - (X_S ∪ Y_S) ⟶ Z - (X ∪ Y)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] (C : TransverseCorner k) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (zbar : Spec (.of Ω) ⟶ C.Z)

/-- `S - (X_S ∪ Y_S)`: the inverse image of `Z - (X ∪ Y)` in the strict localization `S = Z_(z̄)`,
as the inverse image of `Z - (X ∪ Y)` under `S - Y_S ⟶ Z - Y`. -/
noncomputable abbrev strictLocalizationComplement : Scheme.{u} :=
  pullback C.i (pullback.fst C.j (strictLocalizationToBase zbar))

/-- The open immersion `S - (X_S ∪ Y_S) ⟶ S - Y_S`. -/
noncomputable abbrev strictLocalizationComplementι :
    C.strictLocalizationComplement zbar ⟶ pullback C.j (strictLocalizationToBase zbar) :=
  pullback.snd _ _

/-- The projection `S - (X_S ∪ Y_S) ⟶ Z - (X ∪ Y)`. -/
noncomputable abbrev strictLocalizationComplementToV :
    C.strictLocalizationComplement zbar ⟶ C.V :=
  pullback.fst _ _

/-- The cartesian square `S - (X_S ∪ Y_S) = (S - Y_S) ×_{Z - Y} (Z - (X ∪ Y))`. -/
lemma isPullback_strictLocalizationComplement :
    IsPullback (C.strictLocalizationComplementToV zbar) (C.strictLocalizationComplementι zbar)
      C.i (pullback.fst C.j (strictLocalizationToBase zbar)) :=
  IsPullback.of_hasPullback _ _

end AlgebraicGeometry.Scheme.TransverseCorner
