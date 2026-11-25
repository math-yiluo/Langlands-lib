/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierDualWeil

/-!
# The two exceptional base change maps agree

The exceptional base change map `Lg'^* Rf^! ⟶ Rf'^! Lg^*` of a cartesian square appears twice in
the library: as `AlgebraicGeometry.Etale.upperShriekBaseChangeMap`, the right adjoint exchange of
the compactly supported base change isomorphism, and as
`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`, its mate. They are equal, and so
the dualizing complex base change map `AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap` is
the component of `upperShriekBaseChangeMap` at `Λ_Y` followed by `Rf'^!(Lg^* Λ_Y ≅ Λ_{Y'})`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
  {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [HasCompactification f] [HasCompactification f']
  [QuasiCompact f']

/-- The right adjoint exchange `AlgebraicGeometry.Etale.upperShriekBaseChangeMap` is the mate
`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`. -/
lemma upperShriekBaseChangeMap_eq_rightDerivedUpperShriekBaseChangeMap
    (sq : IsPullback g' f' f g) :
    upperShriekBaseChangeMap Λ sq = rightDerivedUpperShriekBaseChangeMap Λ sq := by
  simp only [upperShriekBaseChangeMap, rightDerivedUpperShriekBaseChangeMap,
    Adjunction.rightAdjointExchange, asIso_inv]

/-- The dualizing complex base change map is the component of
`AlgebraicGeometry.Etale.upperShriekBaseChangeMap` at the unit, followed by
`Rf'^!(Lg^* Λ_Y ≅ Λ_{Y'})`. -/
lemma upperShriekBaseChangeMap_app_comp_map_leftDerivedUpperStarUnitIso_hom
    (sq : IsPullback g' f' f g) :
    (upperShriekBaseChangeMap Λ sq).app (𝟙_ _) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom =
      dualizingComplexBaseChangeMap Λ sq := by
  rw [upperShriekBaseChangeMap_eq_rightDerivedUpperShriekBaseChangeMap,
    dualizingComplexBaseChangeMap]

end AlgebraicGeometry.Etale
