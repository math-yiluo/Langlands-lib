/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps

/-!
# Base change of the exceptional inverse image along an open immersion

The open-immersion case of the elementary cases in the proof of blueprint
`proposition-exceptional-inverse-image-smooth-morphism--6`: for a quasi-compact open immersion
`j : U ⟶ X` and a cartesian square

```
  U' --g'--> U
  |          |
  j'         j
  ↓          ↓
  X' --g---> X
```

with `j'` quasi-compact, the canonical base change map `Lg'^* Rj^! ⟶ Rj'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) is an isomorphism.

## Proof

The extension by zero `Rj'_! ≅ D(j'_!)` is fully faithful, so the unit of `Rj'_! ⊣ Rj'^!` is an
isomorphism, and then so is `Rj'^!` of its counit. Applying `Rj'^!` to the defining relation
`Rj'_! β_K ≫ ε' = Ex_!⁻¹ ≫ Lg^* ε_K` of the mate `β`, the map `β_K` is an isomorphism as soon as
`Rj'^! Lg^* ε_K` is one. Through `Rj'^! ≅ D(j'^*)` and the composition of pullbacks along the
square, this is `Lg'^* Lj^* ε_K`, and `Lj^* ε_K ≅ Rj^! ε_K` is an isomorphism by the triangle
identity, the unit of `Rj_! ⊣ Rj^!` being an isomorphism as well.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_of_isOpenImmersion`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- For a quasi-compact open immersion `j`, the unit of `Rj_! ⊣ Rj^!` is an isomorphism:
`Rj_! ⋙ Rj^! ≅ D(j_!) ⋙ D(j^*) ≅ 𝟭`. -/
instance isIso_rightDerivedUpperShriekAdjunction_unit_of_isOpenImmersion {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j] [QuasiCompact j] :
    IsIso (rightDerivedUpperShriekAdjunction Λ j).unit :=
  (rightDerivedUpperShriekAdjunction _ j).isIso_unit_of_iso
    (Functor.isoWhiskerRight (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j) _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j) ≪≫
      (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).unit).symm)

/-- Let `L' ⊣ R'` be an adjunction whose unit is an isomorphism. A morphism `β : A ⟶ R' Z` is an
isomorphism as soon as `R'` of its transpose `L' β ≫ ε'_Z` is one: `R' ε'_Z` is invertible,
and `R' L' β` is `β` up to the unit. -/
lemma _root_.CategoryTheory.Adjunction.isIso_of_isIso_map_comp_counit {C D : Type*}
    [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.unit] {A : C}
    {Z : D} (β : A ⟶ R.obj Z) {φ : L.obj A ⟶ Z} (h : L.map β ≫ adj.counit.app Z = φ)
    (hφ : IsIso (R.map φ)) : IsIso β := by
  have := adj.isIso_map_counit_app_of_isIso_unit Z
  refine (NatIso.isIso_map_iff (asIso adj.unit) β).2 ?_
  rw [Functor.comp_map,
    ← isIso_comp_right_iff _ (R.map (adj.counit.app Z)), ← Functor.map_comp, h]
  exact hφ

/-- **Base change along an open immersion.** For a quasi-compact open immersion `j` and a
cartesian square `g' ≫ j = j' ≫ g` with `j'` quasi-compact, the canonical base change map
`Lg'^* Rj^! ⟶ Rj'^! Lg^*` is an isomorphism. Here the open immersion is the morphism `j` whose
exceptional inverse image is taken; for an open immersion `g` along which one base changes, see
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) [IsOpenImmersion f] [QuasiCompact f] [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have : IsOpenImmersion f' := MorphismProperty.of_isPullback sq ‹IsOpenImmersion f›
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  let adj := rightDerivedUpperShriekAdjunction Λ f
  let adj' := rightDerivedUpperShriekAdjunction Λ f'
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  refine adj'.isIso_of_isIso_map_comp_counit _
    (mateEquiv_counit adj adj' (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)) K) ?_
  rw [Functor.map_comp, isIso_comp_left_iff,
    NatIso.isIso_map_iff (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ f'),
    ← NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ f'), ← Functor.comp_map,
    ← NatIso.isIso_map_iff (leftDerivedUpperStarComp _ f' g),
    NatIso.isIso_map_iff (leftDerivedUpperStarComp _ g' f (f' ≫ g) sq.w.symm), Functor.comp_map]
  have := adj.isIso_map_counit_app_of_isIso_unit K
  have : IsIso ((L((f)^*[ModuleCat.{u + 1} Λ])).map (adj.counit.app K)) := by
    rw [NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ f),
      ← NatIso.isIso_map_iff (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ f)]
    infer_instance
  infer_instance

end Etale

end AlgebraicGeometry
