/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Pullback along a surjective morphism

For a surjective morphism of schemes `π : T' ⟶ T`, the pullback `π^*` of étale sheaves of
`Λ`-modules is faithful, so that the unit `F ⟶ π_* π^* F` of the adjunction `π^* ⊣ π_*` is a
monomorphism. The stalk of `π^* F` at a geometric point `s` of `T'` is the stalk of `F` at
`s ≫ π` by `AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso`, and since `π` is
surjective the geometric points of `T` of this form already make up a conservative family.

## Main statements

- `AlgebraicGeometry.Etale.faithful_upperStar_of_surjective`: the pullback along a
  surjective morphism is faithful.
- `AlgebraicGeometry.Etale.mono_unit_app_of_surjective`: the unit `F ⟶ π_* π^* F` is a
  monomorphism for surjective `π`.
- `AlgebraicGeometry.Etale.reflectsIsomorphisms_upperStar_of_surjective`: the pullback along a
  surjective morphism reflects isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {T T' : Scheme.{u}} (π : T' ⟶ T)

/-- The pullback of étale sheaves of `Λ`-modules along a surjective morphism `π` is faithful:
a morphism killed by `π^*` is killed by the stalk functors at the geometric points `s ≫ π`,
which form a conservative family of points of `T` because `π` is surjective. -/
theorem Etale.faithful_upperStar_of_surjective (hπ : Function.Surjective π.base) :
    (π)^*[ModuleCat.{u + 1} Λ].Faithful where
  map_injective {G G'} φ ψ h := by
    have hP := (Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
      T (fun t' : T' ↦ T'.algClosurePoint t' ≫ π) (by
        refine Set.eq_univ_of_forall fun t ↦ ?_
        obtain ⟨t', rfl⟩ := hπ t
        obtain ⟨x, hx⟩ : t' ∈ ⋃ s : T', Set.range (T'.algClosurePoint s) := by
          rw [T'.iUnion_range_algClosurePoint]
          trivial
        obtain ⟨s, x, rfl⟩ := Set.mem_iUnion.1 ⟨x, hx⟩
        exact Set.mem_iUnion.2 ⟨s, x, rfl⟩)).jointlyReflectIsomorphisms (ModuleCat.{u + 1} Λ)
    have : LocallySmall.{u + 1} T.Etale := locallySmall_max.{u + 1, u}
    rw [← sub_eq_zero]
    refine hP.eq_zero_of_map_eq_zero _ ?_
    rintro ⟨-, ⟨t'⟩⟩
    change ((Scheme.pointSmallEtale (T'.algClosurePoint t' ≫ π)).ulift.{u + 1}).sheafFiber.map
      (φ - ψ) = 0
    rw [← NatIso.naturality_1 (Etale.upperStarCompUliftSheafFiberIso _ π
      (T'.algClosurePoint t')) (φ - ψ)]
    simp [Functor.map_sub, h]

/-- The unit `F ⟶ π_* π^* F` of the adjunction `π^* ⊣ π_*` is a monomorphism when `π` is
surjective, `π^*` being faithful by `AlgebraicGeometry.Etale.faithful_upperStar_of_surjective`.
This is the first step of the proof of blueprint `lemma-integral-changes-source-base--1`. -/
theorem Etale.mono_unit_app_of_surjective (hπ : Function.Surjective π.base)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app F) :=
  have := Etale.faithful_upperStar_of_surjective Λ π hπ
  (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit_mono_of_L_faithful F

/-- The pullback of étale sheaves of `Λ`-modules along a surjective morphism `π` reflects
isomorphisms: it is faithful by `AlgebraicGeometry.Etale.faithful_upperStar_of_surjective`, so
it reflects monomorphisms and epimorphisms, and the category of sheaves is balanced. -/
theorem Etale.reflectsIsomorphisms_upperStar_of_surjective (hπ : Function.Surjective π.base) :
    (π)^*[ModuleCat.{u + 1} Λ].ReflectsIsomorphisms :=
  have := Etale.faithful_upperStar_of_surjective Λ π hπ
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms _

end AlgebraicGeometry
