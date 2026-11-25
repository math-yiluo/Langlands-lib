/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic

/-!
# Vanishing of geometric stalks under change of the geometric point

For a geometric point `s : Spec Ω ⟶ T` and a morphism of fields `Spec Ω' ⟶ Spec Ω`, the
derived pullback along `Spec Ω' ⟶ Spec Ω` is conservative (the morphism is surjective), so the
vanishing of the stalk `L(a ≫ s)^* M` implies that of `Ls^* M`. This reduces vanishing at a
geometric point with separably closed field to vanishing at one with algebraically closed field
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`).

## Main statements

- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_of_isZero_comp`
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- If the derived pullback of `M` along the composite `a ≫ s` of a geometric point
`s : Spec Ω ⟶ T` with a morphism `a : Spec Ω' ⟶ Spec Ω` vanishes, so does `Ls^* M`. -/
theorem isZero_leftDerivedUpperStar_of_isZero_comp {T : Scheme.{u}} {Ω Ω' : Type u} [Field Ω]
    [Field Ω'] (a : Spec (.of Ω') ⟶ Spec (.of Ω)) (s : Spec (.of Ω) ⟶ T)
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsZero ((L((a ≫ s)^*[ModuleCat.{u + 1} Λ])).obj M)) :
    IsZero ((L((s)^*[ModuleCat.{u + 1} Λ])).obj M) := by
  rw [_root_.DerivedCategory.isZero_iff]
  intro q
  have hz : IsZero ((a)^*[ModuleCat.{u + 1} Λ].obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((L((s)^*[ModuleCat.{u + 1} Λ])).obj M))) :=
    ((_root_.DerivedCategory.homologyFunctor _ q).map_isZero
      (h.of_iso ((leftDerivedUpperStarComp _ a s).app M).symm)).of_iso
      ((leftDerivedUpperStarHomologyFunctorIso _ a q).app _)
  have hi := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (ι := PUnit.{u + 1}) (fun _ ↦ a)
    (fun _ ↦ ⟨⟨⟩, IsLocalRing.closedPoint Ω', Subsingleton.elim _ _⟩)
    (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((L((s)^*[ModuleCat.{u + 1} Λ])).obj M) ⟶ 0)
    (fun _ ↦ isIso_of_source_target_iso_zero _ hz.isoZero
      (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (@asIso _ _ _ _ _ hi)

end AlgebraicGeometry.Etale
