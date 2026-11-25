/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityMap

/-!

# Twisting the dualizing objects of the nearby duality map

Let `Ψ : C ⥤ C'` be a functor between monoidal closed categories with lax tensor maps `μ`, and
`θ : Ψ ω ⟶ ω'` a dualizing map, with duality map `δ_M : Ψ [M, ω] ⟶ [Ψ M, ω']`
(`CategoryTheory.Verdier.nearbyDualityMap`). Let `T` and `T'` be invertible objects of `C` and
`C'` and `κ_A : Ψ (A ⊗ T) ≅ Ψ A ⊗ T'` an isomorphism, natural in `A` and compatible with `μ`.
The *twisted* dualizing map is `θ_tw = (θ ▷ T') ∘ κ_ω : Ψ (ω ⊗ T) ⟶ ω' ⊗ T'`. This file proves
(formal input of the twist step of blueprint `lemma-nearby-duality-slice--1`):

* `CategoryTheory.Verdier.map_ihomTensorToIhom_comp_nearbyDualityMap_twist`: under the canonical
  isomorphisms `[M, ω] ⊗ T ≅ [M, ω ⊗ T]` and `[Ψ M, ω'] ⊗ T' ≅ [Ψ M, ω' ⊗ T']` and `κ`, the
  twisted duality map is `δ_M ▷ T'`;
* `CategoryTheory.Verdier.isIso_nearbyDualityMap_twist_iff`: hence the twisted duality map is
  an isomorphism at `M` iff `δ_M` is;
* `CategoryTheory.Verdier.isIso_nearbyDualityMap_of_iso_twist_iff`: the same after transporting
  the dualizing objects along isomorphisms `u : ω₁ ≅ ω ⊗ T`, `u' : ω₁' ≅ ω' ⊗ T'` (used for
  `c^* ω_{X₁} ≅ ω_{X₂}(1)[2]`, a shift being a tensor product with an invertible object).

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonoidalClosed

namespace CategoryTheory

/-- Whiskering on the right by an invertible object reflects isomorphisms. -/
theorem isIso_whiskerRight_iff {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] {N : C}
    (hN : IsInvertible N) {X Y : C} (f : X ⟶ Y) : IsIso (f ▷ N) ↔ IsIso f := by
  obtain ⟨N', ⟨e⟩, ⟨e'⟩⟩ := hN
  exact isIso_iff_of_reflects_iso f (tensorRightEquivalenceOfTensorIso e e').functor

end CategoryTheory

namespace CategoryTheory.Verdier

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type u₂} [Category.{v₂} C'] [MonoidalCategory C'] [MonoidalClosed C']
  {Ψ : C ⥤ C'} (μ : ∀ A B : C, Ψ.obj A ⊗ Ψ.obj B ⟶ Ψ.obj (A ⊗ B))

omit [MonoidalClosed C] [MonoidalClosed C'] in
/-- A lax tensor map natural in both variables is natural in the second variable. -/
lemma whiskerLeft_map_comp_of_natural
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    (A : C) {B B' : C} (y : B ⟶ B') :
    Ψ.obj A ◁ Ψ.map y ≫ μ A B' = μ A B ≫ Ψ.map (A ◁ y) := by
  simpa using hμ (𝟙 A) y

/-- **Change of the source dualizing object**: for `f : ω₀ ⟶ ω`, the duality map of
`θ ∘ Ψ f` is that of `θ` precomposed with `Ψ [M, f]`. -/
lemma map_ihom_map_comp_nearbyDualityMap
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    {ω₀ ω : C} {ω' : C'} (f : ω₀ ⟶ ω) (θ : Ψ.obj ω ⟶ ω') (M : C) :
    Ψ.map ((ihom M).map f) ≫ nearbyDualityMap μ θ M = nearbyDualityMap μ (Ψ.map f ≫ θ) M := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_nearbyDualityMap, uncurry_nearbyDualityMap,
    reassoc_of% (whiskerLeft_map_comp_of_natural μ hμ M ((ihom M).map f)), ← Ψ.map_comp_assoc,
    ihom.ev_naturality, Ψ.map_comp_assoc]

variable {T : C} {T' : C'} (κ : ∀ A : C, Ψ.obj (A ⊗ T) ≅ Ψ.obj A ⊗ T')

/-- **Twisting the dualizing objects.** Let `κ_A : Ψ (A ⊗ T) ≅ Ψ A ⊗ T'` be natural in `A` and
compatible with the lax tensor maps,
`κ_{A ⊗ B} ∘ Ψ(α⁻¹) ∘ μ_{A, B ⊗ T} = (μ_{A,B} ▷ T') ∘ α⁻¹ ∘ (Ψ A ◁ κ_B)`. Then the duality map
of the twisted dualizing map `(θ ▷ T') ∘ κ_ω : Ψ (ω ⊗ T) ⟶ ω' ⊗ T'` is, under the canonical maps
`[M, ω] ⊗ T ⟶ [M, ω ⊗ T]` and `[Ψ M, ω'] ⊗ T' ⟶ [Ψ M, ω' ⊗ T']` and `κ`, the duality map of `θ`
whiskered by `T'`. -/
theorem map_ihomTensorToIhom_comp_nearbyDualityMap_twist
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    (hκ : ∀ {A B : C} (f : A ⟶ B), Ψ.map (f ▷ T) ≫ (κ B).hom = (κ A).hom ≫ Ψ.map f ▷ T')
    (hκμ : ∀ A B : C, μ A (B ⊗ T) ≫ Ψ.map (α_ A B T).inv ≫ (κ (A ⊗ B)).hom =
      Ψ.obj A ◁ (κ B).hom ≫ (α_ _ _ _).inv ≫ μ A B ▷ T')
    {ω : C} {ω' : C'} (θ : Ψ.obj ω ⟶ ω') (M : C) :
    Ψ.map (ihomTensorToIhom M ω T) ≫ nearbyDualityMap μ ((κ ω).hom ≫ θ ▷ T') M =
      (κ _).hom ≫ nearbyDualityMap μ θ M ▷ T' ≫ ihomTensorToIhom (Ψ.obj M) ω' T' := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_nearbyDualityMap,
    reassoc_of% (whiskerLeft_map_comp_of_natural μ hμ M (ihomTensorToIhom M ω T)),
    ← Ψ.map_comp_assoc, whiskerLeft_ihomTensorToIhom_ev, Ψ.map_comp_assoc, reassoc_of%
      (hκ (A := M ⊗ (ihom M).obj ω) ((ihom.ev M).app ω)),
    reassoc_of% (hκμ _ _), uncurry_natural_left, uncurry_whiskerRight_comp_ihomTensorToIhom,
    uncurry_nearbyDualityMap]
  simp only [comp_whiskerRight]

/-- **Twisting preserves invertibility of the duality map.** In the situation of
`map_ihomTensorToIhom_comp_nearbyDualityMap_twist`, with `T` and `T'` invertible, the duality
map of the twisted dualizing map `(θ ▷ T') ∘ κ_ω` is an isomorphism at `M` iff that of `θ` is. -/
theorem isIso_nearbyDualityMap_twist_iff
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    (hκ : ∀ {A B : C} (f : A ⟶ B), Ψ.map (f ▷ T) ≫ (κ B).hom = (κ A).hom ≫ Ψ.map f ▷ T')
    (hκμ : ∀ A B : C, μ A (B ⊗ T) ≫ Ψ.map (α_ A B T).inv ≫ (κ (A ⊗ B)).hom =
      Ψ.obj A ◁ (κ B).hom ≫ (α_ _ _ _).inv ≫ μ A B ▷ T')
    (hT : IsInvertible T) (hT' : IsInvertible T')
    {ω : C} {ω' : C'} (θ : Ψ.obj ω ⟶ ω') (M : C) :
    IsIso (nearbyDualityMap μ ((κ ω).hom ≫ θ ▷ T') M) ↔ IsIso (nearbyDualityMap μ θ M) := by
  have := isIso_ihomTensorToIhom M ω hT
  have := isIso_ihomTensorToIhom (Ψ.obj M) ω' hT'
  have e := map_ihomTensorToIhom_comp_nearbyDualityMap_twist μ κ hμ hκ hκμ θ M
  rw [← isIso_whiskerRight_iff hT' (nearbyDualityMap μ θ M),
    ← isIso_comp_left_iff (Ψ.map (ihomTensorToIhom M ω T)), e,
    isIso_comp_left_iff, isIso_comp_right_iff]

/-- **Twisting preserves invertibility, up to isomorphisms of the dualizing objects.** In the
situation of `isIso_nearbyDualityMap_twist_iff`, let `u : ω₁ ≅ ω ⊗ T` and
`u' : ω₁' ≅ ω' ⊗ T'` and let `θ₁ : Ψ ω₁ ⟶ ω₁'` correspond to the twisted dualizing map,
`u' ∘ θ₁ = (θ ▷ T') ∘ κ_ω ∘ Ψ u`. Then the duality map of `θ₁` is an isomorphism at `M` iff that
of `θ` is. -/
theorem isIso_nearbyDualityMap_of_iso_twist_iff
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    (hκ : ∀ {A B : C} (f : A ⟶ B), Ψ.map (f ▷ T) ≫ (κ B).hom = (κ A).hom ≫ Ψ.map f ▷ T')
    (hκμ : ∀ A B : C, μ A (B ⊗ T) ≫ Ψ.map (α_ A B T).inv ≫ (κ (A ⊗ B)).hom =
      Ψ.obj A ◁ (κ B).hom ≫ (α_ _ _ _).inv ≫ μ A B ▷ T')
    (hT : IsInvertible T) (hT' : IsInvertible T')
    {ω : C} {ω' : C'} (θ : Ψ.obj ω ⟶ ω') {ω₁ : C} {ω₁' : C'} (u : ω₁ ≅ ω ⊗ T)
    (u' : ω₁' ≅ ω' ⊗ T') (θ₁ : Ψ.obj ω₁ ⟶ ω₁')
    (hθ : θ₁ ≫ u'.hom = Ψ.map u.hom ≫ (κ ω).hom ≫ θ ▷ T') (M : C) :
    IsIso (nearbyDualityMap μ θ₁ M) ↔ IsIso (nearbyDualityMap μ θ M) := by
  rw [← isIso_nearbyDualityMap_twist_iff μ κ hμ hκ hκμ hT hT' θ M,
    ← isIso_comp_left_iff (Ψ.map ((ihom M).map u.inv)), ← isIso_comp_right_iff _
      ((ihom (Ψ.obj M)).map u'.hom), Category.assoc, nearbyDualityMap_comp_ihom_map,
    map_ihom_map_comp_nearbyDualityMap μ hμ, hθ, ← Ψ.map_comp_assoc, Iso.inv_hom_id, Ψ.map_id,
    Category.id_comp]


omit [MonoidalClosed C] [MonoidalClosed C'] in
/-- **Invariance of a twisted dualizing map.** If an endomorphism `ρ` of `Ψ` commutes with the
twist, `ρ_{A ⊗ T} ≫ κ_A = κ_A ≫ ρ_A ▷ T'`, and fixes `θ`, then it fixes the dualizing map
`Ψ u ≫ κ_ω ≫ θ ▷ T' ≫ u'⁻¹` transported along `u : ω₁ ≅ ω ⊗ T`, `u' : ω₁' ≅ ω' ⊗ T'`. -/
theorem app_comp_twist_eq (ρ : Ψ ⟶ Ψ)
    (hρκ : ∀ A : C, ρ.app (A ⊗ T) ≫ (κ A).hom = (κ A).hom ≫ ρ.app A ▷ T')
    {ω : C} {ω' : C'} (θ : Ψ.obj ω ⟶ ω') (hρθ : ρ.app ω ≫ θ = θ) {ω₁ : C} {ω₁' : C'}
    (u : ω₁ ≅ ω ⊗ T) (u' : ω₁' ≅ ω' ⊗ T') :
    ρ.app ω₁ ≫ Ψ.map u.hom ≫ (κ ω).hom ≫ θ ▷ T' ≫ u'.inv =
      Ψ.map u.hom ≫ (κ ω).hom ≫ θ ▷ T' ≫ u'.inv := by
  rw [← ρ.naturality_assoc, reassoc_of% (hρκ ω), ← comp_whiskerRight_assoc, hρθ]

/-- `CategoryTheory.Verdier.isIso_nearbyDualityMap_of_iso_twist_iff` for the transported dualizing
map `Ψ u ≫ κ_ω ≫ θ ▷ T' ≫ u'⁻¹`. -/
theorem isIso_nearbyDualityMap_twist_comp_inv_iff
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    (hκ : ∀ {A B : C} (f : A ⟶ B), Ψ.map (f ▷ T) ≫ (κ B).hom = (κ A).hom ≫ Ψ.map f ▷ T')
    (hκμ : ∀ A B : C, μ A (B ⊗ T) ≫ Ψ.map (α_ A B T).inv ≫ (κ (A ⊗ B)).hom =
      Ψ.obj A ◁ (κ B).hom ≫ (α_ _ _ _).inv ≫ μ A B ▷ T')
    (hT : IsInvertible T) (hT' : IsInvertible T')
    {ω : C} {ω' : C'} (θ : Ψ.obj ω ⟶ ω') {ω₁ : C} {ω₁' : C'} (u : ω₁ ≅ ω ⊗ T)
    (u' : ω₁' ≅ ω' ⊗ T') (M : C) :
    IsIso (nearbyDualityMap μ (Ψ.map u.hom ≫ (κ ω).hom ≫ θ ▷ T' ≫ u'.inv) M) ↔
      IsIso (nearbyDualityMap μ θ M) :=
  isIso_nearbyDualityMap_of_iso_twist_iff μ κ hμ hκ hκμ hT hT' θ u u' _
    (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]) M

end CategoryTheory.Verdier

namespace CategoryTheory

/-- From `x ≫ v = a ≫ z₁ ≫ z₂ ≫ z₃` with `v` an isomorphism, `x = a ≫ z₁ ≫ z₂ ≫ z₃ ≫ v⁻¹`. -/
lemma eq_comp_comp_comp_inv_of_comp_hom_eq {C : Type u₁} [Category.{v₁} C] {P X Y Q R S : C}
    {x : P ⟶ X} (v : X ≅ Y) {a : P ⟶ Q} {z₁ : Q ⟶ R} {z₂ : R ⟶ S} {z₃ : S ⟶ Y}
    (h : x ≫ v.hom = a ≫ z₁ ≫ z₂ ≫ z₃) : x = a ≫ z₁ ≫ z₂ ≫ z₃ ≫ v.inv := by
  simp only [← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

end CategoryTheory
