/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd

/-!
# Pulling back functions along a morphism over the base

For `f₁ : Y₁ ⟶ X`, `f₂ : Y₂ ⟶ X` and `g : Y₂ ⟶ Y₁` with `g ≫ f₁ = f₂`, pulling back sections along
`g` gives a morphism `f₁_* Λ ⟶ f₂_* Λ` of pushforwards of the constant sheaf. For `Y₁ = Y₂` and
`f₁ = f₂` this is `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver`. The construction is
contravariantly functorial in `g` and compatible with pushing forward along a morphism of the
base.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarConstantSheafMapOfOver`: the morphism `f₁_* Λ ⟶ f₂_* Λ`.

## Main results

- `AlgebraicGeometry.Etale.lowerStarConstantSheafMapOfOver_id`,
  `AlgebraicGeometry.Etale.lowerStarConstantSheafMapOfOver_comp`: functoriality.
- `AlgebraicGeometry.Etale.lowerStar_map_lowerStarConstantSheafMapOfOver`: compatibility with
  the pushforward `n_*` along `n : X ⟶ X'`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

noncomputable section

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- For `f₁ : Y₁ ⟶ X`, `f₂ : Y₂ ⟶ X` and `g : Y₂ ⟶ Y₁` over `X`, the morphism `f₁_* Λ ⟶ f₂_* Λ`
pulling back sections along `g`:

```
f₁_* Λ --f₁_* ε--> f₁_* g_* Λ ≅ (g ≫ f₁)_* Λ = f₂_* Λ
```
-/
def lowerStarConstantSheafMapOfOver {X Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
    (g : Y₂ ⟶ Y₁) (h : g ≫ f₁ = f₂) :
    (f₁)_*[ModuleCat Λ].obj (𝟙_ _) ⟶ (f₂)_*[ModuleCat Λ].obj (𝟙_ _) :=
  (f₁)_*[ModuleCat Λ].map (ε (g)_*[ModuleCat Λ]) ≫ (lowerStarComp _ g f₁ f₂ h.symm).hom.app _

lemma lowerStarConstantSheafEndOfOver_eq_mapOfOver {X Y : Scheme.{u}} (f : Y ⟶ X) (g : Y ⟶ Y)
    (h : g ≫ f = f) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f g h = lowerStarConstantSheafMapOfOver f f g h :=
  lowerStarConstantSheafEndOfOver_eq f g h

/-- Pulling back along the identity is the identity. -/
lemma lowerStarConstantSheafMapOfOver_id {X Y : Scheme.{u}} (f : Y ⟶ X) :
    lowerStarConstantSheafMapOfOver (Λ := Λ) f f (𝟙 Y) (Category.id_comp f) = 𝟙 _ := by
  rw [← lowerStarConstantSheafEndOfOver_eq_mapOfOver, lowerStarConstantSheafEndOfOver_id]

/-- Pulling back sections is contravariant: pulling back along `g' ≫ g` is pulling back along
`g` and then along `g'`. -/
lemma lowerStarConstantSheafMapOfOver_comp {X Y₁ Y₂ Y₃ : Scheme.{u}} (f₁ : Y₁ ⟶ X)
    (f₂ : Y₂ ⟶ X) (f₃ : Y₃ ⟶ X) (g : Y₂ ⟶ Y₁) (g' : Y₃ ⟶ Y₂) (h : g ≫ f₁ = f₂)
    (h' : g' ≫ f₂ = f₃) :
    lowerStarConstantSheafMapOfOver (Λ := Λ) f₁ f₃ (g' ≫ g) (by rw [Category.assoc, h, h']) =
      lowerStarConstantSheafMapOfOver f₁ f₂ g h ≫ lowerStarConstantSheafMapOfOver f₂ f₃ g' h' := by
  have key := congr_app (lowerStarComp_assoc' (ModuleCat Λ) g' g f₁ (g' ≫ g) f₂ f₃ rfl h.symm
    (by rw [Category.assoc, h, h'])) (𝟙_ _)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  rw [lowerStarConstantSheafMapOfOver, lowerStarConstantSheafMapOfOver,
    lowerStarConstantSheafMapOfOver, ε_lowerStar_comp g' g (g' ≫ g) rfl]
  simp only [Functor.map_comp, Category.assoc, key]
  rw [← NatTrans.naturality_assoc]
  rfl

/-- Pulling back sections commutes with pushing forward along a morphism `n` of the base, up to
the composition isomorphisms of pushforwards. -/
lemma lowerStar_map_lowerStarConstantSheafMapOfOver {X X' Y₁ Y₂ : Scheme.{u}} (n : X ⟶ X')
    (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) (g : Y₂ ⟶ Y₁) (h : g ≫ f₁ = f₂) :
    (n)_*[ModuleCat Λ].map (lowerStarConstantSheafMapOfOver f₁ f₂ g h) ≫
        (lowerStarComp _ f₂ n (f₂ ≫ n) rfl).hom.app _ =
      (lowerStarComp _ f₁ n (f₁ ≫ n) rfl).hom.app _ ≫
        lowerStarConstantSheafMapOfOver (f₁ ≫ n) (f₂ ≫ n) g (by rw [← Category.assoc, h]) := by
  have key := congr_app (lowerStarComp_assoc' (ModuleCat Λ) g f₁ n f₂ (f₁ ≫ n) (f₂ ≫ n)
    h.symm rfl rfl) (𝟙_ _)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  rw [lowerStarConstantSheafMapOfOver, lowerStarConstantSheafMapOfOver, Functor.map_comp,
    Category.assoc, key, ← NatTrans.naturality_assoc]
  rfl

lemma lowerStarConstantSheafMapOfOver_congr {X Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
    {g g' : Y₂ ⟶ Y₁} (hg : g = g') (h : g ≫ f₁ = f₂) (h' : g' ≫ f₁ = f₂) :
    lowerStarConstantSheafMapOfOver (Λ := Λ) f₁ f₂ g h =
      lowerStarConstantSheafMapOfOver f₁ f₂ g' h' := by
  subst hg
  rfl

lemma lowerStarConstantSheafMapOfOver_of_eq_id {X Y : Scheme.{u}} (f : Y ⟶ X) {g : Y ⟶ Y}
    (hg : g = 𝟙 Y) (h : g ≫ f = f) :
    lowerStarConstantSheafMapOfOver (Λ := Λ) f f g h = 𝟙 _ := by
  subst hg
  exact lowerStarConstantSheafMapOfOver_id f

end AlgebraicGeometry.Etale
