/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit

/-!
# Transition maps of higher direct images and the transition maps over the source

For `f : X ⟶ Y` and a morphism `φ : U ⟶ V` of schemes over `X`, the transition map
`R^q f_* G ⟶ R^q (V → Y)_* (G|_V)` followed by the transition map
`AlgebraicGeometry.Etale.higherDirectImageOverMap` along `φ` is the transition map
`R^q f_* G ⟶ R^q (U → Y)_* (G|_U)`.

## Main statements

- `AlgebraicGeometry.Etale.higherDirectImageTransition_comp_higherDirectImageOverMap`.

The proof unfolds `AlgebraicGeometry.Etale.higherDirectImageTransition`, which is expensive for
the kernel; this module imports only what the proof needs.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The transition maps of higher direct images compose with the transition maps over `X`. -/
lemma Etale.higherDirectImageTransition_comp_higherDirectImageOverMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {U V : Over X} (φ : U ⟶ V) :
    Etale.higherDirectImageTransition Λ V.hom f (V.hom ≫ f) rfl q G ≫
        Etale.higherDirectImageOverMap Λ f G q φ =
      Etale.higherDirectImageTransition Λ U.hom f (U.hom ≫ f) rfl q G := by
  have h1 := Etale.homologyFunctor_map_overLowerStarTransition Λ f G q φ
  have h2 := Etale.lowerStarPlusTransition_comp Λ V.hom φ.left U.hom (Over.w φ) f (V.hom ≫ f)
    (U.hom ≫ f) rfl (by rw [← Category.assoc, Over.w]) rfl
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  simp only [Etale.higherDirectImageTransition, Functor.map_comp, Category.assoc]
  rw [← h1, ← Functor.map_comp_assoc, Etale.overLowerStarTransition, h2]

end AlgebraicGeometry
