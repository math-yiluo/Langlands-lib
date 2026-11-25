/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!
# Restricted supported classes and the counit

Forgetting the supports of a restricted supported class
(`AlgebraicGeometry.Etale.restrictSupportedClass`) is the restriction of the class with its supports
forgotten (`AlgebraicGeometry.Etale.restrictSupportedClass_comp_counit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- Forgetting the supports of a restricted class: the restriction of supports followed by the
counit is the restriction of the class with forgotten supports. -/
lemma restrictSupportedClass_comp_counit {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {U X Z Z' : Scheme.{u}}
    (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i] [IsClosedImmersion i']
    (g : Z' ⟶ Z) (hg : IsPullback g i' i e) {K L : DerivedCategoryModule Λ X}
    {K' L' : DerivedCategoryModule Λ U} (σ : K' ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K)
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (γ : K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    restrictSupportedClass Λ e i i' g hg σ τ γ ≫
        (rightDerivedUpperShriekAdjunction _ i').counit.app L' =
      σ ≫ (L((e)^*[ModuleCat.{u + 1} Λ])).map
        (γ ≫ (rightDerivedUpperShriekAdjunction _ i).counit.app L) ≫ τ.hom := by
  have h := (existsUnique_supportedRestriction Λ e i i' g hg L L'
    τ).exists.choose_spec
  rw [restrictSupportedClass, Category.assoc, Category.assoc]
  erw [h]
  rw [Functor.map_comp_assoc]

end Etale

end AlgebraicGeometry
