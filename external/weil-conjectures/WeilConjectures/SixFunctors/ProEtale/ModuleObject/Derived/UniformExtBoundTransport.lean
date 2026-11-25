/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-!
# Transport of the uniform `Ext` bound along isomorphisms of coefficient rings

The property `ProEtale.HasUniformConstructibleExtBound R` of a ring object `R` of abelian sheaves
on `X_proét` (blueprint `lemma-uniform-ext-bound`) only depends on `R` up to
isomorphism of ring objects (`ProEtale.HasUniformConstructibleExtBound.of_isIso`): restriction of
scalars along an isomorphism `φ : R ⟶ S` is an equivalence `Mod S ≌ Mod R` which preserves
constructibility, and so is its levelwise extension to the derived categories.

This lets us transfer the bound between the coefficient rings `E̲`, `𝒪̲_E` attached to an abstract
finite extension `E` of `ℚ_ℓ` and those attached to a finite subextension of `ℚ̄_ℓ`, for which the
integral and rational theory is developed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj S]

/-- Restriction of scalars along an isomorphism of ring objects preserves constructibility. -/
lemma IsConstructibleModuleObject.comap_of_isIso (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (hM : IsConstructibleModuleObject S M) :
    IsConstructibleModuleObject R ((Mod.comap φ).obj M) :=
  constructible_comap φ hM

/-- The uniform `Ext` bound is invariant under isomorphisms of ring objects. -/
theorem HasUniformConstructibleExtBound.of_isIso (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    (h : HasUniformConstructibleExtBound S) : HasUniformConstructibleExtBound R := by
  intro M hM
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (inv φ)
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso (inv φ)).isEquivalence_functor
  obtain ⟨N, hN⟩ := h (F.obj M) (hM.comap_of_isIso (inv φ))
  refine ⟨N, fun B hB n hn f ↦ F.mapDerivedCategory.map_injective ?_⟩
  have := hN (F.obj B) (hB.comap_of_isIso (inv φ)) n hn
    ((F.mapDerivedCategorySingleFunctor 0).inv.app M ≫ F.mapDerivedCategory.map f ≫
      (F.mapDerivedCategorySingleFunctor n).hom.app B)
  rw [Functor.map_zero, ← cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app M),
    ← cancel_mono ((F.mapDerivedCategorySingleFunctor n).hom.app B)]
  simpa using this

end AlgebraicGeometry.ProEtale
